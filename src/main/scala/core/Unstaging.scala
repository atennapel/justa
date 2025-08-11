package core

import common.Common.*
import common.State
import common.State.GlobalEntry
import Core.*
import ir.IR
import Evaluation.*
import ir.IR.Type

import scala.annotation.tailrec
import scala.collection.mutable

// convert from Core to IR
object Unstaging:
  def unstage(mods: List[Module]): List[IR.Module] = mods.flatMap(unstage)

  private def unstage(mod: Module): Option[IR.Module] =
    newDefs.clear()
    val defs = mod.defs.toList.flatMap(unstage)
    val extraDefs = newDefs.toList
    if defs.isEmpty then None
    else Some(IR.Module(mod.name, extraDefs ++ defs))

  private def unstage(defn: Def): Option[IR.Def] = defn match
    case Def.D0(pub, x, ty, v) =>
      val ety = goTypeDef(ty)(using Env.Empty)
      val value = unstage(v)
      Some(IR.Def.Value(pub, x, ety, value))
    case Def.Data(k, pub, x, ps, cs) => None
    case Def.D1(_, _, _, _)          => None
    case Def.Primitive(_, _, _)      => None

  private def unstage(c: Constructor, env: Env = Env.Empty): IR.Constructor =
    IR.Constructor(
      c.name,
      c.parameters.map((x, t) => (x.toOption, goTy(t)(using env)))
    )

  private inline def unstage(tm: Tm0): IR.Expr =
    go(unstage0(tm))(using Nil, Env.Empty)

  private def getDataKind(m: Name, dx: Name): DataKind =
    State.getGlobal(m, dx) match
      case Some(GlobalEntry.Data(k, _, _, _, _, _, _)) => k
      case _                                           => impossible()

  private def go(tm: Tm0)(using env: List[IR.TypeDef], venv: Env): IR.Expr =
    inline def extEnv(td: IR.TypeDef) = td :: env
    inline def extVEnv = Env.E0(venv, Val0.Var(mkLvl(venv.size)))
    tm match
      case Tm0.IntLit(v)               => IR.Expr.IntLit(v)
      case Tm0.Global(m, x)            => IR.Expr.Global(IR.MName(m, x))
      case Tm0.Select(m, dx, cx, s, i) =>
        IR.Expr.Field(getDataKind(m, dx), IR.MName(m, dx), cx, go(s), i)
      case Tm0.Let(_, ty, v, b) =>
        val td = goTypeDef(ty)
        IR.Expr.Let(td, go(v), go(b)(using extEnv(td), extVEnv))
      case Tm0.LetRec(_, ty, v, b) =>
        val td = goTypeDef(ty)
        IR.Expr.LetRec(
          td,
          go(v)(using extEnv(td), extVEnv),
          go(b)(using extEnv(td), extVEnv)
        )
      case Tm0.Lam(_, ty, b) =>
        val ta = goTy(ty)
        val td = IR.TypeDef(ta)
        IR.Expr.Lam(ta, go(b)(using extEnv(td), extVEnv))
      case app @ Tm0.App(_, _) =>
        val (hd, args) = app.flattenApps
        args.foldLeft(go(hd))((f, a) => IR.Expr.App(f, go(a)))
      case Tm0.Instr(op, ts, rt, args) =>
        IR.Expr.Instr(op, ts.map(t => goTy(t)), goTy(rt), args.map(go))
      case Tm0.Wk1(tm) => go(tm)
      case Tm0.Wk0(tm) => go(tm)(using env.tail, venv.tail)

      case Tm0.Var(ix) => IR.Expr.Local(ix.expose, env(ix.expose))

      case Tm0.Match(rt, m, dx, s, cs, o) =>
        val k = getDataKind(m, dx)
        val td = IR.TypeDef(IR.Type.Data(k, IR.MName(m, dx)))
        IR.Expr.Case(
          k,
          goTypeDef(rt),
          IR.MName(m, dx),
          go(s),
          cs.map((cx, b) => (cx, go(b)(using extEnv(td), extVEnv))),
          o.map(go)
        )

      case Tm0.Splice(tm) =>
        @tailrec
        def apps(tm: Tm1, args: List[Tm1] = Nil): (Name, Name, List[Tm1]) =
          tm match
            case Tm1.App(f, a, _)    => apps(f, a :: args)
            case Tm1.Primitive(m, x) => (m, x, args)
            case _                   => impossible()
        def stWithEnv(t: Tm1, e: Env) = unstage0Under(t.splice, e)
        inline def st(t: Tm1) = stWithEnv(t, venv)
        inline def stgo(t: Tm1) = go(st(t))
        apps(tm) match
          case (Name("Primitives"), Name("returnIO"), List(_, v)) =>
            IR.Expr.ReturnIO(stgo(v))
          case (Name("Primitives"), Name("bindIO"), List(ty, _, v, k)) =>
            val ety = goTy(ty)
            val ev = stgo(v)
            val ek = stgo(k)
            IR.Expr.BindIO(
              ety,
              ev,
              IR.Expr.App(ek, IR.Expr.Local(0, IR.TypeDef(ety)))
            )
          case (m, x, _) => err(s"invalid primitive in unstaging: $m.$x")

  // types
  private inline def goTypeDef(t: Ty)(using env: Env): IR.TypeDef =
    goVTypeDef(eval1(t)(using env))

  private def goVTypeDef(t: VTy): IR.TypeDef =
    forceAll1(t) match
      case Val1.Fun(pty, _, rty) =>
        IR.TypeDef(goVTy(pty), goVTypeDef(rty))
      case VPrimitive(Name("Primitives"), Name("IO"), List(ty)) =>
        IR.TypeDef(Nil, true, goVTy(ty))
      case t => IR.TypeDef(goVTy(t))

  private inline def goTy(t: Ty)(using env: Env): IR.Type =
    goVTy(eval1(t)(using env))

  private def goVTy(t: VTy): IR.Type =
    forceAll1(t) match
      case VPrimitive(Name("Primitives"), Name("Byte"), _)   => IR.Type.Byte
      case VPrimitive(Name("Primitives"), Name("Char"), _)   => IR.Type.Char
      case VPrimitive(Name("Primitives"), Name("Short"), _)  => IR.Type.Short
      case VPrimitive(Name("Primitives"), Name("Int"), _)    => IR.Type.Int
      case VPrimitive(Name("Primitives"), Name("Long"), _)   => IR.Type.Long
      case VPrimitive(Name("Primitives"), Name("Float"), _)  => IR.Type.Float
      case VPrimitive(Name("Primitives"), Name("Double"), _) => IR.Type.Double

      case VPrimitive(Name("Primitives"), Name("Array"), List(ty)) =>
        IR.Type.Array(goVTy(ty))

      case VTypeCon(k, m, x, ps) => monomorphize(k, m, x, ps)

      case _ => impossible()

  // monomorphization
  private type MonoKey = (IR.MName, List[IR.Type])
  private val monoStore = mutable.Map.empty[MonoKey, Name]
  private val newDefs = mutable.ArrayBuffer.empty[IR.Def]

  private def monomorphize(
      k: DataKind,
      m: Name,
      x: Name,
      ps: List[VTy]
  ): IR.Type =
    val mx = IR.MName(m, x)
    val eps = ps.map(goVTy)
    val (nx, alreadyDone) = monomorphize(mx, eps)
    if !alreadyDone then
      val cons = State.getGlobal(m, x) match
        case Some(GlobalEntry.Data(_, _, _, xs, _, _, _)) =>
          xs.map { cx =>
            State.getGlobal(m, cx) match
              case Some(GlobalEntry.DataCon(_, _, _, ps, _, _, _, _, _)) =>
                cx -> ps.map((x, t, _) => (x, t))
              case _ => impossible()
          }
        case _ => impossible()
      val env = Env(ps)
      val ecs = cons.map { (cx, ts) =>
        val ets = ts.map((x, t) => (x.toOption, goTy(t)(using env)))
        IR.Constructor(cx, ets)
      }
      newDefs += IR.Def.Data(k, false, x, ecs)
    IR.Type.Data(k, IR.MName(State.currentModule, nx))

  private def monomorphize(name: IR.MName, ps: List[IR.Type]): (Name, Boolean) =
    val k = (name, ps)
    monoStore.get(k) match
      case Some(x) => (x, true)
      case None    =>
        val x = createName(name, ps)
        monoStore += k -> x
        (x, false)

  private def createName(name: IR.MName, ps: List[IR.Type]): Name =
    def paramStr(p: IR.Type): String = p match
      case Type.Byte               => "Byte"
      case Type.Char               => "Char"
      case Type.Short              => "Short"
      case Type.Int                => "Int"
      case Type.Long               => "Long"
      case Type.Float              => "Float"
      case Type.Double             => "Double"
      case Type.Array(ty)          => s"Array_${paramStr(ty)}"
      case Type.Jvm(qualifiedName) => qualifiedName.replace('.', '$')
      case Type.Data(_, x)         =>
        s"${name.module.expose.replace('.', '$')}$$${name.name}"
    if ps.isEmpty then name.name
    else Name(s"${name.name}_${ps.map(paramStr).mkString("_")}")
