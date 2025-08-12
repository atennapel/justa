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
    currentModule = Some(mod.name)
    monoStore.clear()
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
      case Tm0.IntLit(v)            => IR.Expr.IntLit(v)
      case Tm0.Global(m, x)         => IR.Expr.Global(IR.MName(m, x))
      case Tm0.Select(dt, cx, s, i) =>
        val (k, em, edx) = forceAll1(eval1(dt)) match
          case VTypeCon(k, m, dx, ps) =>
            val ty = monomorphize(m, dx, ps.map(_._1))
            val (em, edx) = ty match
              case IR.Type.Data(_, mx) => (mx.module, mx.name)
              case _                   => impossible()
            (k, em, edx)
          case _ => impossible()
        IR.Expr.Field(k, IR.MName(em, edx), cx, go(s), i)
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

      case Tm0.Match(rt, dt, s, cs, o) =>
        val (k, edt, m, dx, em, edx) = forceAll1(eval1(dt)) match
          case VTypeCon(k, m, dx, ps) =>
            val ty = monomorphize(m, dx, ps.map(_._1))
            val (em, edx) = ty match
              case IR.Type.Data(_, mx) => (mx.module, mx.name)
              case _                   => impossible()
            (k, ty, m, dx, em, edx)
          case _ => impossible()
        val td = IR.TypeDef(edt)
        IR.Expr.Case(
          k,
          goTypeDef(rt),
          IR.MName(em, edx),
          go(s),
          cs.map((cx, b) =>
            (cx, conIndex(m, dx, cx), go(b)(using extEnv(td), extVEnv))
          ),
          o.map(go)
        )

      case Tm0.Splice(tm) =>
        @tailrec
        def apps(
            tm: Tm1,
            args: List[(Tm1, Icit)] = Nil
        ): (Tm1, List[(Tm1, Icit)]) =
          tm match
            case Tm1.App(f, a, i)    => apps(f, (a, i) :: args)
            case Tm1.Primitive(m, x) => (tm, args)
            case Tm1.Con(_, _, _)    => (tm, args)
            case _                   => impossible()
        def stWithEnv(t: Tm1, e: Env) = unstage0Under(t.splice, e)
        inline def st(t: Tm1) = stWithEnv(t, venv)
        inline def stgo(t: Tm1) = go(st(t))
        def takeImpl(args: List[(Tm1, Icit)]): List[Tm1] =
          args match
            case (a, Icit.Impl) :: tl => a :: takeImpl(tl)
            case _                    => Nil
        apps(tm) match
          case (Tm1.Con(m, dx, cx), args) =>
            val ps = takeImpl(args).map(eval1)
            val as = args.drop(ps.size).map((t, _) => stgo(t))
            monomorphize(m, dx, ps) match
              case IR.Type.Data(k, mx) =>
                IR.Expr.Con(k, mx, cx, conIndex(m, dx, cx), as)
              case _ => impossible()

          case (
                Tm1.Primitive(Name("Primitives"), Name("returnIO")),
                List(_, (v, _))
              ) =>
            IR.Expr.ReturnIO(stgo(v))
          case (
                Tm1.Primitive(Name("Primitives"), Name("bindIO")),
                List((ty, _), _, (v, _), (k, _))
              ) =>
            val ety = goTy(ty)
            val ev = stgo(v)
            val ek = stgo(k)
            IR.Expr.BindIO(
              ety,
              ev,
              IR.Expr.App(ek, IR.Expr.Local(0, IR.TypeDef(ety)))
            )

          case (hd, _) => err(s"invalid spliced function in unstaging: $hd")

  // types
  private inline def goTypeDef(t: Ty)(using env: Env): IR.TypeDef =
    goVTypeDef(eval1(t)(using env))

  private def goVTypeDef(t: VTy): IR.TypeDef =
    forceAll1(t) match
      case Val1.Fun(pty, _, rty) =>
        IR.TypeDef(goVTy(pty), goVTypeDef(rty))
      case VPrimitive(Name("Primitives"), Name("IO"), List((ty, _))) =>
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

      case VPrimitive(Name("Primitives"), Name("Array"), List((ty, _))) =>
        IR.Type.Array(goVTy(ty))

      case VTypeCon(_, m, x, ps) => monomorphize(m, x, ps.map(_._1))

      case _ => impossible()

  // monomorphization
  private type MonoKey = (IR.MName, List[IR.Type])
  private var currentModule: Option[Name] = None
  private val monoStore = mutable.Map.empty[MonoKey, Name]
  private val newDefs = mutable.ArrayBuffer.empty[IR.Def]

  private def conIndex(m: Name, dx: Name, cx: Name): Int =
    State.getGlobal(m, dx) match
      case Some(GlobalEntry.Data(_, _, _, xs, _, _, _)) => xs.indexOf(cx)
      case _                                            => impossible()

  private def monomorphize(
      m: Name,
      x: Name,
      ps: List[VTy]
  ): IR.Type =
    val (k, xs) = State.getGlobal(m, x) match
      case Some(GlobalEntry.Data(k, _, _, xs, _, _, _)) => (k, xs)
      case _                                            => impossible()
    val mx = IR.MName(m, x)
    val eps = ps.map(goVTy)
    val (nx, alreadyDone) = monomorphize(mx, eps)
    if !alreadyDone then
      val cons = xs.map { cx =>
        State.getGlobal(m, cx) match
          case Some(GlobalEntry.DataCon(_, _, _, ps, _, _, _, _, _)) =>
            cx -> ps.map((x, t, _) => (x, t))
          case _ => impossible()
      }
      val env = Env(ps)
      val ecs = cons.map { (cx, ts) =>
        val ets = ts.map((x, t) => (x.toOption, goTy(t)(using env)))
        IR.Constructor(cx, ets)
      }
      newDefs += IR.Def.Data(k, false, nx, ecs)
    IR.Type.Data(k, IR.MName(currentModule.get, nx))

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
