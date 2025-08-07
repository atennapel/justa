package core

import common.Common.*
import Core.*
import ir.IR
import Evaluation.*

import scala.annotation.tailrec

// convert from Core to IR
object Unstaging:
  def unstage(mods: List[Module]): List[IR.Module] = mods.flatMap(unstage)

  private def unstage(mod: Module): Option[IR.Module] =
    val defs = mod.defs.toList.flatMap(unstage)
    if defs.isEmpty then None
    else Some(IR.Module(mod.name, defs))

  private def unstage(defn: Def): Option[IR.Def] = defn match
    case Def.D0(pub, x, ty, v) =>
      val ety = goTypeDef(ty)(using Env.Empty)
      val value = unstage(v)
      Some(IR.Def.Value(pub, x, ety, value))
    case Def.Finite(pub, x, cs) => Some(IR.Def.Finite(pub, x, cs.size))
    case Def.D1(_, _, _, _)     => None
    case Def.Primitive(_, _, _) => None

  private inline def unstage(tm: Tm0): IR.Expr =
    go(unstage0(tm))(using Nil, Env.Empty)

  private def go(tm: Tm0)(using env: List[IR.TypeDef], venv: Env): IR.Expr =
    inline def extEnv(td: IR.TypeDef) = td :: env
    inline def extVEnv = Env.E0(venv, Val0.Var(mkLvl(venv.size)))
    inline def goCon(m: Name, dx: Name, cx: Name, args: List[Tm0]): IR.Expr =
      IR.Expr.Con(IR.MName(m, dx), cx, args.map(go))
    tm match
      case Tm0.IntLit(v)               => IR.Expr.IntLit(v)
      case Tm0.Global(m, x)            => IR.Expr.Global(IR.MName(m, x))
      case Tm0.Con(m, dx, cx)          => goCon(m, dx, cx, Nil)
      case Tm0.Select(m, dx, cx, s, i) =>
        IR.Expr.Field(IR.MName(m, dx), cx, go(s), i)
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
        hd match
          case Tm0.Con(m, dx, cx) => goCon(m, dx, cx, args)
          case _ => args.foldLeft(go(hd))((f, a) => IR.Expr.App(f, go(a)))
      case Tm0.Instr(op, ts, rt, args) =>
        IR.Expr.Instr(op, ts.map(t => goTy(t)), goTy(rt), args.map(go))
      case Tm0.Wk1(tm) => go(tm)
      case Tm0.Wk0(tm) => go(tm)(using env.tail, venv.tail)

      case Tm0.Var(ix) => IR.Expr.Local(ix.expose, env(ix.expose))

      case Tm0.Match(rt, m, dx, s, cs, o) =>
        val td = IR.TypeDef(IR.Type.Finite(IR.MName(m, dx)))
        IR.Expr.Case(
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

      case VTypeCon(DataKind.Data, m, x)   => IR.Type.Data(IR.MName(m, x))
      case VTypeCon(DataKind.Record, m, x) => IR.Type.Record(IR.MName(m, x))
      case VTypeCon(DataKind.Finite, m, x) => IR.Type.Finite(IR.MName(m, x))

      case _ => impossible()
