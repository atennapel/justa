package core

import common.Common.*
import Core.*
import ir.IR
import Evaluation.*

// convert from Core to IR
object Unstaging:
  def unstage(mods: List[Module]): List[IR.Module] = mods.flatMap(unstage)

  private def unstage(mod: Module): Option[IR.Module] =
    val defs = mod.defs.toList.flatMap(unstage)
    if defs.isEmpty then None
    else Some(IR.Module(mod.name, defs))

  private def unstage(defn: Def): Option[IR.Def] = defn match
    case Def.D1(_, _, _, _)    => None
    case Def.D0(pub, x, ty, v) =>
      val ety = goTypeDef(ty)
      val value = unstage(v)
      Some(IR.Def.Value(pub, x, ety, value))

  private inline def unstage(tm: Tm0): IR.Expr =
    go(unstage0(tm))(using Nil, Env.Empty)

  private def go(tm: Tm0)(using env: List[IR.TypeDef], venv: Env): IR.Expr =
    inline def extEnv(td: IR.TypeDef) = td :: env
    inline def extVEnv = Env.E0(venv, Val0.Var(mkLvl(venv.size)))
    tm match
      case Tm0.IntLit(v)        => IR.Expr.IntLit(v)
      case Tm0.Global(m, x)     => IR.Expr.Global(IR.MName(m, x))
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
      case Tm0.App(f, a)               => IR.Expr.App(go(f), go(a))
      case Tm0.Instr(op, ts, rt, args) =>
        IR.Expr.Instr(op, ts.map(t => goTy(t)), goTy(rt), args.map(go))
      case Tm0.Wk1(tm) => go(tm)
      case Tm0.Wk0(tm) =>
        go(tm)(using env.tail, venv.tail) // TODO: is this correct?

      case Tm0.Var(ix) => IR.Expr.Local(ix.expose, env(ix.expose))

      case Tm0.Splice(_) => impossible()

  // types
  private inline def goTypeDef(t: Ty, env: Env = Env.Empty): IR.TypeDef =
    goVTypeDef(eval1(t)(using env))

  private def goVTypeDef(t: VTy): IR.TypeDef =
    forceAll1(t) match
      case Val1.Fun(pty, _, rty) =>
        IR.TypeDef(goVTy(pty), goVTypeDef(rty))
      case t => IR.TypeDef(goVTy(t))

  private inline def goTy(t: Ty, env: Env = Env.Empty): IR.Type =
    goVTy(eval1(t)(using env))

  private def goVTy(t: VTy): IR.Type =
    forceAll1(t) match
      case VPrimitive(Name("Byte"))   => IR.Type.Byte
      case VPrimitive(Name("Char"))   => IR.Type.Char
      case VPrimitive(Name("Short"))  => IR.Type.Short
      case VPrimitive(Name("Int"))    => IR.Type.Int
      case VPrimitive(Name("Long"))   => IR.Type.Long
      case VPrimitive(Name("Float"))  => IR.Type.Float
      case VPrimitive(Name("Double")) => IR.Type.Double
      case _                          => impossible()
