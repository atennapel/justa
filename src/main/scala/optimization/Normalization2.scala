package optimization

import common.Common.*
import Syntax.{Ty, TDef}
import Syntax.Ty.*
import core.Value as V
import core.Syntax as S
import core.Syntax.Tm0
import core.State
import core.Evaluation
import core.State.GlobalEntry

import scala.annotation.tailrec

object Normalization2:
  private enum VComp:
    case VLam(comp: Lvl => VComp)
    case VBody(body: VANF)
  import VComp.*

  private enum VVal:
    case VApp(fn: Lvl, args: List[Lvl])
    case VGlobal(x: Name, args: List[Lvl])
    case VCon(x: Name, args: List[Lvl])
    case VLetComp(ty: TDef, comp: VComp)
    case VLetRecComp(ty: TDef, comp: Lvl => VComp)
  import VVal.*

  private enum VANF:
    case VRet(lvl: Lvl)
    case VLet(value: VVal, body: Lvl => VANF)
    case VIf(cond: Lvl, ifTrue: VANF, ifFalse: VANF)
  import VANF.*

  enum Val:
    case App(fn: Lvl, args: List[Lvl])
    case Global(x: Name, args: List[Lvl])
    case Con(x: Name, args: List[Lvl])
    case Lam(ty: TDef, body: ANF)
    case Rec(ty: TDef, body: ANF)
  export Val.*

  enum ANF:
    case Ret(lvl: Lvl)
    case Let(value: Val, body: ANF)
    case If(cond: Lvl, ifTrue: ANF, ifFalse: ANF)
  export ANF.*

  final case class Def(x: Name, ty: TDef, value: ANF)

  def normalize(state: State): List[Def] =
    implicit val e: Evaluation = new Evaluation(state)
    state.allGlobals.flatMap {
      case GlobalEntry.GlobalEntry0(x, tm, ty, cv, value, vty, vcv) =>
        val nty = goVTDef(vty)
        val ntm = normalize(tm, nty)
        List(Def(x, nty, ntm))
      case _ => Nil
    }

  private def normalize(tm: S.Tm0, ty: TDef)(implicit e: Evaluation): ANF =
    val stm = e.stage(tm)
    quote(lvl0, go(Nil, ty.ps, stm, Nil))

  // evaluation
  private def go(
      env: List[Lvl],
      ps: List[Ty],
      body: S.Tm0,
      args: List[Lvl]
  )(implicit ev: Evaluation): VComp =
    ps match
      case Nil     => VBody(go(env, body, args, VRet.apply))
      case _ :: ps => VLam(v => go(v :: env, ps, body, v :: args))

  private def go(
      env: List[Lvl],
      tm: S.Tm0,
      args: List[Lvl],
      k: Lvl => VANF
  )(implicit ev: Evaluation): VANF =
    tm match
      case S.Var0(ix) =>
        inline def x = env(ix.expose)
        args match
          case Nil  => k(x)
          case args => VLet(VApp(x, args), k)
      case S.Global0(x) => VLet(VGlobal(x, args), k)

      case S.App0(f, a) => go(env, a, Nil, a => go(env, f, a :: args, k))

      case S.Let0(_, ty, v, b) =>
        goTDef(ty) match
          case TDef(Nil, _) => go(env, v, Nil, v => go(v :: env, b, args, k))
          case ty @ TDef(ps, _) =>
            VLet(
              VLetComp(ty, go(env, ps, v, Nil)),
              v => go(v :: env, b, args, k)
            )
      case S.LetRec(_, ty, v, b) =>
        goTDef(ty) match
          case ty @ TDef(ps, _) =>
            VLet(
              VLetRecComp(ty, r => go(r :: env, ps, v, Nil)),
              v => go(v :: env, b, args, k)
            )

      case S.Lam0(_, _, b) =>
        args match
          case Nil       => impossible()
          case v :: args => go(v :: env, b, args, k)

      case S.Wk10(tm) => go(env, tm, args, k)
      case S.Wk00(tm) => go(env.tail, tm, args, k)

      case S.Splice(tm) =>
        @tailrec
        def apps(tm: S.Tm1, args: List[S.Tm1] = Nil): (Name, List[S.Tm1]) =
          tm match
            case S.App1(f, a, _) => apps(f, a :: args)
            case S.Native(x)     => (x, args)
            case x               => impossible()
        apps(tm) match
          case (x @ Name("True"), Nil)  => VLet(VCon(x, Nil), k)
          case (x @ Name("False"), Nil) => VLet(VCon(x, Nil), k)
          case (x @ Name("cond"), List(_, _, t, f, c)) =>
            val venv = env.foldRight(V.EEmpty)((k, e) => V.E0(e, V.VVar0(k)))
            def st(t: S.Tm1) = ev.stageUnder(S.splice(t), venv)
            go(
              env,
              st(c),
              Nil,
              c =>
                VIf(
                  c,
                  go(env, st(t), args, k),
                  go(env, st(f), args, k)
                )
            )

          case _ => impossible()

  // quote
  private def quote(k: Lvl, c: VComp): ANF =
    c match
      case VLam(c)  => quote(k + 1, c(k))
      case VBody(b) => quote(k, b)

  private def quote(k: Lvl, v: VVal): Val =
    v match
      case VApp(fn, args)     => App(fn, args)
      case VGlobal(x, args)   => Global(x, args)
      case VCon(x, args)      => Con(x, args)
      case VLetComp(ty, c)    => Lam(ty, quote(k, c))
      case VLetRecComp(ty, c) => Rec(ty, quote(k + 1, c(k)))

  private def quote(k: Lvl, v: VANF): ANF =
    v match
      case VRet(lvl)    => Ret(lvl)
      case VLet(v, b)   => Let(quote(k, v), quote(k + 1, b(k)))
      case VIf(c, t, f) => If(c, quote(k, t), quote(k, f))

  // types
  private inline def goTDef(t: S.Ty)(implicit e: Evaluation): TDef =
    goVTDef(e.eval1(t)(V.EEmpty))
  private def goVTDef(t: V.VTy)(implicit e: Evaluation): TDef =
    e.forceAll1(t) match
      case V.VFun(pty, _, rty) => TDef(goVTy(pty), goVTDef(rty))
      case t                   => TDef(goVTy(t))

  private inline def goTy(t: S.Ty, env: V.Env = V.EEmpty)(implicit
      e: Evaluation
  ): Ty =
    goVTy(e.eval1(t)(env))
  private def goVTy(t: V.VTy)(implicit e: Evaluation): Ty =
    e.forceAll1(t) match
      case V.VRigid(V.HNative(x @ Name("Bool")), V.SId) => TNative(x)
      case V.VRigid(V.HNative(x @ Name("Nat")), V.SId)  => TNative(x)
      case V.VRigid(V.HNative(x @ Name("List")), V.SApp(V.SId, a, Expl)) =>
        TNative(x, List(goVTy(a)))
      case _ => impossible()
