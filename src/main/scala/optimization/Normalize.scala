package optimization

import common.Common.*
import common.Ref
import common.Debug.debug
import Syntax.*
import core.Value as V
import core.Syntax as S
import core.Syntax.Tm0
import core.State
import core.Evaluation
import core.State.GlobalEntry

import scala.annotation.tailrec

/* normalize the elaborated output
- eta-expand
- saturated applications
- convert to ANF form

algorithm adapted from https://github.com/AndrasKovacs/staged/blob/main/opt/SimpleANF.hs
 */
object Normalize:
  def normalize(state: State): List[Def[NTm]] =
    implicit val e: Evaluation = new Evaluation(state)
    state.allGlobals.flatMap {
      case GlobalEntry.GlobalEntry0(x, tm, ty, cv, value, vty, vcv) =>
        def nty = goTDef(ty)
        def ntm = normalize(tm, nty)
        List(DDef(x, nty, ntm))
      case _ => Nil
    }

  private type R = Ref[(Lvl, List[LetEntry[NTm]])]

  private def addLet(let: LetEntry[NTm])(implicit r: R): Lvl =
    r.updateGetOld((dom, lets) => (dom + 1, let :: lets))._1
  private def weaken()(implicit r: R): Lvl =
    r.updateGetOld((dom, lets) => (dom + 1, lets))._1
  private def locally[A](a: R ?=> A)(implicit r: R): A =
    val (dom, lets) = r.value
    r.set((dom, Nil))
    val v = a
    r.set((dom, lets))
    v

  private enum Stack:
    case Id
    case Arg(stack: Stack, arg: Lvl)

    def toList: List[Lvl] = this match
      case Id              => Nil
      case Arg(stack, arg) => arg :: stack.toList
  import Stack.*

  private def mkStack(arity: Int, stack: Stack = Id)(implicit r: R): Stack =
    arity match
      case 0 => stack
      case n =>
        val a = weaken()
        Arg(mkStack(n - 1, stack), a)

  private def normalize(tm: S.Tm0, ty: TDef)(implicit e: Evaluation): NTm =
    val stm = e.stage(tm)
    implicit val normState: R = new Ref((lvl0, Nil))
    val ret = go(stm, Nil, V.EEmpty, mkStack(ty.arity))
    val lets = normState.value._2.reverse
    NTm(Tm(lets, ret))

  private def go(tm: S.Tm0, env: List[Lvl], venv: V.Env, stack: Stack)(implicit
      r: R,
      e: Evaluation
  ): Lvl =
    debug(s"go $tm $env $venv $stack")
    inline def underVEnv(l: Lvl): V.Env = V.E0(venv, V.VVar0(l))
    inline def go0(tm: S.Tm0, st: Stack = stack): Lvl = go(tm, env, venv, st)
    inline def go1(tm: S.Tm1, st: Stack = stack): Lvl =
      go0(e.stageUnder(S.splice(tm), venv), st)
    inline def go1s(tms: S.Tm1*): List[Lvl] = tms.map(x => go1(x)).toList
    def goUnder(tm: S.Tm0, l: Lvl, st: Stack = stack): Lvl =
      go(tm, l :: env, underVEnv(l), st)
    tm match
      case S.Var0(ix) =>
        stack match
          case Id    => env(ix.expose)
          case stack => addLet(LetApp(env(ix.expose), stack.toList))
      case S.Global0(x) => addLet(LetGlobal(x, stack.toList))

      /*
      case S.Let0(x, ty, S.Let0(x2, ty2, v2, b2), b) =>
        go0(S.Let0(x2, ty2, v2, S.Let0(x, ty, b2, b)))
      case S.Let0(x, ty, S.LetRec(x2, ty2, v2, b2), b) =>
        go0(S.LetRec(x2, ty2, v2, S.Let0(x, ty, b2, b)))
      // TODO: what about letrec(letrec) and letrec(let)?
       */

      case S.Let0(x, ty, v, b) =>
        goTDef(ty) match
          case TDef(Nil, rt) => goUnder(b, go0(v, Id))
          case nty @ TDef(ps, rt) =>
            val lam = locally {
              val ret = go0(v, mkStack(nty.arity))
              val lets = summon[R].value._2.reverse
              LetLam(nty, NTm(Tm(lets, ret)))
            }
            goUnder(b, addLet(lam))
      case S.LetRec(x, ty, v, b) =>
        val nty = goTDef(ty)
        val dom = r.value._1
        val lam = locally {
          weaken()
          val ret = goUnder(v, dom, mkStack(nty.arity))
          val lets = summon[R].value._2.reverse
          LetRecLam(nty, NTm(Tm(lets, ret)))
        }
        val k = addLet(lam)
        if (dom != k) impossible()
        goUnder(b, k)

      case S.Lam0(x, ty, b) =>
        stack match
          case Id              => impossible()
          case Arg(stack, arg) => goUnder(b, arg, stack)

      case S.App0(fn, arg) => go0(fn, Arg(stack, go0(arg, Id)))

      case S.Wk10(tm) => go0(tm)
      case S.Wk00(tm) => weaken(); go(tm, env.tail, venv.wk0, stack)

      case S.Splice(tm) =>
        @tailrec
        def apps(tm: S.Tm1, args: List[S.Tm1] = Nil): (Name, List[S.Tm1]) =
          tm match
            case S.App1(f, a, _) => apps(f, a :: args)
            case S.Native(x)     => (x, args)
            case x               => debug(x); impossible()
        apps(tm) match
          case (x @ Name("True"), Nil)  => addLet(LetNative(x, Nil))
          case (x @ Name("False"), Nil) => addLet(LetNative(x, Nil))
          case (x @ Name("cond"), List(_, _, t, f, c)) =>
            addLet(LetNative(x, go1s(t, f, c)))

          case (x @ Name("Z"), Nil)     => addLet(LetNative(x, Nil))
          case (x @ Name("S"), List(n)) => addLet(LetNative(x, List(go1(n))))
          case (x @ Name("caseNat"), List(_, rt, n, z, s)) =>
            val ty = TDef(TNative(Name("Nat"), Nil), goTDef(rt))
            val lam = addLet(locally {
              val ret = go1(s, mkStack(1, stack))
              val lets = summon[R].value._2.reverse
              LetLam(ty, NTm(Tm(lets, ret)))
            })
            addLet(LetNative(x, go1s(n, z) ++ List(lam)))

          case (x @ Name("Nil"), List(_)) => addLet(LetNative(x, Nil))
          case (x @ Name("::"), List(_, hd, tl)) =>
            addLet(LetNative(x, go1s(hd, tl)))
          case (x @ Name("caseList"), List(pt, _, rt, l, n, c)) =>
            val npt = goTy(pt)
            val ty =
              TDef(List(npt, TNative(Name("List"), List(npt))), goTDef(rt))
            val lam = addLet(locally {
              val ret = go1(c, mkStack(2, stack))
              val lets = summon[R].value._2.reverse
              LetLam(ty, NTm(Tm(lets, ret)))
            })
            addLet(LetNative(x, go1s(l, n) ++ List(lam)))

          case _ => impossible()

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
