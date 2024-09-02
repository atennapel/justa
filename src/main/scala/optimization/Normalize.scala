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
 */
object Normalize:
  def normalize(state: State): List[Def] =
    implicit val e: Evaluation = new Evaluation(state)
    state.allGlobals.flatMap {
      case GlobalEntry.GlobalEntry0(x, tm, ty, cv, value, vty, vcv) =>
        def nty = goTDef(ty)
        def ntm = normalize(tm, nty)
        List(DDef(x, nty, ntm))
      case _ => Nil
    }

  private type R = Ref[(Lvl, List[LetEntry])]

  private def addLet(let: LetEntry)(implicit r: R): Lvl =
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

  private def mkStack(ty: TDef)(implicit r: R): Stack =
    def go(arity: Int): Stack =
      arity match
        case 0 => Id
        case n =>
          val a = weaken()
          Arg(go(n - 1), a)
    go(ty.ps.size)

  private def normalize(tm: S.Tm0, ty: TDef)(implicit e: Evaluation): Tm =
    val stm = e.stage(tm)
    implicit val normState: R = new Ref((mkLvl(0), Nil))
    val ret = go(stm, Nil, V.EEmpty, mkStack(ty))
    val lets = normState.value._2.reverse
    Tm(lets, ret)

  private def go(tm: S.Tm0, env: List[Lvl], venv: V.Env, stack: Stack)(implicit
      r: R,
      e: Evaluation
  ): Lvl =
    debug(s"go $tm $env $stack")
    inline def underVEnv(l: Lvl): V.Env = V.E0(venv, V.VVar0(l))
    inline def go0(tm: S.Tm0, st: Stack = stack): Lvl = go(tm, env, venv, st)
    inline def go1(tm: S.Tm1): Lvl = go0(e.stageUnder(S.splice(tm), venv))
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
              val ret = go0(v, mkStack(nty))
              val lets = summon[R].value._2.reverse
              LetLam(nty, Tm(lets, ret))
            }
            goUnder(b, addLet(lam))
      case S.LetRec(x, ty, v, b) =>
        val nty = goTDef(ty)
        val dom = r.value._1
        val lam = locally {
          weaken()
          val ret = goUnder(v, dom, mkStack(nty))
          val lets = summon[R].value._2.reverse
          // TODO: what if let rec is not a function type?
          LetLam(nty, Tm(lets, ret))
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
      case S.Wk00(tm) => weaken(); go0(tm)

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
            addLet(LetNative(x, List(t, f, c).map(t => go1(t))))
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
      case _                                            => impossible()
