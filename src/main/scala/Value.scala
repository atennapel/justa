import Common.*
import Core.{Tm0, Tm1}

import scala.annotation.tailrec

object Value:
  enum Clos0:
    case Clos(env: Env, tm: Tm0)
    case Fun(fn: Val0 => Val0)
  object Clos0:
    def apply(tm: Tm0)(implicit env: Env): Clos0 = Clos0.Clos(env, tm)

  enum Clos1:
    case Clos(env: Env, tm: Tm1)
    case Fun(fn: Val1 => Val1)
  object Clos1:
    def apply(tm: Tm1)(implicit env: Env): Clos1 = Clos1.Clos(env, tm)

  enum Env:
    case Empty
    case E1(env: Env, value: Val1)
    case E0(env: Env, value: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, e: Env): Int = e match
        case Empty    => acc
        case E1(e, _) => go(acc + 1, e)
        case E0(e, _) => go(acc + 1, e)
      go(0, this)

    inline def wk1: Env = this match
      case E1(env, _) => env
      case _          => impossible()

    inline def wk0: Env = this match
      case E0(env, _) => env
      case _          => impossible()

    inline def tail: Env = this match
      case E0(env, _) => env
      case E1(env, _) => env
      case _          => impossible()
  object Env:
    def apply(vs: List[Val1]): Env = vs.foldLeft(Env.Empty)(E1.apply)

  enum Spine:
    case Empty
    case App(sp: Spine, arg: Val1, icit: Icit)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case Empty         => acc
        case App(sp, _, _) => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case Empty         => acc
        case App(sp, v, i) => go(App(acc, v, i), sp)
      go(Empty, this)

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  enum Val0:
    case Var(lvl: Lvl)
    case Global(mod: Name, name: Name)
    case Let(
        name: Name,
        ty: VTy,
        value: Val0,
        body: Clos0
    )
    case LetRec(
        name: Name,
        ty: VTy,
        value: Clos0,
        body: Clos0
    )
    case Lam(name: Bind, ty: VTy, body: Clos0)
    case App(fn: Val0, arg: Val0)
    case Splice(tm: Val1)

  enum Head:
    case Var(lvl: Lvl)

  enum UnfoldHead:
    case Global(mod: Name, name: Name)

  type VTy = Val1
  enum Val1:
    case Rigid(head: Head, spine: Spine)
    case Unfold(head: UnfoldHead, spine: Spine, value: () => Val1)

    case Pi(name: Bind, icit: Icit, ty: VTy, body: Clos1)
    case Lam(name: Bind, icit: Icit, ty: VTy, body: Clos1)

    case UTy(cv: VTy)
    case UMeta

    case CV
    case Val
    case Comp

    case Fun(pty: VTy, cv: VTy, rty: VTy)
    case Lift(cv: VTy, ty: VTy)

    case Quote(tm: Val0)

  object Var1:
    def apply(lvl: Lvl): Val1 = Val1.Rigid(Head.Var(lvl), Spine.Empty)
    def unapply(value: Val1): Option[Lvl] = value match
      case Val1.Rigid(Head.Var(hd), Spine.Empty) => Some(hd)
      case _                                     => None
