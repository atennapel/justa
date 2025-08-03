import Common.*

import scala.annotation.tailrec

object Core:
  enum Tm0:
    case Var(ix: Ix)
    case Global(mod: Name, name: Name)
    case Let(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam(name: Bind, ty: Ty, body: Tm0)
    case App(fn: Tm0, arg: Tm0)
    case Splice(tm: Tm1)
    case Wk1(tm: Tm0)
    case Wk0(tm: Tm0)

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm0): Tm0 = if n == 0 then t else go(n - 1, Wk0(t))
      go(n, this)

    def quote: Tm1 = this match
      case Tm0.Splice(t) => t
      case t             => Tm1.Quote(t)

    override def toString: String = this match
      case Var(ix)             => s"'$ix"
      case Global(m, x)        => s"$m.$x"
      case Let(x, ty, v, b)    => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b) => s"(let rec $x : $ty := $v; $b)"
      case Lam(x, ty, b)       => s"(\\($x : $ty) => $b)"
      case App(fn, arg)        => s"($fn $arg)"
      case Splice(tm)          => s"$$$tm"
      case Wk1(tm)             => s"Wk10($tm)"
      case Wk0(tm)             => s"Wk00($tm)"

  type Ty = Tm1
  enum Tm1:
    case Var(ix: Ix)
    case Global(mod: Name, name: Name)
    case Let(name: Name, ty: Ty, value: Tm1, body: Tm1)

    case UMeta
    case UTy(cv: Tm1)

    case CV
    case Val
    case Comp

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: Icit, ty: Ty, body: Tm1)
    case App(fn: Tm1, arg: Tm1, icit: Icit)

    case Fun(pty: Ty, cv: Ty, rty: Ty)

    case Lift(cv: Ty, ty: Ty)
    case Quote(tm: Tm0)

    case Wk0(tm: Tm1)
    case Wk1(tm: Tm1)

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk0(t))
      go(n, this)

    def wk1N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk1(t))
      go(n, this)

    def splice: Tm0 = this match
      case Tm1.Quote(t) => t
      case t            => Tm0.Splice(t)

    override def toString: String = this match
      case Var(ix)                 => s"'$ix"
      case Global(m, x)            => s"$m.$x"
      case Let(x, ty, v, b)        => s"(let $x : $ty = $v; $b)"
      case UTy(cv)                 => s"(type $cv)"
      case UMeta                   => "meta"
      case CV                      => "cv"
      case Val                     => "val"
      case Comp                    => "comp"
      case Pi(x, i, ty, b)         => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, i, ty, b)        => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App(fn, arg, Icit.Expl) => s"($fn $arg)"
      case App(fn, arg, i)         => s"($fn ${i.wrap(arg)})"
      case Fun(pty, _, rty)        => s"($pty -> $rty)"
      case Lift(_, ty)             => s"^$ty"
      case Quote(tm)               => s"`$tm"
      case Wk0(tm)                 => s"Wk01($tm)"
      case Wk1(tm)                 => s"Wk11($tm)"

  enum Locals:
    case Empty
    case Def(locs: Locals, ty: Ty, value: Tm1)
    case Bind0(locs: Locals, ty: Ty, cv: Ty)
    case Bind1(locs: Locals, ty: Ty)
