package core

import common.Common.*

import scala.annotation.tailrec

object Syntax:
  enum Tm0:
    case Var0(ix: Ix)
    case Global0(name: Name)
    case Let0(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam0(name: Bind, ty: Ty, body: Tm0)
    case App0(fn: Tm0, arg: Tm0)
    case Splice(tm: Tm1)
    case Wk10(tm: Tm0)
    case Wk00(tm: Tm0)

    override def toString: String = this match
      case Var0(ix)            => s"'$ix"
      case Global0(x)          => s"$x"
      case Let0(x, ty, v, b)   => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b) => s"(let rec $x : $ty := $v; $b)"
      case Lam0(x, ty, b)      => s"(\\($x : $ty) => $b)"
      case App0(fn, arg)       => s"($fn $arg)"
      case Splice(tm)          => s"$$$tm"
      case Wk10(tm)            => s"Wk10($tm)"
      case Wk00(tm)            => s"Wk00($tm)"

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm0): Tm0 = if n == 0 then t else go(n - 1, Wk00(t))
      go(n, this)
  export Tm0.*

  type Ty = Tm1
  type CV = Ty

  enum Tm1:
    case Var1(ix: Ix)
    case Global1(name: Name)
    case Native(name: Name)
    case Let1(name: Name, ty: Ty, value: Tm1, body: Tm1)

    case U0(cv: Tm1)
    case U1

    case CV
    case CVV
    case CVC

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam1(name: Bind, icit: Icit, ty: Ty, body: Tm1)
    case App1(fn: Tm1, arg: Tm1, icit: Icit)

    case Fun(pty: Ty, cv: CV, rty: Ty)

    case Lift(cv: CV, ty: Ty)
    case Quote(tm: Tm0)

    case Wk01(tm: Tm1)
    case Wk11(tm: Tm1)

    case Meta(id: MetaId)
    case MetaPi1(ty: Ty, body: Ty)
    case MetaPi0(ty: Ty, body: Ty)
    case MetaLam1(body: Tm1)
    case MetaLam0(body: Tm1)
    case MetaApp1(fn: Tm1, arg: Tm1)
    case MetaApp0(fn: Tm1, arg: Tm0)
    case AppPruning(id: MetaId, pruning: Pruning)

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk01(t))
      go(n, this)

    def wk1N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk11(t))
      go(n, this)

    override def toString: String = this match
      case Var1(ix)            => s"'$ix"
      case Global1(x)          => s"$x"
      case Native(x)           => s"$x"
      case Let1(x, ty, v, b)   => s"(let $x : $ty = $v; $b)"
      case U0(cv)              => s"(type $cv)"
      case U1                  => "meta"
      case CV                  => "CV"
      case CVV                 => "Val"
      case CVC                 => "Comp"
      case Pi(x, i, ty, b)     => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam1(x, i, ty, b)   => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App1(fn, arg, Expl) => s"($fn $arg)"
      case App1(fn, arg, i)    => s"($fn ${i.wrap(arg)})"
      case Fun(pty, _, rty)    => s"($pty -> $rty)"
      case Lift(_, ty)         => s"^$ty"
      case Quote(tm)           => s"`$tm"
      case AppPruning(id, p)   => s"(?$id ...(${p.size}))"
      case Wk01(tm)            => s"Wk01($tm)"
      case Wk11(tm)            => s"Wk11($tm)"
      case Meta(id)            => s"?$id"
      case MetaPi1(t, b)       => s"($t 1-> $b)"
      case MetaLam1(b)         => s"(\\1 => $b)"
      case MetaPi0(t, b)       => s"($t 0-> $b)"
      case MetaLam0(b)         => s"(\\0 => $b)"
      case MetaApp0(f, a)      => s"($f 0 $a)"
      case MetaApp1(f, a)      => s"($f 1 $a)"
  export Tm1.*

  inline def quote(t: Tm0): Tm1 = t match
    case Splice(t) => t
    case t         => Quote(t)

  inline def splice(t: Tm1): Tm0 = t match
    case Quote(t) => t
    case t        => Splice(t)

  enum Locals:
    case LEmpty
    case LDef(locs: Locals, ty: Ty, value: Tm1)
    case LBind0(locs: Locals, ty: Ty, cv: CV)
    case LBind1(locs: Locals, ty: Ty)
  export Locals.*
