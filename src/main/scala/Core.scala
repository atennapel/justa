import Common.*

import scala.annotation.tailrec

object Core:
  enum Tm0:
    case Var(ix: Ix)
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
      case Splice(t) => t
      case t         => Tm1.Quote(t)

    def flattenApps: (Tm0, List[Tm0]) = this match
      case App(f, a) =>
        val (hd, args) = f.flattenApps
        (hd, args ++ List(a))
      case t => (t, Nil)

    override def toString: String = this match
      case Var(ix)             => s"'$ix"
      case Let(x, ty, v, b)    => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b) => s"(let rec $x : $ty := $v; $b)"
      case Lam(x, ty, b)       => s"(\\($x : $ty) => $b)"
      case App(fn, arg)        => s"($fn $arg)"
      case Splice(tm)          => s"$$$tm"
      case Wk1(tm)             => s"Wk10($tm)"
      case Wk0(tm)             => s"Wk00($tm)"

  enum Primitive:
    case Meta
    case Type
    case CV
    case Comp
    case Val
    case Kind
    case Prim
    case Ref
    case Nullability
    case NonNullable
    case Nullable
    case Rep
    case RepBoolean
    case RepByte
    case RepShort
    case RepInt
    case RepLong
    case RepFloat
    case RepDouble
    case RepChar
    case Boolean
    case Byte
    case Short
    case Int
    case Long
    case Float
    case Double
    case Char

    override def toString: String = this match
      case Meta        => "meta"
      case Type        => "type"
      case CV          => "cv"
      case Comp        => "comp"
      case Val         => "val"
      case Kind        => "kind"
      case Prim        => "prim"
      case Ref         => "ref"
      case Nullability => "nullability"
      case NonNullable => "nonnullable"
      case Nullable    => "nullable"
      case Rep         => "rep"
      case RepBoolean  => "repboolean"
      case RepByte     => "repbyte"
      case RepShort    => "repshort"
      case RepInt      => "repint"
      case RepLong     => "replong"
      case RepFloat    => "repfloat"
      case RepDouble   => "repdouble"
      case RepChar     => "repchar"
      case Boolean     => "bool"
      case Byte        => "byte"
      case Short       => "short"
      case Int         => "int"
      case Long        => "long"
      case Float       => "float"
      case Double      => "double"
      case Char        => "char"

  type Ty = Tm1
  enum Tm1:
    case Var(ix: Ix)
    case Prim(prim: Primitive)
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
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk0(t))
      go(n, this)

    def wk1N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm1): Tm1 = if n == 0 then t else go(n - 1, Wk1(t))
      go(n, this)

    def splice: Tm0 = this match
      case Quote(t) => t
      case t        => Tm0.Splice(t)

    override def toString: String = this match
      case Var(ix)                 => s"'$ix"
      case Prim(p)                 => p.toString
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
      case Meta(id)                => s"?$id"
      case MetaPi1(t, b)           => s"($t 1-> $b)"
      case MetaLam1(b)             => s"(\\1 => $b)"
      case MetaPi0(t, b)           => s"($t 0-> $b)"
      case MetaLam0(b)             => s"(\\0 => $b)"
      case MetaApp0(f, a)          => s"($f 0 $a)"
      case MetaApp1(f, a)          => s"($f 1 $a)"
      case AppPruning(id, p)       => s"(?$id ...(${p.size}))"

  enum Locals:
    case Empty
    case Def(locs: Locals, ty: Ty, value: Tm1)
    case Bind0(locs: Locals, ty: Ty, cv: Ty)
    case Bind1(locs: Locals, ty: Ty)

  // values
  enum Env:
    case Empty
    case Ext1(env: Env, value: Val1)
    case Ext0(env: Env, value: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, e: Env): Int = e match
        case Empty      => acc
        case Ext1(e, _) => go(acc + 1, e)
        case Ext0(e, _) => go(acc + 1, e)
      go(0, this)

    inline def wk1: Env = this match
      case Ext1(env, _) => env
      case _            => impossible()

    inline def wk0: Env = this match
      case Ext0(env, _) => env
      case _            => impossible()

    inline def tail: Env = this match
      case Ext0(env, _) => env
      case Ext1(env, _) => env
      case _            => impossible()
  object Env:
    def apply(vs: List[Val1]): Env = vs.foldLeft(Empty)(Ext1.apply)

  enum Clos0:
    case Clos(env: Env, tm: Tm0)
    case Fun(fn: Val0 => Val0)
  object Clos0:
    def apply(tm: Tm0)(using env: Env): Clos0 = Clos(env, tm)

  enum Clos1:
    case Clos(env: Env, tm: Tm1)
    case Fun(fn: Val1 => Val1)
  object Clos1:
    def apply(tm: Tm1)(using env: Env): Clos1 = Clos(env, tm)

  enum Val0:
    case Var(lvl: Lvl)
    case Let(name: Name, ty: VTy, value: Val0, body: Clos0)
    case LetRec(name: Name, ty: VTy, value: Clos0, body: Clos0)
    case Lam(name: Bind, ty: VTy, body: Clos0)
    case App(fn: Val0, arg: Val0)
    case Splice(tm: Val1)

  enum Head:
    case Var(lvl: Lvl)
    case Prim(prim: Primitive)

  enum Spine:
    case Empty
    case App(sp: Spine, arg: Val1, icit: Icit)
    case MetaApp1(sp: Spine, arg: Val1)
    case MetaApp0(sp: Spine, arg: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case Empty           => acc
        case App(sp, _, _)   => go(acc + 1, sp)
        case MetaApp1(sp, _) => go(acc + 1, sp)
        case MetaApp0(sp, _) => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case Empty           => acc
        case App(sp, v, i)   => go(App(acc, v, i), sp)
        case MetaApp1(sp, v) => go(MetaApp1(acc, v), sp)
        case MetaApp0(sp, v) => go(MetaApp0(acc, v), sp)
      go(Empty, this)

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  type VTy = Val1
  enum Val1:
    case Rigid(head: Head, spine: Spine)
    case Flex(id: MetaId, spine: Spine)

    case Pi(name: Bind, icit: Icit, ty: VTy, body: Clos1)
    case Lam(name: Bind, icit: Icit, ty: VTy, body: Clos1)

    case Fun(pty: VTy, cv: VTy, rty: VTy)
    case Lift(cv: VTy, ty: VTy)

    case Quote(tm: Val0)

    case MetaPi1(ty: VTy, body: Clos1)
    case MetaPi0(ty: VTy, body: Clos1)
    case MetaLam1(body: Clos1)
    case MetaLam0(body: Clos1)

  object Val1:
    object Var:
      def apply(lvl: Lvl): Val1 = Rigid(Head.Var(lvl), Spine.Empty)
      def unapply(value: Val1): Option[Lvl] = value match
        case Rigid(Head.Var(hd), Spine.Empty) => Some(hd)
        case _                                => None
