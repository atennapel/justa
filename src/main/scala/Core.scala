import Common.*

import scala.annotation.tailrec

object Core:
  enum Cases:
    case Ext(x: Name, ps: List[(Bind, Ty)], body: Tm0, rest: Cases)
    case Otherwise(body: Tm0)
    case Empty

    override def toString: String =
      this match
        case Cases.Ext(x, Nil, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x => $b$next"
        case Cases.Ext(x, ps, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x ${ps.map((x, _) => x).mkString(" ")} => $b$next"
        case Cases.Otherwise(b) => s"_ => $b"
        case Cases.Empty        => s""

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  enum Tm0:
    case Var(ix: Ix)
    case Global(name: Name)
    case IntLit(value: Int)
    case Let(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)

    case Lam(name: Bind, ty: Ty, body: Tm0)
    case App(fn: Tm0, arg: Tm0)

    case Splice(tm: Tm1)

    case If(rty: Ty, cond: Tm0, ifTrue: Tm0, ifFalse: Tm0)
    case Case(rty: Ty, dty: Ty, scrut: Tm0, cases: Cases)

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
      case Var(ix)                    => s"'$ix"
      case Global(x)                  => s"$x"
      case IntLit(v)                  => s"$v"
      case Let(x, ty, v, b)           => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b)        => s"(let rec $x : $ty := $v; $b)"
      case Lam(x, ty, b)              => s"(\\($x : $ty) => $b)"
      case App(fn, arg)               => s"($fn $arg)"
      case Splice(tm)                 => s"$$$tm"
      case If(_, c, t, f)             => s"(if $c then $t else $f)"
      case Wk1(tm)                    => s"Wk10($tm)"
      case Wk0(tm)                    => s"Wk00($tm)"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"

  type Ty = Tm1
  enum Tm1:
    case Var(ix: Ix)
    case Global(name: Name)
    case Prim(prim: Primitive)
    case TypeCon(name: Name)
    case Con(dx: Name, cx: Name)
    case Let(name: Name, ty: Ty, value: Tm1, body: Tm1)

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
      case Global(x)               => s"$x"
      case Prim(p)                 => s"$p"
      case TypeCon(x)              => s"$x"
      case Con(_, x)               => s"$x"
      case Let(x, ty, v, b)        => s"(let $x : $ty = $v; $b)"
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

  object Tm1:
    val CV = Prim(Primitive.CV)
    val Val = Prim(Primitive.Val)
    val Comp = Prim(Primitive.Comp)
    val TypeV = App(Prim(Primitive.Type), Val, Icit.Expl)
    val TypeC = App(Prim(Primitive.Type), Comp, Icit.Expl)

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

  final case class ClosCases(env: Env, cases: Cases)
  object ClosCases:
    def apply(cases: Cases)(using env: Env): ClosCases = ClosCases(env, cases)

  enum Clos1:
    case Clos(env: Env, tm: Tm1)
    case Fun(fn: Val1 => Val1)
  object Clos1:
    def apply(tm: Tm1)(using env: Env): Clos1 = Clos(env, tm)

  enum Val0:
    case Var(lvl: Lvl)
    case Global(name: Name)
    case IntLit(value: Int)
    case Let(name: Name, ty: VTy, value: Val0, body: Clos0)
    case LetRec(name: Name, ty: VTy, value: Clos0, body: Clos0)
    case Lam(name: Bind, ty: VTy, body: Clos0)
    case App(fn: Val0, arg: Val0)
    case If(rty: VTy, cond: Val0, ifTrue: Val0, ifFalse: Val0)
    case Case(rty: VTy, dty: VTy, scrut: Val0, cases: ClosCases)
    case Splice(tm: Val1)

  enum Head:
    case Var(lvl: Lvl)
    case Prim(prim: Primitive)
    case TypeCon(name: Name)
    case Con(dx: Name, cx: Name)

  enum UnfoldHead:
    case Global(name: Name)

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

    def toList: List[(Val1, Icit)] = this match
      case Spine.App(sp, arg, i) => sp.toList ++ List((arg, i))
      case Spine.Empty           => Nil
      case _                     => impossible()

  object Spine:
    def apps(args: List[(Val1, Icit)]): Spine =
      args.foldLeft(Spine.Empty) { case (s, (a, i)) => Spine.App(s, a, i) }

  type VTy = Val1
  enum Val1:
    case Rigid(head: Head, spine: Spine)
    case Flex(id: MetaId, spine: Spine)
    case Unfold(head: UnfoldHead, spine: Spine, value: () => Val1)

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

    object Prim:
      def apply(prim: Primitive): Val1 = Rigid(Head.Prim(prim), Spine.Empty)
      def unapply(value: Val1): Option[Primitive] = value match
        case Rigid(Head.Prim(hd), Spine.Empty) => Some(hd)
        case _                                 => None

    object TypeCon:
      def apply(name: Name, args: List[(VTy, Icit)] = Nil): Val1 =
        Rigid(Head.TypeCon(name), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, List[(VTy, Icit)])] = value match
        case Rigid(Head.TypeCon(hd), spine) => Some((hd, spine.toList))
        case _                              => None

    object Con:
      def apply(dx: Name, cx: Name, args: List[(VTy, Icit)] = Nil): Val1 =
        Rigid(Head.Con(dx, cx), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, Name, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.Con(dx, cx), spine) => Some((dx, cx, spine.toList))
          case _                              => None

    object Type:
      def apply(cv: Val1): Val1 =
        Rigid(Head.Prim(Primitive.Type), Spine.App(Spine.Empty, cv, Icit.Expl))
      def unapply(value: Val1): Option[Val1] = value match
        case Rigid(
              Head.Prim(Primitive.Type),
              Spine.App(Spine.Empty, cv, Icit.Expl)
            ) =>
          Some(cv)
        case _ => None

    object IO:
      def apply(ty: Val1): Val1 =
        Rigid(Head.Prim(Primitive.IO), Spine.App(Spine.Empty, ty, Icit.Expl))
      def unapply(value: Val1): Option[Val1] = value match
        case Rigid(
              Head.Prim(Primitive.IO),
              Spine.App(Spine.Empty, ty, Icit.Expl)
            ) =>
          Some(ty)
        case _ => None

    val Meta = Prim(Primitive.Meta)
    val CV = Prim(Primitive.CV)
    val Val = Prim(Primitive.Val)
    val Comp = Prim(Primitive.Comp)
    val Bool = Prim(Primitive.Bool)
    val Int = Prim(Primitive.Int)

    val TypeV = Type(Val)
    val TypeC = Type(Comp)

    // helpers
    private inline def bind(x: String): Bind =
      if x == "_" then Bind.DontBind else Bind.DoBind(Name(x))
    def lam1(x: String, ty: VTy, b: Val1 => Val1): Val1 =
      Val1.Lam(bind(x), Icit.Expl, ty, Clos1.Fun(b))
    def lamI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
      Val1.Lam(bind(x), Icit.Impl, ty, Clos1.Fun(b))
    def fun1(ty: VTy, rt: VTy): VTy =
      Val1.Pi(Bind.DontBind, Icit.Expl, ty, Clos1.Fun(_ => rt))
    def pi(x: String, ty: VTy, b: VTy => VTy): VTy =
      Val1.Pi(bind(x), Icit.Expl, ty, Clos1.Fun(b))
    def piI(x: String, ty: VTy, b: Val1 => VTy): VTy =
      Val1.Pi(bind(x), Icit.Impl, ty, Clos1.Fun(b))
    def liftV(ty: VTy): VTy = Lift(Val, ty)
    def liftC(ty: VTy): VTy = Lift(Comp, ty)
