import Common.*
import Common.Icit.*
import Surface.PiIcit

import scala.annotation.tailrec

object Core:
  final case class ProjType(name: Option[Name], ix: Int):
    override def toString: String =
      name match
        case None    => ix.toString
        case Some(x) => x.toString

  enum Cases0 derives CanEqual:
    case Ext(x: Name, ps: List[(Bind, Ty)], body: Tm0, rest: Cases0)
    case Otherwise(body: Tm0)
    case Empty

    override def toString: String =
      this match
        case Ext(x, Nil, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x => $b$next"
        case Ext(x, ps, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x ${ps.map((x, _) => x).mkString(" ")} => $b$next"
        case Otherwise(b) => s"_ => $b"
        case Empty        => s""

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  enum Tm0:
    case Var(ix: Ix)
    case Global(mod: Name, name: Name)
    case IntLit(value: Int)
    case StringLit(value: String)
    case Let(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)

    case Lam(name: Bind, ty: Ty, body: Tm0)
    case App(fn: Tm0, arg: Tm0)

    case Splice(tm: Tm1)

    case If(rty: Ty, cond: Tm0, ifTrue: Tm0, ifFalse: Tm0)
    case Case(rty: Ty, dty: Ty, scrut: Tm0, cases: Cases0)

    case RecordCon(ty: Ty, fields: List[Tm0])
    case Proj(rty: Ty, scrut: Tm0, p: ProjType)

    case Unsafe(rty: Tm1, io: Boolean, label: Tm1, args: List[Tm0])

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
        (hd, args :+ a)
      case t => (t, Nil)

    override def toString: String = this match
      case Var(ix)                     => s"'$ix"
      case Global(m, x)                => s"$m.$x"
      case IntLit(v)                   => s"$v"
      case StringLit(v)                => s"\"$v\""
      case Let(x, ty, v, b)            => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b)         => s"(let rec $x : $ty := $v; $b)"
      case Lam(x, ty, b)               => s"(\\($x : $ty) => $b)"
      case App(fn, arg)                => s"($fn $arg)"
      case Splice(tm)                  => s"$$$tm"
      case If(_, c, t, f)              => s"(if $c then $t else $f)"
      case Wk1(tm)                     => s"Wk10($tm)"
      case Wk0(tm)                     => s"Wk00($tm)"
      case Case(_, _, s, Cases0.Empty) => s"(match $s)"
      case Case(_, _, s, cs)           => s"(match $s { $cs })"
      case Proj(_, s, p)               => s"$s.$p"
      case RecordCon(_, fs)            => fs.mkString("[", ", ", "]")
      case Unsafe(_, io, l, Nil) => s"(unsafe${if io then "IO" else ""} $l)"
      case Unsafe(_, io, l, args) =>
        s"(unsafe${if io then "IO" else ""} $l ${args.mkString(" ")})"

  object Tm0:
    def RecordConEmpty(cv: Ty) = RecordCon(Tm1.RecordTy0Empty(cv), Nil)

  enum Cases1 derives CanEqual:
    case Ext(x: Name, ps: List[(Bind, Icit, Ty)], body: Tm1, rest: Cases1)
    case Otherwise(body: Tm1)
    case Empty

    override def toString: String =
      this match
        case Ext(x, Nil, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x => $b$next"
        case Ext(x, ps, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x ${ps.map((x, i, _) => i.wrapI(x)).mkString(" ")} => $b$next"
        case Otherwise(b) => s"_ => $b"
        case Empty        => s""

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  type Ty = Tm1
  enum Tm1:
    case Var(ix: Ix)
    case Global(mod: Name, name: Name, value: Val1)
    case Prim(prim: Primitive)
    case LabelLit(value: String)
    case TypeCon1(mod: Name, name: Name)
    case Con1(mod: Name, dx: Name, cx: Name)
    case TypeCon0(mod: Name, name: Name)
    case Con0(mod: Name, dx: Name, cx: Name)
    case Let(name: Name, ty: Ty, value: Tm1, body: Tm1)

    case Pi(name: Bind, icit: PiIcit, ty: Ty, body: Ty)
    case Lam(name: Bind, icit: PiIcit, ty: Ty, body: Tm1)
    case App(fn: Tm1, arg: Tm1, icit: Icit)

    case Fun(pty: Ty, cv: Ty, rty: Ty)

    case Lift(cv: Ty, ty: Ty)
    case Quote(tm: Tm0)

    case RecordTy1(fields: AssocBind[Ty])
    case RecordTy0(cv: Ty, fields: AssocBind[Ty])
    case RecordCon(fields: List[Tm1])
    case Proj(tm: Tm1, proj: ProjType)

    case Case(scrut: Tm1, cases: Cases1)

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
    case PostponedCheck(id: CheckId)

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
      case Var(ix)            => s"'$ix"
      case Global(m, x, _)    => s"$m.$x"
      case Prim(p)            => s"$p"
      case LabelLit(v)        => s"\"$v\""
      case TypeCon1(m, x)     => s"$m.$x"
      case Con1(m, _, x)      => s"$m.$x"
      case TypeCon0(m, x)     => s"$m.$x"
      case Con0(m, _, x)      => s"$m.$x"
      case Let(x, ty, v, b)   => s"(let $x : $ty = $v; $b)"
      case Pi(x, i, ty, b)    => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, i, ty, b)   => s"(\\${i.wrap(s"$x : $ty")} => $b)"
      case App(fn, arg, Expl) => s"($fn $arg)"
      case App(fn, arg, i)    => s"($fn ${i.wrap(arg)})"
      case Fun(pty, _, rty)   => s"($pty -> $rty)"
      case Lift(_, ty)        => s"^$ty"
      case Quote(tm)          => s"`$tm"
      case RecordTy1(fs) =>
        fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case RecordTy0(_, fs) =>
        fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case RecordCon(fs)         => fs.mkString("[", ", ", "]")
      case Proj(tm, p)           => s"$tm.$p"
      case Case(s, Cases1.Empty) => s"(match $s)"
      case Case(s, cs)           => s"(match $s { $cs })"
      case Wk0(tm)               => s"Wk01($tm)"
      case Wk1(tm)               => s"Wk11($tm)"
      case Meta(id)              => s"?$id"
      case MetaPi1(t, b)         => s"($t 1-> $b)"
      case MetaLam1(b)           => s"(\\1 => $b)"
      case MetaPi0(t, b)         => s"($t 0-> $b)"
      case MetaLam0(b)           => s"(\\0 => $b)"
      case MetaApp0(f, a)        => s"($f 0 $a)"
      case MetaApp1(f, a)        => s"($f 1 $a)"
      case AppPruning(id, p)     => s"(?$id ...(${p.size}))"
      case PostponedCheck(id)    => s"??$id"

  object Tm1:
    val MetaU = Prim(Primitive.Meta)
    val CV = Prim(Primitive.CV)
    val Val = Prim(Primitive.Val)
    val Comp = Prim(Primitive.Comp)
    val TypeV = App(Prim(Primitive.Type), Val, Expl)
    val TypeC = App(Prim(Primitive.Type), Comp, Expl)

    val RecordTy1Empty = RecordTy1(Nil)
    def RecordTy0Empty(cv: Ty) = RecordTy0(cv, Nil)
    val RecordConEmpty = RecordCon(Nil)

    def ElimId(a: Tm1, x: Tm1, pp: Tm1, hh: Tm1, y: Tm1, p: Tm1): Tm1 =
      Tm1.App(
        Tm1.App(
          Tm1.App(
            Tm1.App(
              Tm1.App(Tm1.App(Tm1.Prim(Primitive.ElimId), a, Impl), x, Impl),
              pp,
              Expl
            ),
            hh,
            Expl
          ),
          y,
          Impl
        ),
        p,
        Expl
      )

    def FixIx(ii: Tm1, a: Tm1, b: Tm1, f: Tm1, i: Tm1, x: Tm1): Tm1 =
      Tm1.App(
        Tm1.App(
          Tm1.App(
            Tm1.App(
              Tm1.App(
                Tm1.App(Tm1.Prim(Primitive.FixIx), ii, Impl),
                a,
                Impl
              ),
              b,
              Impl
            ),
            f,
            Expl
          ),
          i,
          Impl
        ),
        x,
        Expl
      )

  enum Locals derives CanEqual:
    case Empty
    case Def(locs: Locals, ty: Ty, value: Tm1)
    case Bind0(locs: Locals, ty: Ty, cv: Ty)
    case Bind1(locs: Locals, ty: Ty)

  // values
  enum Env derives CanEqual:
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

    inline def exts1(vs: List[Val1]): Env = vs.foldLeft(this)(Ext1.apply)
  object Env:
    def apply(vs: List[Val1]): Env = vs.foldLeft(Empty)(Ext1.apply)

  enum Clos0:
    case Clos(env: Env, tm: Tm0)
    case Fun(fn: Val0 => Val0)
  object Clos0:
    def apply(tm: Tm0)(using env: Env): Clos0 = Clos(env, tm)

  final case class ClosCases0(env: Env, cases: Cases0)
  object ClosCases0:
    def apply(cases: Cases0)(using env: Env): ClosCases0 =
      ClosCases0(env, cases)

  enum Clos1:
    case Clos(env: Env, tm: Tm1)
    case Fun(fn: Val1 => Val1)
  object Clos1:
    def apply(tm: Tm1)(using env: Env): Clos1 = Clos(env, tm)

  final case class ClosRec(env: Env, fields: AssocBind[Ty]):
    def add(v: Val1): ClosRec = ClosRec(Env.Ext1(env, v), fields.tail)
  object ClosRec:
    def apply(fields: AssocBind[Ty])(using env: Env): ClosRec =
      ClosRec(env, fields)

  final case class ClosCases1(env: Env, cases: Cases1)
  object ClosCases1:
    def apply(cases: Cases1)(using env: Env): ClosCases1 =
      ClosCases1(env, cases)

  enum Val0:
    case Var(lvl: Lvl)
    case Global(mod: Name, name: Name)
    case IntLit(value: Int)
    case StringLit(value: String)
    case Let(name: Name, ty: VTy, value: Val0, body: Clos0)
    case LetRec(name: Name, ty: VTy, value: Clos0, body: Clos0)
    case Lam(name: Bind, ty: VTy, body: Clos0)
    case App(fn: Val0, arg: Val0)
    case If(rty: VTy, cond: Val0, ifTrue: Val0, ifFalse: Val0)
    case Case(rty: VTy, dty: VTy, scrut: Val0, cases: ClosCases0)
    case Proj(rty: VTy, scrut: Val0, p: ProjType)
    case RecordCon(ty: VTy, fields: List[Val0])
    case Splice(tm: Val1)
    case Unsafe(rty: Val1, io: Boolean, label: Val1, args: List[Val0])

  enum Head derives CanEqual:
    case Var(lvl: Lvl)
    case Prim(prim: Primitive)
    case TypeCon1(mod: Name, name: Name)
    case Con1(mod: Name, dx: Name, cx: Name)
    case TypeCon0(mod: Name, name: Name)
    case Con0(mod: Name, dx: Name, cx: Name)

  enum UnfoldHead:
    case Global(mod: Name, name: Name, value: Val1)

  enum Spine derives CanEqual:
    case Empty
    case App(sp: Spine, arg: Val1, icit: Icit)
    case Proj(sp: Spine, proj: ProjType)
    case ElimId(sp: Spine, a: Val1, x: Val1, pp: Val1, h: Val1, y: Val1)
    case FixIx(sp: Spine, ii: Val1, a: Val1, b: Val1, f: Val1, i: Val1)
    case Case(sp: Spine, cases: ClosCases1)
    case MetaApp1(sp: Spine, arg: Val1)
    case MetaApp0(sp: Spine, arg: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case Empty                     => acc
        case App(sp, _, _)             => go(acc + 1, sp)
        case Proj(sp, _)               => go(acc + 1, sp)
        case ElimId(sp, _, _, _, _, _) => go(acc + 1, sp)
        case FixIx(sp, _, _, _, _, _)  => go(acc + 1, sp)
        case Case(sp, _)               => go(acc + 1, sp)
        case MetaApp1(sp, _)           => go(acc + 1, sp)
        case MetaApp0(sp, _)           => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case Empty                      => acc
        case App(sp, v, i)              => go(App(acc, v, i), sp)
        case Proj(sp, p)                => go(Proj(acc, p), sp)
        case ElimId(sp, a, x, pp, h, y) => go(ElimId(acc, a, x, pp, h, y), sp)
        case FixIx(sp, ii, a, b, f, i)  => go(FixIx(acc, ii, a, b, f, i), sp)
        case Case(sp, cs)               => go(Case(acc, cs), sp)
        case MetaApp1(sp, v)            => go(MetaApp1(acc, v), sp)
        case MetaApp0(sp, v)            => go(MetaApp0(acc, v), sp)
      go(Empty, this)

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

    def toList: List[(Val1, Icit)] = this match
      case Spine.App(sp, arg, i) => sp.toList :+ (arg, i)
      case Spine.Empty           => Nil
      case _                     => impossible()

  object Spine:
    def apps(args: List[(Val1, Icit)]): Spine =
      args.foldLeft(Spine.Empty) { case (s, (a, i)) => Spine.App(s, a, i) }

  type VTy = Val1
  enum Val1 derives CanEqual:
    case Rigid(head: Head, spine: Spine)
    case Flex(id: MetaId, spine: Spine)
    case Unfold(head: UnfoldHead, spine: Spine, value: () => Val1)

    case LabelLit(value: String)

    case Pi(name: Bind, icit: PiIcit, ty: VTy, body: Clos1)
    case Lam(name: Bind, icit: PiIcit, ty: VTy, body: Clos1)

    case Fun(pty: VTy, cv: VTy, rty: VTy)
    case Lift(cv: VTy, ty: VTy)

    case Quote(tm: Val0)

    case RecordTy1(fields: ClosRec)
    case RecordTy0(cv: VTy, fields: AssocBind[VTy])
    case RecordCon(fields: List[Val1])

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

    object TypeCon1:
      def apply(
          mod: Name,
          name: Name,
          args: List[(VTy, Icit)] = Nil
      ): Val1 =
        Rigid(Head.TypeCon1(mod, name), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, Name, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.TypeCon1(mod, hd), spine) =>
            Some((mod, hd, spine.toList))
          case _ => None

    object TypeCon0:
      def apply(
          mod: Name,
          name: Name,
          args: List[(VTy, Icit)] = Nil
      ): Val1 =
        Rigid(Head.TypeCon0(mod, name), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, Name, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.TypeCon0(mod, hd), spine) =>
            Some((mod, hd, spine.toList))
          case _ => None

    object Con1:
      def apply(
          mod: Name,
          dx: Name,
          cx: Name,
          args: List[(VTy, Icit)] = Nil
      ): Val1 =
        Rigid(Head.Con1(mod, dx, cx), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, Name, Name, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.Con1(mod, dx, cx), spine) =>
            Some((mod, dx, cx, spine.toList))
          case _ => None

    object Con0:
      def apply(
          mod: Name,
          dx: Name,
          cx: Name,
          args: List[(VTy, Icit)] = Nil
      ): Val1 =
        Rigid(Head.Con0(mod, dx, cx), Spine.apps(args))
      def unapply(value: Val1): Option[(Name, Name, Name, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.Con0(mod, dx, cx), spine) =>
            Some((mod, dx, cx, spine.toList))
          case _ => None

    object Type:
      def apply(cv: Val1): Val1 =
        Rigid(Head.Prim(Primitive.Type), Spine.App(Spine.Empty, cv, Expl))
      def unapply(value: Val1): Option[Val1] = value match
        case Rigid(
              Head.Prim(Primitive.Type),
              Spine.App(Spine.Empty, cv, Expl)
            ) =>
          Some(cv)
        case _ => None

    object IO:
      def apply(ty: Val1): Val1 =
        Rigid(Head.Prim(Primitive.IO), Spine.App(Spine.Empty, ty, Expl))
      def unapply(value: Val1): Option[Val1] = value match
        case Rigid(
              Head.Prim(Primitive.IO),
              Spine.App(Spine.Empty, ty, Expl)
            ) =>
          Some(ty)
        case _ => None

    object Id:
      def apply(ty1: Val1, ty2: Val1, v1: Val1, v2: Val1): Val1 =
        Rigid(
          Head.Prim(Primitive.Id),
          Spine.App(
            Spine
              .App(
                Spine.App(Spine.App(Spine.Empty, ty1, Impl), ty2, Impl),
                v1,
                Expl
              ),
            v2,
            Expl
          )
        )
      def unapply(value: Val1): Option[(Val1, Val1, Val1, Val1)] = value match
        case Rigid(
              Head.Prim(Primitive.Id),
              Spine.App(
                Spine
                  .App(
                    Spine.App(Spine.App(Spine.Empty, ty1, Impl), ty2, Impl),
                    v1,
                    Expl
                  ),
                v2,
                Expl
              )
            ) =>
          Some((ty1, ty2, v1, v2))
        case _ => None

    object Refl:
      def apply(ty: Val1, v: Val1): Val1 =
        Rigid(
          Head.Prim(Primitive.Refl),
          Spine.App(Spine.App(Spine.Empty, ty, Impl), v, Impl)
        )
      def unapply(value: Val1): Option[(Val1, Val1)] = value match
        case Rigid(
              Head.Prim(Primitive.Refl),
              Spine.App(Spine.App(Spine.Empty, ty, Impl), v, Impl)
            ) =>
          Some((ty, v))
        case _ => None

    object PrimArgs:
      def apply(p: Primitive, args: List[(VTy, Icit)] = Nil): Val1 =
        Rigid(Head.Prim(p), Spine.apps(args))
      def unapply(value: Val1): Option[(Primitive, List[(VTy, Icit)])] =
        value match
          case Rigid(Head.Prim(p), spine) => Some((p, spine.toList))
          case _                          => None

    object Class:
      def apply(l: Val1): Val1 =
        Rigid(Head.Prim(Primitive.Class), Spine.App(Spine.Empty, l, Expl))
      def unapply(value: Val1): Option[Val1] = value match
        case Rigid(
              Head.Prim(Primitive.Class),
              Spine.App(Spine.Empty, l, Expl)
            ) =>
          Some(l)
        case _ => None

    val Meta = Prim(Primitive.Meta)
    val CV = Prim(Primitive.CV)
    val Val = Prim(Primitive.Val)
    val Comp = Prim(Primitive.Comp)
    val Bool = Prim(Primitive.Bool)
    val Int = Prim(Primitive.Int)
    val Label = Prim(Primitive.Label)
    val String = Class(LabelLit("java.lang.String"))

    val TypeV = Type(Val)
    val TypeC = Type(Comp)

    inline def RecordTy1Empty(using env: Env) = RecordTy1(ClosRec(Nil))
    def RecordTy0Empty(cv: VTy) = RecordTy0(cv, Nil)
    val RecordConEmpty = RecordCon(Nil)

    // helpers
    private inline def bind(x: String): Bind =
      if x == "_" then Bind.DontBind else Bind.DoBind(Name(x))
    def lam1(x: String, ty: VTy, b: Val1 => Val1): Val1 =
      Val1.Lam(bind(x), PiIcit.Expl, ty, Clos1.Fun(b))
    def lamI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
      Val1.Lam(bind(x), PiIcit.ImplU, ty, Clos1.Fun(b))
    def fun1(ty: VTy, rt: VTy): VTy =
      Val1.Pi(Bind.DontBind, PiIcit.Expl, ty, Clos1.Fun(_ => rt))
    def pi(x: String, ty: VTy, b: VTy => VTy): VTy =
      Val1.Pi(bind(x), PiIcit.Expl, ty, Clos1.Fun(b))
    def piI(x: String, ty: VTy, b: Val1 => VTy): VTy =
      Val1.Pi(bind(x), PiIcit.ImplU, ty, Clos1.Fun(b))
    def liftV(ty: VTy): VTy = Lift(Val, ty)
    def liftC(ty: VTy): VTy = Lift(Comp, ty)
