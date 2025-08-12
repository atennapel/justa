package core

import common.Common
import common.Common.*

import scala.annotation.tailrec

object Core:
  final case class Module(name: Name, defs: Defs):
    override def toString: String =
      s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Constructor(name: Name, parameters: List[(Bind, Ty)])

  enum Def:
    case D0(
        public: Boolean,
        name: Name,
        ty: Ty,
        value: Tm0
    )
    case D1(
        public: Boolean,
        name: Name,
        ty: Ty,
        value: Tm1
    )
    case Primitive(
        public: Boolean,
        name: Name,
        ty: Ty
    )
    case Data(
        kind: DataKind,
        public: Boolean,
        name: Name,
        params: List[Name],
        cons: List[Constructor]
    )

    override def toString: String = this match
      case D0(p, x, t, v) =>
        s"${if p then "pub " else ""}def $x : $t := $v"
      case D1(p, x, t, v) =>
        s"${if p then "pub " else ""}def $x : $t = $v"
      case Primitive(p, x, t) =>
        s"${if p then "pub " else ""}primitive $x : $t"
      case Data(k, p, x, ps, cs) =>
        s"${if p then "pub " else ""}$k $x ${ps.mkString(" ")} = ${cs.map(c => s"$c ${c.parameters.map((x, t) => s"($x : $t)").mkString(" ")}").mkString(" | ")}"

  enum Tm0:
    case Var(ix: Ix)
    case IntLit(value: Int)
    case Global(mod: Name, name: Name)
    case Select(dty: Tm1, cx: Name, scrut: Tm0, ix: Int)
    case Let(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case LetRec(name: Name, ty: Ty, value: Tm0, body: Tm0)
    case Lam(name: Bind, ty: Ty, body: Tm0)
    case App(fn: Tm0, arg: Tm0)
    case Splice(tm: Tm1)
    case Instr(instr: String, types: List[Ty], returntype: Ty, args: List[Tm0])
    case Match(
        rty: Ty,
        dty: Ty,
        scrut: Tm0,
        cases: List[(Name, Tm0)],
        otherwise: Option[Tm0]
    )
    case Wk1(tm: Tm0)
    case Wk0(tm: Tm0)

    def wk0N(n: Int) =
      @tailrec
      def go(n: Int, t: Tm0): Tm0 = if n == 0 then t else go(n - 1, Wk0(t))
      go(n, this)

    def quote: Tm1 = this match
      case Tm0.Splice(t) => t
      case t             => Tm1.Quote(t)

    def flattenApps: (Tm0, List[Tm0]) = this match
      case Tm0.App(f, a) =>
        val (hd, args) = f.flattenApps
        (hd, args ++ List(a))
      case t => (t, Nil)

    override def toString: String = this match
      case Var(ix)                     => s"'$ix"
      case IntLit(v)                   => v.toString
      case Select(_, _, s, i)          => s"(select $i $s)"
      case Global(m, x)                => s"$m.$x"
      case Let(x, ty, v, b)            => s"(let $x : $ty := $v; $b)"
      case LetRec(x, ty, v, b)         => s"(let rec $x : $ty := $v; $b)"
      case Lam(x, ty, b)               => s"(\\($x : $ty) => $b)"
      case App(fn, arg)                => s"($fn $arg)"
      case Splice(tm)                  => s"$$$tm"
      case Instr(x, _, _, args)        => s"(instr $x ${args.mkString(" ")})"
      case Match(_, _, s, cs, Some(o)) =>
        s"(match $s { ${cs.map((x, b) => s"$x => $b").mkString(" | ")} | _ => $o })"
      case Match(_, _, s, cs, None) =>
        s"(match $s { ${cs.map((x, b) => s"$x => $b").mkString(" | ")} })"
      case Wk1(tm) => s"Wk10($tm)"
      case Wk0(tm) => s"Wk00($tm)"

  type Ty = Tm1
  enum Tm1:
    case Var(ix: Ix)
    case Primitive(mod: Name, name: Name)
    case Con(mod: Name, dx: Name, cx: Name)
    case TypeCon(kind: DataKind, mod: Name, name: Name)
    case Global(mod: Name, name: Name, value: Val1)
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
      case Primitive(m, x)         => s"$m.$x"
      case Global(m, x, _)         => s"$m.$x"
      case Con(m, _, cx)           => s"$m.$cx"
      case TypeCon(_, m, x)        => s"$m.$x"
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

  // values
  enum Clos0:
    case Clos(env: Env, tm: Tm0)
    case Fun(fn: Val0 => Val0)

  object Clos0:
    def apply(tm: Tm0)(using env: Env): Clos0 = Clos0.Clos(env, tm)

  enum Clos1:
    case Clos(env: Env, tm: Tm1)
    case Fun(fn: Val1 => Val1)

  object Clos1:
    def apply(tm: Tm1)(using env: Env): Clos1 = Clos1.Clos(env, tm)

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

    inline def lvl: Lvl = mkLvl(size)

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

    def toList: List[(Val1, Icit)] = this match
      case Spine.App(sp, arg, i) => sp.toList ++ List((arg, i))
      case Spine.Empty           => Nil
  object Spine:
    def apps(args: List[(Val1, Icit)]): Spine =
      args.foldLeft(Spine.Empty) { case (s, (a, i)) => Spine.App(s, a, i) }

  enum Val0:
    case Var(lvl: Lvl)
    case IntLit(value: Int)
    case Global(mod: Name, name: Name)
    case Select(dty: VTy, cx: Name, scrut: Val0, ix: Int)
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
    case Instr(
        instr: String,
        types: List[VTy],
        returntype: VTy,
        args: List[Val0]
    )
    case Match(
        rty: VTy,
        dty: VTy,
        scrut: Val0,
        cases: List[(Name, Clos0)],
        otherwise: Option[Val0]
    )

  enum Head:
    case Var(lvl: Lvl)
    case Primitive(mod: Name, name: Name)
    case Con(mod: Name, dx: Name, cx: Name)
    case TypeCon(kind: DataKind, mod: Name, name: Name)

  enum UnfoldHead:
    case Global(mod: Name, name: Name, value: Val1)

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

  private inline def bind(x: String): Bind =
    if x == "_" then Bind.DontBind else Bind.DoBind(Name(x))
  def vlam1(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    Val1.Lam(bind(x), Icit.Expl, ty, Clos1.Fun(b))
  def vlamI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    Val1.Lam(bind(x), Icit.Impl, ty, Clos1.Fun(b))
  def vfun1(ty: VTy, rt: VTy): Val1 =
    Val1.Pi(Bind.DontBind, Icit.Expl, ty, Clos1.Fun(_ => rt))
  def vpi(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    Val1.Pi(bind(x), Icit.Expl, ty, Clos1.Fun(b))
  def vpiI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    Val1.Pi(bind(x), Icit.Impl, ty, Clos1.Fun(b))

  val TyVal: Ty = Tm1.UTy(Tm1.Val)
  val TyComp: Ty = Tm1.UTy(Tm1.Comp)
  val VTyVal: VTy = Val1.UTy(Val1.Val)
  val VTyComp: VTy = Val1.UTy(Val1.Comp)

  object Var1:
    def apply(lvl: Lvl): Val1 = Val1.Rigid(Head.Var(lvl), Spine.Empty)
    def unapply(value: Val1): Option[Lvl] = value match
      case Val1.Rigid(Head.Var(hd), Spine.Empty) => Some(hd)
      case _                                     => None

  object VPrimitive:
    def apply(mod: Name, name: Name, args: List[(Val1, Icit)] = Nil): Val1 =
      Val1.Rigid(Head.Primitive(mod, name), Spine.apps(args))
    def unapply(value: Val1): Option[(Name, Name, List[(Val1, Icit)])] =
      value match
        case Val1.Rigid(Head.Primitive(mod, name), spine) =>
          Some((mod, name, spine.toList))
        case _ => None

  object VCon:
    def apply(
        mod: Name,
        name: Name,
        cx: Name,
        params: List[(VTy, Icit)] = Nil
    ): Val1 =
      Val1.Rigid(Head.Con(mod, name, cx), Spine.apps(params))
    def unapply(value: Val1): Option[(Name, Name, Name, List[(VTy, Icit)])] =
      value match
        case Val1.Rigid(Head.Con(mod, name, cx), spine) =>
          Some((mod, name, cx, spine.toList))
        case _ => None

  object VTypeCon:
    def apply(
        kind: DataKind,
        mod: Name,
        name: Name,
        params: List[(VTy, Icit)] = Nil
    ): Val1 =
      Val1.Rigid(Head.TypeCon(kind, mod, name), Spine.apps(params))
    def unapply(
        value: Val1
    ): Option[(DataKind, Name, Name, List[(VTy, Icit)])] =
      value match
        case Val1.Rigid(Head.TypeCon(kind, mod, name), spine) =>
          Some((kind, mod, name, spine.toList))
        case _ => None
