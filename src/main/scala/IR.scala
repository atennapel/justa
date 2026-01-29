import Common.*

object IR:
  enum VTy derives CanEqual:
    case Bool
    case Int
    case Data(mod: Name, name: Name, args: List[VTy])
    case Record(fields: AssocBind[VTy])

    override def toString: String = this match
      case Bool             => "Bool"
      case Int              => "Int"
      case Data(m, x, Nil)  => s"$m.$x"
      case Data(m, x, args) => s"($m.$x ${args.mkString(" ")})"
      case Record(fs) => fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")

  /*
  final case class CTy(params: List[VTy], io: Boolean, ret: VTy):
    def head: VTy = params.head
    def tail: CTy = CTy(params.tail, io, ret)
    def drop(n: Int): CTy = CTy(params.drop(n), io, ret)
    override def toString: String =
      params match
        case Nil if !io => s"$ret"
        case Nil        => s"IO $ret"
        case _ =>
          s"${params.mkString("(", ",", ")")} ->${if io then " IO" else ""} $ret"
  object CTy:
    def apply(ret: VTy): CTy = CTy(Nil, false, ret)
    def apply(param: VTy, ret: VTy): CTy = CTy(List(param), false, ret)
    def apply(param: VTy, ret: CTy): CTy =
      CTy(param :: ret.params, ret.io, ret.ret)
   */

  enum CTy derives CanEqual:
    case CUnit
    case CPair(fst: CTy, snd: CTy)
    case Fun(pty: VTy, rty: CTy)
    case IO(ty: VTy)
    case Val(ty: VTy)

    override def toString: String = this match
      case CUnit           => "()"
      case CPair(fst, snd) => s"($fst * $snd)"
      case Fun(pty, rty)   => s"($pty -> $rty)"
      case IO(ty)          => s"(IO $ty)"
      case Val(ty)         => s"$ty"

  object CTy:
    def apply(ty: VTy): CTy = CTy.Val(ty)

  final case class Module(name: Name, defs: Defs):
    override def toString: String = s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Def(pub: Boolean, name: Name, ty: CTy, value: Tm):
    override def toString: String =
      s"${if pub then "pub " else ""}def $name : $ty = $value"

  enum Cases derives CanEqual:
    case Ext(x: Name, ps: List[(LocalName, VTy, Int)], body: Tm, rest: Cases)
    case Otherwise(body: Tm)
    case Empty

    override def toString: String =
      this match
        case Cases.Ext(x, Nil, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x => $b$next"
        case Cases.Ext(x, ps, b, r) =>
          val next = if r.isEmpty then "" else s" | $r}"
          s"$x ${ps.map((x, _, _) => s"'$x").mkString(" ")} => $b$next"
        case Cases.Otherwise(b) => s"_ => $b"
        case Cases.Empty        => s""

    def isEmpty: Boolean = this match
      case Empty => true
      case _     => false

  type LocalName = Int
  enum Tm derives CanEqual:
    case Local(ix: LocalName, ty: CTy)
    case Global(mod: Name, name: Name, ty: CTy)
    case Prim(prim: RuntimePrimitive)
    case BoolLit(value: Boolean)
    case IntLit(value: Int)

    case Let(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)
    case LetRec(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)

    case Lam(name: LocalName, usage: Int, ty: VTy, body: Tm)
    case App(fn: Tm, arg: Tm)

    case If(rty: CTy, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Con(mod: Name, dx: Name, cx: Name, ix: Int, ty: VTy, args: List[Tm])
    case Case(rty: CTy, dty: VTy, scrut: Tm, cases: Cases)
    case Record(dty: VTy, args: List[Tm])
    case Select(rty: VTy, scrut: Tm, i: Int)

    case ReturnIO(ty: VTy, value: Tm)
    case BindIO(name: LocalName, usage: Int, ty: VTy, value: Tm, body: Tm)

    case CUnit
    case CPair(fst: Tm, snd: Tm)
    case CFst(tm: Tm)
    case CSnd(tm: Tm)

    override def toString: String = this match
      case Local(ix, _)               => s"'$ix"
      case Global(m, x, _)            => s"$m.$x"
      case Prim(p)                    => s"$p"
      case BoolLit(v)                 => s"$v"
      case IntLit(v)                  => s"$v"
      case Let(x, _, ty, v, b)        => s"(let '$x : $ty = $v; $b)"
      case LetRec(x, _, ty, v, b)     => s"(let rec '$x : $ty = $v; $b)"
      case Lam(x, _, ty, b)           => s"(\\('$x : $ty) => $b)"
      case App(fn, arg)               => s"($fn $arg)"
      case If(_, c, t, f)             => s"(if $c then $t else $f)"
      case Con(m, _, cx, _, _, Nil)   => s"$m.$cx"
      case Con(m, _, cx, _, _, args)  => s"($m.$cx ${args.mkString(" ")})"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"
      case Record(_, args)            => args.mkString("[", ", ", "]")
      case Select(_, s, i)            => s"$s.$i"
      case ReturnIO(ty, v)            => s"(returnIO $v)"
      case BindIO(x, _, ty, v, b)     => s"(bindIO '$x : $ty = $v; $b)"
      case CUnit                      => "()"
      case CPair(a, b)                => s"($a, $b)"
      case CFst(t)                    => s"(cfst $t)"
      case CSnd(t)                    => s"(csnd $t)"

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, args) = f.flattenApps
        (hd, args :+ a)
      case t => (t, Nil)

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
