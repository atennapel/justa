import Common.*

object IR:
  enum VTy:
    case Bool
    case Int
    case Data(name: Name)

    override def toString: String = this match
      case Bool    => "bool"
      case Int     => "int"
      case Data(x) => s"$x"

  final case class CTy(params: List[VTy], ret: VTy):
    def head: VTy = params.head
    def tail: CTy = CTy(params.tail, ret)
    def drop(n: Int): CTy = CTy(params.drop(n), ret)
    override def toString: String = s"${params.mkString("(", ",", ")")} -> $ret"
  object CTy:
    def apply(ret: VTy): CTy = CTy(Nil, ret)
    def apply(param: VTy, ret: VTy): CTy = CTy(List(param), ret)
    def apply(param: VTy, ret: CTy): CTy = CTy(param :: ret.params, ret.ret)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Constructor(
      name: Name,
      params: List[(Option[Name], VTy)]
  ):
    override def toString: String = params match
      case Nil => s"$name"
      case _ =>
        val ps = params
          .map((x, t) => s"($x : $t)")
          .mkString(" ")
        s"$name $ps"

  enum Def:
    case Value(name: Name, ty: CTy, value: Tm)
    case Data(name: Name, constructors: List[Constructor])

    override def toString: String = this match
      case Value(x, ty, v) => s"def $x : $ty = $v"
      case Data(x, Nil)    => s"data $x"
      case Data(x, cs)     => s"data $x = ${cs.mkString(" | ")}"

  enum Cases:
    case Ext(x: Name, ps: List[(LocalName, VTy, Int)], body: Tm, rest: Cases)
    case Otherwise(body: Tm)
    case Empty

    override def toString: String =
      this match
        case Cases.Ext(x, Nil, b, r) => s"$x => $b | $r"
        case Cases.Ext(x, ps, b, r) =>
          s"$x ${ps.map((x, _, _) => s"'$x").mkString(" ")} => $b | $r"
        case Cases.Otherwise(b) => s"_ => $b"
        case Cases.Empty        => s""

  type LocalName = Int
  enum Tm:
    case Local(ix: LocalName, ty: CTy)
    case Global(name: Name)
    case Prim(prim: RuntimePrimitive)
    case BoolLit(value: Boolean)
    case IntLit(value: Int)

    case Let(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)
    case LetRec(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)

    case Lam(name: LocalName, usage: Int, ty: VTy, body: Tm)
    case App(fn: Tm, arg: Tm)

    case If(rty: CTy, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Con(dx: Name, cx: Name, ix: Int, args: List[Tm])
    case Case(rty: CTy, dty: Name, scrut: Tm, cases: Cases)

    override def toString: String = this match
      case Local(ix, _)               => s"'$ix"
      case Global(x)                  => s"$x"
      case Prim(p)                    => s"$p"
      case BoolLit(v)                 => s"$v"
      case IntLit(v)                  => s"$v"
      case Let(x, _, ty, v, b)        => s"(let '$x : $ty = $v; $b)"
      case LetRec(x, _, ty, v, b)     => s"(let rec '$x : $ty = $v; $b)"
      case Lam(x, _, ty, b)           => s"(\\('$x : $ty) => $b)"
      case App(fn, arg)               => s"($fn $arg)"
      case If(_, c, t, f)             => s"(if $c then $t else $f)"
      case Con(_, cx, _, Nil)         => s"$cx"
      case Con(_, cx, _, args)        => s"($cx ${args.mkString(" ")})"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, args) = f.flattenApps
        (hd, args ++ List(a))
      case t => (t, Nil)

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
