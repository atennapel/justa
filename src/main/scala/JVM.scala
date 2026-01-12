import Common.*

object JVM:
  enum Ty:
    case Bool
    case Int

    override def toString: String = this match
      case Bool => "bool"
      case Int  => "int"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  type LocalName = Int

  enum Def:
    case Value(name: Name, ty: Ty, value: Tm)
    case Function(
        name: Name,
        params: List[(LocalName, Ty)],
        retty: Ty,
        body: Tm
    )

    override def toString: String = this match
      case Value(x, t, v) =>
        s"def $x : $t = $v"
      case Function(x, Nil, t, b) =>
        s"def $x () : $t = $b"
      case Function(x, ps, t, b) =>
        s"def $x ${ps.map((x, ty) => s"('$x : $ty)").mkString(" ")} : $t = $b"

  enum Tm:
    case Local(ix: LocalName, ty: Ty)
    case Global(name: Name, args: List[Tm])
    case Prim(prim: RuntimePrimitive, args: List[Tm])
    case BoolLit(value: Boolean)
    case IntLit(value: Int)
    case Let(name: LocalName, ty: Ty, value: Tm, body: Tm)
    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Join(
        name: LocalName,
        params: List[(LocalName, Ty)],
        value: Tm,
        body: Tm
    )
    case JoinRec(
        name: LocalName,
        params: List[(LocalName, Ty)],
        value: Tm,
        body: Tm
    )
    case Jump(name: LocalName, args: List[Tm])

    override def toString: String = this match
      case Local(ix, _)     => s"'$ix"
      case Global(x, args)  => s"$x${args.mkString("(", ",", ")")}"
      case Prim(p, args)    => s"$p${args.mkString("(", ",", ")")}"
      case BoolLit(v)       => s"$v"
      case IntLit(v)        => s"$v"
      case Let(x, ty, v, b) => s"(let '$x : $ty = $v; $b)"
      case If(c, t, f)      => s"(if $c then $t else $f)"
      case Join(x, Nil, v, b) =>
        s"(join '$x = $v; $b"
      case Join(x, ps, v, b) =>
        s"(join '$x ${ps.map((x, t) => s"('$x : $t)").mkString(" ")} = $v; $b"
      case JoinRec(x, Nil, v, b) =>
        s"(join rec '$x = $v; $b"
      case JoinRec(x, ps, v, b) =>
        s"(join rec '$x ${ps.map((x, t) => s"('$x : $t)").mkString(" ")} = $v; $b"
      case Jump(x, Nil)  => s"(jump '$x)"
      case Jump(x, args) => s"(jump '$x${args.mkString("(", ",", ")")})"

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
