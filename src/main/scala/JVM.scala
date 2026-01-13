import Common.*

object JVM:
  enum Ty:
    case Bool
    case Int
    case Data(name: Name)

    override def toString: String = this match
      case Bool    => "Bool"
      case Int     => "Int"
      case Data(x) => s"$x"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  type LocalName = Int

  final case class Constructor(
      name: Name,
      params: List[(Option[Name], Ty)]
  ):
    override def toString: String = params match
      case Nil => s"$name"
      case _ =>
        val ps = params
          .map((x, t) => s"(${x.getOrElse("_")} : $t)")
          .mkString(" ")
        s"$name $ps"

  enum Def:
    case Value(name: Name, ty: Ty, value: Tm)
    case Function(
        name: Name,
        params: List[(LocalName, Ty)],
        retty: Ty,
        body: Tm
    )
    case Data(name: Name, constructors: List[Constructor])

    override def toString: String = this match
      case Value(x, t, v) =>
        s"def $x : $t = $v"
      case Function(x, Nil, t, b) =>
        s"def $x () : $t = $b"
      case Function(x, ps, t, b) =>
        s"def $x ${ps.map((x, ty) => s"('$x : $ty)").mkString(" ")} : $t = $b"
      case Data(x, Nil) => s"data $x"
      case Data(x, cs)  => s"data $x = ${cs.mkString(" | ")}"

  enum Cases:
    case Ext(x: Name, ps: List[(LocalName, Ty, Int)], body: Tm, rest: Cases)
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

    case Con(dx: Name, cx: Name, ix: Int, args: List[Tm])
    case Case(dty: Name, scrut: Tm, cases: Cases)

    override def toString: String = this match
      case Local(ix, _)     => s"'$ix"
      case Global(x, Nil)   => s"$x"
      case Global(x, args)  => s"$x${args.mkString("(", ",", ")")}"
      case Prim(p, Nil)     => s"$p"
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
      case Jump(x, Nil)        => s"(jump '$x)"
      case Jump(x, args)       => s"(jump '$x${args.mkString("(", ",", ")")})"
      case Con(_, cx, _, Nil)  => s"$cx"
      case Con(_, cx, _, args) => s"($cx ${args.mkString(" ")})"
      case Case(_, s, Cases.Empty) => s"(match $s)"
      case Case(_, s, cs)          => s"(match $s { $cs })"

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
