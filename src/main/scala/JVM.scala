import Common.*

object JVM:
  enum Ty:
    case Bool
    case Int
    case Data(mod: Name, name: Name)

    override def toString: String = this match
      case Bool       => "Bool"
      case Int        => "Int"
      case Data(m, x) => s"$m.$x"

  final case class Module(name: Name, defs: Defs):
    override def toString: String = s"module $name\n$defs"

  final case class Defs(defs: Seq[Def]):
    override def toString: String = defs.mkString("\n")
    def toSeq: Seq[Def] = defs

  type LocalName = Int

  final case class Constructor(
      name: Name,
      params: Seq[(Option[Name], Ty)]
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
        params: Seq[(LocalName, Ty)],
        retty: Ty,
        body: Tm
    )
    case Data(name: Name, constructors: Seq[Constructor])

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
    case Ext(x: Name, ps: Seq[(LocalName, Ty, Int)], body: Tm, rest: Cases)
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
    case Global(mod: Name, name: Name)
    case GlobalApp(mod: Name, name: Name, args: Seq[Tm])
    case Prim(prim: RuntimePrimitive, args: Seq[Tm])
    case BoolLit(value: Boolean)
    case IntLit(value: Int)
    case Let(name: LocalName, ty: Ty, value: Tm, body: Tm)
    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Join(
        name: LocalName,
        params: Seq[(LocalName, Ty)],
        value: Tm,
        body: Tm
    )
    case JoinRec(
        name: LocalName,
        params: Seq[(LocalName, Ty)],
        value: Tm,
        body: Tm
    )
    case Jump(name: LocalName, args: Seq[Tm])

    case Con(mod: Name, dx: Name, cx: Name, ix: Int, args: Seq[Tm])
    case Case(mod: Name, dty: Name, scrut: Tm, cases: Cases)

    override def toString: String = this match
      case Local(ix, _)          => s"'$ix"
      case Global(m, x)          => s"$m.$x"
      case GlobalApp(m, x, args) => s"$m.$x${args.mkString("(", ",", ")")}"
      case Prim(p, Nil)          => s"$p"
      case Prim(p, args)         => s"$p${args.mkString("(", ",", ")")}"
      case BoolLit(v)            => s"$v"
      case IntLit(v)             => s"$v"
      case Let(x, ty, v, b)      => s"(let '$x : $ty = $v; $b)"
      case If(c, t, f)           => s"(if $c then $t else $f)"
      case Join(x, Nil, v, b) =>
        s"(join '$x = $v; $b"
      case Join(x, ps, v, b) =>
        s"(join '$x ${ps.map((x, t) => s"('$x : $t)").mkString(" ")} = $v; $b"
      case JoinRec(x, Nil, v, b) =>
        s"(join rec '$x = $v; $b"
      case JoinRec(x, ps, v, b) =>
        s"(join rec '$x ${ps.map((x, t) => s"('$x : $t)").mkString(" ")} = $v; $b"
      case Jump(x, Nil)          => s"(jump '$x)"
      case Jump(x, args)         => s"(jump '$x${args.mkString("(", ",", ")")})"
      case Con(m, _, cx, _, Nil) => s"$m.$cx"
      case Con(m, _, cx, _, args)     => s"($m.$cx ${args.mkString(" ")})"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
