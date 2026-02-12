import Common.*

object IR:
  enum VTy derives CanEqual:
    case Void
    case Bool
    case Int
    case Data(mod: Name, name: Name, args: List[VTy])
    case Record(fields: AssocBind[VTy])
    case Class(fullyQualifiedName: String)
    case Array(ty: VTy)

    override def toString: String = this match
      case Void             => "Void"
      case Bool             => "Bool"
      case Int              => "Int"
      case Data(m, x, Nil)  => s"$m.$x"
      case Data(m, x, args) => s"($m.$x ${args.mkString(" ")})"
      case Record(fs) => fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case Class(x)   => s"$x"
      case Array(ty)  => s"(Array $ty)"

  object VTy:
    val String = VTy.Class("java.lang.String")

  enum CTy derives CanEqual:
    case Fun(pty: VTy, rty: CTy)
    case IO(ty: VTy)
    case Rec(fields: List[(Option[Name], CTy)])
    case Val(ty: VTy)

    def vty: VTy = this match
      case Val(ty) => ty
      case _       => impossible()

    def retty: CTy = this match
      case Fun(_, rty) => rty
      case _           => impossible()

    def isVal: Boolean = this match
      case Val(_) => true
      case _      => false

    override def toString: String = this match
      case Fun(pty, rty) => s"($pty -> $rty)"
      case IO(ty)        => s"(IO $ty)"
      case Rec(fs) =>
        fs.map((x, t) => x.map(x => s"$x : $t").getOrElse(s"$t"))
          .mkString("[", ", ", "]")
      case Val(ty) => s"$ty"

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
    case StringLit(value: String)

    case Let(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)
    case LetRec(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)

    case Lam(name: LocalName, usage: Int, ty: VTy, body: Tm)
    case App(fn: Tm, arg: Tm, argty: VTy)

    case If(rty: CTy, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Con(
        mod: Name,
        dx: Name,
        cx: Name,
        ix: Int,
        ty: VTy,
        args: List[(Tm, VTy)]
    )
    case Case(rty: CTy, dty: VTy, scrut: Tm, cases: Cases)
    case Record(dty: VTy, args: List[Tm])
    case Select(rty: VTy, scrutty: VTy, scrut: Tm, i: Int)

    case ReturnIO(ty: VTy, value: Tm)
    case BindIO(name: LocalName, usage: Int, ty: VTy, value: Tm, body: Tm)

    case CRecord(fields: List[Tm])
    case CSelect(scrut: Tm, i: Int)

    case Unsafe(rty: VTy, io: Boolean, label: String, args: List[(Tm, VTy)])

    override def toString: String = this match
      case Local(ix, _)             => s"'$ix"
      case Global(m, x, _)          => s"$m.$x"
      case Prim(p)                  => s"$p"
      case BoolLit(v)               => s"$v"
      case IntLit(v)                => s"$v"
      case StringLit(v)             => s"\"$v\""
      case Let(x, _, ty, v, b)      => s"(let '$x : $ty = $v; $b)"
      case LetRec(x, _, ty, v, b)   => s"(let rec '$x : $ty = $v; $b)"
      case Lam(x, _, ty, b)         => s"(\\('$x : $ty) => $b)"
      case App(fn, arg, _)          => s"($fn $arg)"
      case If(_, c, t, f)           => s"(if $c then $t else $f)"
      case Con(m, _, cx, _, _, Nil) => s"$m.$cx"
      case Con(m, _, cx, _, _, args) =>
        s"($m.$cx ${args.map((a, _) => a).mkString(" ")})"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"
      case Record(_, args)            => args.mkString("[", ", ", "]")
      case Select(_, _, s, i)         => s"$s.$i"
      case ReturnIO(ty, v)            => s"(returnIO $v)"
      case BindIO(x, _, ty, v, b)     => s"(bindIO '$x : $ty = $v; $b)"
      case CRecord(fs)                => fs.mkString("[", ", ", "]")
      case CSelect(s, i)              => s"$s.$i"
      case Unsafe(_, io, l, Nil) => s"(unsafe${if io then "IO" else ""} $l)"
      case Unsafe(_, io, l, args) =>
        s"(unsafe${if io then "IO" else ""} $l ${args.map(_._1).mkString(" ")})"

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a, _) =>
        val (hd, args) = f.flattenApps
        (hd, args :+ a)
      case t => (t, Nil)

    def flattenCompElims: (Tm, List[Either[Int, Tm]]) = this match
      case App(f, a, _) =>
        val (hd, args) = f.flattenCompElims
        (hd, args :+ Right(a))
      case CSelect(s, i) =>
        val (hd, args) = s.flattenCompElims
        (hd, args :+ Left(i))
      case t => (t, Nil)

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
