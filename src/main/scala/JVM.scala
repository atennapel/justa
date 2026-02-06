import Common.*

import scala.collection.mutable

object JVM:
  val RecordConName = Name("Mk")

  enum Ty derives CanEqual:
    case Bool
    case Int
    case Data(mod: Name, name: Name)

    override def toString: String = this match
      case Bool       => "Bool"
      case Int        => "Int"
      case Data(m, x) => s"$m.$x"

  final case class Module(name: Name, defs: Defs):
    override def toString: String = s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  type LocalName = Int

  enum Access derives CanEqual:
    case Pub
    case Priv
    case Synth

    override def toString: String = this match
      case Pub   => "pub"
      case Priv  => "priv"
      case Synth => "synth"

  final case class Constructor(
      acc: Access,
      name: Name,
      params: List[(Option[Name], Ty)]
  ):
    override def toString: String = params match
      case Nil => s"$acc $name"
      case _ =>
        val ps = params
          .map((x, t) => s"(${x.getOrElse("_")} : $t)")
          .mkString(" ")
        s"$acc $name $ps"

  enum Def:
    case Value(acc: Access, _name: Name, ty: Ty, value: Tm)
    case Function(
        acc: Access,
        _name: Name,
        params: List[(LocalName, Ty)],
        retty: Ty,
        body: Tm
    )
    case Data(acc: Access, _name: Name, constructors: List[Constructor])

    override def toString: String = this match
      case Value(acc, x, t, v) =>
        s"$acc def $x : $t = $v"
      case Function(acc, x, Nil, t, b) =>
        s"$acc def $x () : $t = $b"
      case Function(acc, x, ps, t, b) =>
        s"$acc def $x ${ps.map((x, ty) => s"('$x : $ty)").mkString(" ")} : $t = $b"
      case Data(acc, x, Nil) =>
        s"$acc data $x"
      case Data(acc, x, cs) =>
        s"$acc data $x = ${cs.mkString(" | ")}"

    def isData: Boolean = this match
      case Data(_, _, _) => true
      case _             => false

    def isSynth: Boolean = this match
      case Value(acc, _, _, _)       => acc == Access.Synth
      case Function(acc, _, _, _, _) => acc == Access.Synth
      case Data(acc, _, _)           => acc == Access.Synth

    def name: Name = this match
      case Value(_, x, _, _)       => x
      case Function(_, x, _, _, _) => x
      case Data(_, x, _)           => x

    def globals(res: mutable.Set[(Name, Name)]): Unit =
      this match
        case Value(_, _, _, v)       => v.globals(res)
        case Function(_, _, _, _, v) => v.globals(res)
        case Data(_, _, _)           => ()

  enum Cases derives CanEqual:
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

    def globals(res: mutable.Set[(Name, Name)]): Unit =
      this match
        case Cases.Ext(_, _, b, r) => b.globals(res); r.globals(res)
        case Cases.Otherwise(b)    => b.globals(res)
        case Cases.Empty           => ()

  enum Tm derives CanEqual:
    case Local(ix: LocalName, ty: Ty)
    case Global(mod: Name, name: Name)
    case GlobalApp(mod: Name, name: Name, args: List[Tm])
    case Prim(prim: RuntimePrimitive, args: List[Tm])
    case BoolLit(value: Boolean)
    case IntLit(value: Int)
    case Let(name: LocalName, ty: Ty, value: Tm, body: Tm)
    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Join(
        blocks: List[(LocalName, List[(LocalName, Ty)], Tm)],
        body: Tm
    )
    case Jump(name: LocalName, args: List[Tm])

    case Con(mod: Name, dx: Name, cx: Name, ix: Int, args: List[Tm])
    case Case(mod: Name, dty: Name, scrut: Tm, cases: Cases)
    case Select(scrut: Tm, ix: Int)

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
      case Join(bs, b) =>
        val s = bs
          .map((x, ps, v) =>
            s"let '$x ${ps.map((x, t) => s"('$x : $t)").mkString(" ")} = $v"
          )
          .mkString("; ")
        s"(join $s; $b)"
      case Jump(x, Nil)          => s"(jump '$x)"
      case Jump(x, args)         => s"(jump '$x${args.mkString("(", ",", ")")})"
      case Con(m, _, cx, _, Nil) => s"$m.$cx"
      case Con(m, _, cx, _, args)     => s"($m.$cx ${args.mkString(" ")})"
      case Case(_, _, s, Cases.Empty) => s"(match $s)"
      case Case(_, _, s, cs)          => s"(match $s { $cs })"
      case Select(s, i)               => s"$s.$i"

    def globals(res: mutable.Set[(Name, Name)]): Unit =
      this match
        case Local(_, _) => ()
        case BoolLit(_)  => ()
        case IntLit(_)   => ()

        case Global(m, x) => res += ((m, x))
        case GlobalApp(m, x, args) =>
          res += ((m, x))
          args.foreach(_.globals(res))
        case Con(_, _, _, _, args) => args.foreach(_.globals(res))
        case Case(_, _, s, cs) =>
          def go(cs: Cases): Unit =
            cs match
              case Cases.Ext(_, _, b, r) => b.globals(res); go(r)
              case Cases.Otherwise(b)    => b.globals(res)
              case Cases.Empty           => ()
          s.globals(res); go(cs)

        case Prim(_, args)   => args.foreach(_.globals(res))
        case Let(_, _, v, b) => v.globals(res); b.globals(res)
        case If(c, t, f)     => c.globals(res); t.globals(res); f.globals(res)
        case Join(bs, b) =>
          bs.foreach((_, _, v) => v.globals(res)); b.globals(res)
        case Jump(_, args) => args.foreach(_.globals(res))
        case Select(s, _)  => s.globals(res)

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
