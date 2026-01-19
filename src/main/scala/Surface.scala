import Common.*
import Common.Icit.*

object Surface:
  final case class Module(
      pos: PosInfo,
      name: Name,
      deps: Set[Name],
      imports: List[(PosInfo, PosInfo, Boolean, Name, Name, Option[Name])],
      moduleAliases: Map[Name, Name],
      defs: Defs
  ):
    override def toString: String =
      s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    inline def toList: List[Def] = defs

  final case class Constructor(
      pos: PosInfo,
      pub: Boolean,
      name: Name,
      params: List[(Bind, Ty)]
  ):
    override def toString: String =
      params match
        case Nil => s"${if pub then "" else "priv "}$name"
        case _ =>
          val ps = params
            .map((x, t) => s"($x : $t)")
            .mkString(" ")
          s"${if pub then "" else "priv "}$name $ps"

  enum Def:
    case Def0(pos: PosInfo, pub: Boolean, name: Name, ty: Option[Ty], value: Tm)
    case Def1(pos: PosInfo, pub: Boolean, name: Name, ty: Option[Ty], value: Tm)
    case Data(
        pos: PosInfo,
        pub: Boolean,
        name: Name,
        params: List[Name],
        cons: List[Constructor]
    )

    override def toString: String = this match
      case Def0(_, p, x, t, v) =>
        s"${if p then "public " else ""}def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case Def1(_, p, x, t, v) =>
        s"${if p then "pub " else ""}def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case Data(_, p, x, ps, cs) =>
        val css = cs.mkString(" | ")
        s"${if p then "pub " else ""}data $x ${ps.mkString(" ")} := $css"

  enum ArgInfo derives CanEqual:
    case Named(name: Name)
    case Icit(icit: Common.Icit)
  object ArgInfo:
    val Expl = Icit(Common.Icit.Expl)
    val Impl = Icit(Common.Icit.Impl)

  enum ProjType:
    case Named(name: Name)
    case Indexed(ix: Int)

    override def toString: String = this match
      case Named(x)    => x.toString
      case Indexed(ix) => ix.toString

  type Ty = Tm
  enum Tm:
    case Var(_pos: PosInfo, name: Name)
    case Prim(_pos: PosInfo, prim: Primitive)
    case IntLit(_pos: PosInfo, value: Int)

    case Let0(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case LetRec(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)

    case Proj(_pos: PosInfo, tm: Tm, proj: ProjType)

    case Pi(_pos: PosInfo, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(_pos: PosInfo, name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(_pos: PosInfo, fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(_pos: PosInfo, ty: Ty)
    case Quote(_pos: PosInfo, tm: Tm)
    case Splice(_pos: PosInfo, tm: Tm)

    case If(_pos: PosInfo, cond: Tm, ifTrue: Tm, ifFalse: Tm)
    case Match(
        _pos: PosInfo,
        scrut: Option[Tm],
        cases: List[(PosInfo, Bind, List[Bind], Tm)]
    )

    case UnitLit(_pos: PosInfo)
    case EmptyRecord(_pos: PosInfo)
    case RecordTy(_pos: PosInfo, fields: AssocBind[Ty])
    case RecordCon1(_pos: PosInfo, fields: Assoc[Tm])
    case RecordCon0(_pos: PosInfo, fields: Assoc[Tm])
    case Tuple(_pos: PosInfo, fields: List[Tm])

    case Hole(_pos: PosInfo, name: Option[Name])

    def pos: PosInfo = this match
      case Var(_pos, _)             => _pos
      case Prim(_pos, _)            => _pos
      case IntLit(_pos, _)          => _pos
      case Proj(_pos, _, _)         => _pos
      case Let0(_pos, _, _, _, _)   => _pos
      case Let1(_pos, _, _, _, _)   => _pos
      case LetRec(_pos, _, _, _, _) => _pos
      case Pi(_pos, _, _, _, _)     => _pos
      case Lam(_pos, _, _, _, _)    => _pos
      case App(_pos, _, _, _)       => _pos
      case Lift(_pos, _)            => _pos
      case Quote(_pos, _)           => _pos
      case Splice(_pos, _)          => _pos
      case If(_pos, _, _, _)        => _pos
      case Match(_pos, _, _)        => _pos
      case Hole(_pos, _)            => _pos
      case UnitLit(_pos)            => _pos
      case EmptyRecord(_pos)        => _pos
      case RecordTy(_pos, _)        => _pos
      case RecordCon1(_pos, _)      => _pos
      case RecordCon0(_pos, _)      => _pos
      case Tuple(_pos, _)           => _pos

    def splitProjs: (Tm, List[(PosInfo, ProjType)]) = this match
      case Proj(pos, tm, proj) =>
        val (hd, tl) = tm.splitProjs
        (hd, tl :+ (pos, proj))
      case tm => (tm, Nil)

    override def toString: String = this match
      case Var(_, x)     => s"$x"
      case Prim(_, p)    => s"$p"
      case IntLit(_, v)  => s"$v"
      case Proj(_, t, p) => s"$t.$p"
      case Let0(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Let1(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} = $v; $b)"
      case LetRec(_, x, ty, v, b) =>
        s"(let rec $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Pi(_, Bind.DontBind, Expl, ty, b) => s"($ty -> $b)"
      case Pi(_, x, i, ty, b) => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(_, x, ArgInfo.Icit(Expl), None, b) => s"(\\$x => $b)"
      case Lam(_, x, ArgInfo.Icit(i), ty, b) =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")} => $b)"
      case Lam(_, x, ArgInfo.Named(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")} => $b)"
      case App(_, fn, arg, ArgInfo.Icit(Expl)) => s"($fn $arg)"
      case App(_, fn, arg, ArgInfo.Icit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(_, fn, arg, ArgInfo.Named(x)) =>
        s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(_, ty)            => s"^$ty"
      case Quote(_, tm)           => s"`$tm"
      case Splice(_, tm)          => s"$$$tm"
      case If(_, c, t, f)         => s"(if $c then $t else $f)"
      case Hole(_, None)          => s"_"
      case Hole(_, Some(x))       => s"_$x"
      case Match(_, None, Nil)    => s"(match {})"
      case Match(_, Some(s), Nil) => s"(match $s {})"
      case Match(_, s, cs) =>
        inline def show(c: (PosInfo, Bind, List[Bind], Tm)) =
          c._3 match
            case Nil => s"${c._2} => ${c._4}"
            case ps  => s"${c._2} ${ps.mkString(" ")} => ${c._4}"
        s"(match ${s.map(t => s"$t ").getOrElse("")}{ ${cs.map(show).mkString(" | ")} })"
      case UnitLit(_)     => "()"
      case EmptyRecord(_) => "[]"
      case RecordTy(_, fs) =>
        fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case RecordCon1(_, fs) =>
        fs.map((x, t) => s"$x = $t").mkString("[", ", ", "]")
      case RecordCon0(_, fs) =>
        fs.map((x, t) => s"$x := $t").mkString("[", ", ", "]")
      case Tuple(_, fs) => fs.mkString("[", ", ", "]")
