import Common.*
import Common.Icit.*

object Surface:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Constructor(
      pos: PosInfo,
      name: Name,
      params: List[(Bind, Ty)]
  ):
    override def toString: String =
      params match
        case Nil => s"$name"
        case _ =>
          val ps = params
            .map((x, t) => s"($x : $t)")
            .mkString(" ")
          s"$name $ps"

  enum Def:
    case Def0(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)
    case Def1(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)
    case Data(
        pos: PosInfo,
        name: Name,
        params: List[Name],
        cons: List[Constructor]
    )

    override def toString: String = this match
      case Def0(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case Def1(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case Data(_, x, ps, cs) =>
        val css = cs.mkString(" | ")
        s"data $x ${ps.mkString(" ")} := $css"

  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: Common.Icit)

  type Ty = Tm
  enum Tm:
    case Var(_pos: PosInfo, name: Name)
    case Prim(_pos: PosInfo, prim: Primitive)
    case IntLit(_pos: PosInfo, value: Int)
    case Let0(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case LetRec(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)

    case Pi(_pos: PosInfo, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(_pos: PosInfo, name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(_pos: PosInfo, fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(_pos: PosInfo, ty: Ty)
    case Quote(_pos: PosInfo, tm: Tm)
    case Splice(_pos: PosInfo, tm: Tm)

    case If(_pos: PosInfo, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case Hole(_pos: PosInfo, name: Option[Name])

    def pos: PosInfo = this match
      case Var(_pos, _)             => _pos
      case Prim(_pos, _)            => _pos
      case IntLit(_pos, _)          => _pos
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
      case Hole(_pos, _)            => _pos

    override def toString: String = this match
      case Var(_, x)    => s"$x"
      case Prim(_, p)   => s"$p"
      case IntLit(_, v) => s"$v"
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
      case Lift(_, ty)      => s"^$ty"
      case Quote(_, tm)     => s"`$tm"
      case Splice(_, tm)    => s"$$$tm"
      case If(_, c, t, f)   => s"(if $c then $t else $f)"
      case Hole(_, None)    => s"_"
      case Hole(_, Some(x)) => s"_$x"
