import Common.*
import Common.Icit.*

object Surface:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case Def0(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)
    case Def1(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)

    override def toString: String = this match
      case Def0(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case Def1(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} = $v"

  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: Common.Icit)

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Prim(prim: Primitive)
    case Let0(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case LetRec(name: Name, ty: Option[Ty], value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    override def toString: String = this match
      case Var(x)  => s"$x"
      case Prim(p) => s"$p"
      case Let0(x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Let1(x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} = $v; $b)"
      case LetRec(x, ty, v, b) =>
        s"(let rec $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Pi(Bind.DontBind, Expl, ty, b) => s"($ty -> $b)"
      case Pi(x, i, ty, b)                => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, ArgInfo.Icit(Expl), None, b) => s"(\\$x => $b)"
      case Lam(x, ArgInfo.Icit(i), ty, b) =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")} => $b)"
      case Lam(x, ArgInfo.Named(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")} => $b)"
      case App(fn, arg, ArgInfo.Icit(Expl)) => s"($fn $arg)"
      case App(fn, arg, ArgInfo.Icit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(fn, arg, ArgInfo.Named(x)) => s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(ty)                       => s"^$ty"
      case Quote(tm)                      => s"`$tm"
      case Splice(tm)                     => s"$$$tm"
      case Hole(None)                     => s"_"
      case Hole(Some(x))                  => s"_$x"
      case Pos(_, tm)                     => s"$tm"
