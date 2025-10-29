package surface

import common.Common
import common.Common.*

object Surface:
  final case class Module(
      pos: PosInfo,
      name: Name,
      deps: Set[Name],
      imports: Map[Name, (PosInfo, PosInfo, Name, Option[Name])],
      moduleAliases: Map[Name, Name],
      defs: Defs
  ):
    override def toString: String =
      s"module $name\n$defs"

  final case class Defs(defs: Seq[Def]):
    override def toString: String = defs.mkString("\n")
    def toSeq: Seq[Def] = defs

  enum Def:
    case D0(
        pos: PosInfo,
        name: Name,
        ty: Option[Tm],
        value: Tm
    )
    case D1(
        pos: PosInfo,
        name: Name,
        ty: Option[Tm],
        value: Tm
    )
    override def toString: String = this match
      case D0(_, x, t, v) =>
        s"let $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case D1(_, x, t, v) =>
        s"let $x${t.map(t => s" : $t").getOrElse("")} = $v"

  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: Common.Icit)
  object ArgInfo:
    val Expl = ArgInfo.Icit(Common.Icit.Expl)
    val Impl = ArgInfo.Icit(Common.Icit.Impl)

  enum Tm:
    case Var(_pos: PosInfo, name: Name)

    case Let0(_pos: PosInfo, name: Name, ty: Option[Tm], value: Tm, body: Tm)
    case Let1(_pos: PosInfo, name: Name, ty: Option[Tm], value: Tm, body: Tm)

    case Pi(_pos: PosInfo, name: Bind, icit: Icit, ty: Tm, body: Tm)
    case Lam(_pos: PosInfo, name: Bind, icit: ArgInfo, ty: Option[Tm], body: Tm)
    case App(_pos: PosInfo, fn: Tm, arg: Tm, info: ArgInfo)

    case Hole(_pos: PosInfo)

    override def toString(): String = this match
      case Var(_, x)                 => s"$x"
      case Let0(_, x, None, v, b)    => s"(let $x := $v; $b)"
      case Let0(_, x, Some(t), v, b) => s"(let $x : $t := $v; $b)"
      case Let1(_, x, None, v, b)    => s"(let $x = $v; $b)"
      case Let1(_, x, Some(t), v, b) => s"(let $x : $t = $v; $b)"

      case Pi(_, x, i, ty, b) => s"(${i.wrap(s"$x : $ty")} -> $b)"

      case Lam(_, x, ArgInfo.Icit(Common.Icit.Expl), None, b) => s"(\\$x => $b)"
      case Lam(_, x, ArgInfo.Icit(Common.Icit.Impl), None, b) =>
        s"(\\{$x} => $b)"
      case Lam(_, x, ArgInfo.Icit(i), Some(t), b) =>
        s"(\\${i.wrap(s"$x : $t")} => $b)"
      case Lam(_, x, ArgInfo.Named(y), None, b)    => s"(\\{$x = $y}) => $b"
      case Lam(_, x, ArgInfo.Named(y), Some(t), b) =>
        s"(\\{$x : $t = $y}) => $b"

      case App(_, f, a, ArgInfo.Icit(Common.Icit.Expl)) => s"($f $a)"
      case App(_, f, a, ArgInfo.Icit(Common.Icit.Impl)) => s"($f {$a})"
      case App(_, f, a, ArgInfo.Named(x))               => s"($f {$x = $a})"

      case Hole(_) => "_"

    def pos: PosInfo = this match
      case Var(p, _)           => p
      case Let0(p, _, _, _, _) => p
      case Let1(p, _, _, _, _) => p
      case Pi(p, _, _, _, _)   => p
      case Lam(p, _, _, _, _)  => p
      case App(p, _, _, _)     => p
      case Hole(p)             => p
