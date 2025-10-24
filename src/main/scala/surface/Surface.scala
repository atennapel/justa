package surface

import common.Common
import common.Common.*

object Surface:
  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: Common.Icit)
  object ArgInfo:
    val Expl = ArgInfo.Icit(Common.Icit.Expl)
    val Impl = ArgInfo.Icit(Common.Icit.Impl)

  enum Tm:
    case Var(name: Name)

    case Let(name: Name, ty: Option[Tm], value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Tm, body: Tm)
    case Lam(name: Bind, icit: ArgInfo, ty: Option[Tm], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Hole

    override def toString(): String = this match
      case Var(x)                => s"$x"
      case Let(x, None, v, b)    => s"(let $x = $v; $b)"
      case Let(x, Some(t), v, b) => s"(let $x : $t = $v; $b)"

      case Pi(x, i, ty, b) => s"(${i.wrap(s"$x : $ty")} -> $b)"

      case Lam(x, ArgInfo.Icit(Common.Icit.Expl), None, b) => s"(\\$x => $b)"
      case Lam(x, ArgInfo.Icit(Common.Icit.Impl), None, b) => s"(\\{$x} => $b)"
      case Lam(x, ArgInfo.Icit(i), Some(t), b)             =>
        s"(\\${i.wrap(s"$x : $t")} => $b)"
      case Lam(x, ArgInfo.Named(y), None, b)    => s"(\\{$x = $y}) => $b"
      case Lam(x, ArgInfo.Named(y), Some(t), b) => s"(\\{$x : $t = $y}) => $b"

      case App(f, a, ArgInfo.Icit(Common.Icit.Expl)) => s"($f $a)"
      case App(f, a, ArgInfo.Icit(Common.Icit.Impl)) => s"($f {$a})"
      case App(f, a, ArgInfo.Named(x))               => s"($f {$x = $a})"

      case Hole => "_"
