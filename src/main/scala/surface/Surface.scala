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
