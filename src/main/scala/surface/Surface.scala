package surface

import common.Common
import common.Common.*

object Surface:
  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: Common.Icit)

  enum Tm:
    case Var(name: Name)

    case Let(name: Name, ty: Option[Tm], value: Tm, body: Tm)

    case Pi(name: Bind, icit: Icit, ty: Tm, body: Tm)
    case Lam(name: Bind, icit: ArgInfo, ty: Option[Tm], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)
