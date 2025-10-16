package common

object Common:
  inline def impossible(): Nothing =
    throw new RuntimeException("impossible")

  type Name = String
  type Bind = String

  // icit
  enum Icit:
    case Expl
    case Impl

    def wrap(x: Any): String = this match
      case Expl => s"($x)"
      case Impl => s"{$x}"
