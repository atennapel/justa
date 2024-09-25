package compilation

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TBool
    case TList(ty: Ty)

    override def toString: String = this match
      case TNat     => "Nat"
      case TBool    => "Bool"
      case TList(t) => s"List($t)"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = s"${ps.mkString("(", ", ", ")")} -> $rt"
    def arity: Int = ps.size
    def ty: Ty = if ps.isEmpty then rt else impossible()
    def drop(n: Int): TDef = TDef(ps.drop(n), rt)
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)
    def apply(ps: List[Ty], rt: TDef): TDef = TDef(ps ++ rt.ps, rt.rt)
