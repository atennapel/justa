package compilation

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TBool

    override def toString: String = this match
      case TNat  => "Nat"
      case TBool => "Bool"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = s"${ps.mkString("(", ", ", ")")} -> $rt"
    def arity: Int = ps.size
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)
    def apply(ps: List[Ty], rt: TDef): TDef = TDef(ps ++ rt.ps, rt.rt)

  enum Def:
    case DDef(name: Name, ty: TDef, tm: Tm)

    override def toString: String = this match
      case DDef(x, ty, tm) => s"def $x : $ty = $tm"
  export Def.*

  enum Tm:
    case Var(lvl: Lvl)
    case Global(name: Name, args: List[Tm] = Nil)
    case Let(value: Tm, body: Tm)

    case Join(value: Tm, body: Tm)
    case JoinRec(value: Tm, body: Tm)
    case Jump(lvl: Lvl, args: List[Tm] = Nil)

    case True
    case False
    case NatZ
    case NatS(pred: Tm)

    override def toString: String = this match
      case Var(lvl)        => s"'$lvl"
      case Global(x, Nil)  => s"$x"
      case Global(x, args) => s"$x${args.mkString("(", ", ", ")")}"
      case Let(v, b)       => s"(let $v; $b)"
      case Join(v, b)      => s"(join $v; $b)"
      case JoinRec(v, b)   => s"(join rec $v; $b)"
      case Jump(lvl, args) => s"'$lvl${args.mkString("(", ", ", ")")}"
      case True            => "True"
      case False           => "False"
      case NatZ            => "Z"
      case NatS(pred)      => s"S($pred)"
  export Tm.*
