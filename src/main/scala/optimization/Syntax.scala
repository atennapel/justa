package optimization

import common.Common.*

object Syntax:
  enum Ty:
    case TNative(name: Name, args: List[Ty] = Nil)

    override def toString: String = this match
      case TNative(x, Nil)  => s"$x"
      case TNative(x, args) => s"$x${args.mkString("(", ", ", ")")}"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = s"${ps.mkString("(", ", ", ")")} -> $rt"
    def arity: Int = ps.size
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)
    def apply(ps: List[Ty], rt: TDef): TDef = TDef(ps ++ rt.ps, rt.rt)

  enum Def[T]:
    case DDef(name: Name, ty: TDef, tm: T)

    override def toString: String = this match
      case DDef(x, ty, tm) => s"def $x : $ty = $tm"
  export Def.*

  enum LetEntry[C]:
    case LetGlobal(name: Name, args: List[Lvl])
    case LetApp(fn: Lvl, args: List[Lvl])
    case LetLam(ty: TDef, body: C)
    case LetRecLam(ty: TDef, body: C)
    case LetNative(name: Name, args: List[Lvl])

    override def toString: String = this match
      case LetGlobal(x, Nil)   => s"let = $x"
      case LetLam(ty, body)    => s"let : $ty = ($body)"
      case LetRecLam(ty, body) => s"let rec : $ty = ($body)"
      case LetGlobal(x, args) =>
        s"let = $x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case LetNative(x, args) =>
        s"let = $x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case LetApp(fn, args) =>
        s"let = '$fn${args.map(x => s"'$x").mkString("(", ", ", ")")}"
  export LetEntry.*

  final case class Tm[L](lets: List[L], ret: Lvl):
    override def toString: String = lets match
      case Nil  => s"'$ret"
      case lets => s"${lets.mkString("; ")}; '$ret"

  final case class NTm(tm: Tm[LetEntry[NTm]]):
    override def toString: String = tm.toString

  type CTmId = Int
  type Closure = (LvlSet, CTmId)
  type VLetEntry = LetEntry[Closure]
  type OTm = Tm[Option[VLetEntry]]
  type CTm = Tm[VLetEntry]
