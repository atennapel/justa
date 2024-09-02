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
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)
    def apply(ps: List[Ty], rt: TDef): TDef = TDef(ps ++ rt.ps, rt.rt)

  enum Def:
    case DDef(name: Name, ty: TDef, tm: Tm)

    override def toString: String = this match
      case DDef(x, ty, tm) => s"def $x : $ty = $tm"
  export Def.*

  enum LetEntry:
    case LetGlobal(name: Name, args: List[Lvl])
    case LetApp(fn: Lvl, args: List[Lvl])
    case LetLam(ty: TDef, body: Tm)
    case LetNative(name: Name, args: List[Lvl])

    override def toString: String = this match
      case LetGlobal(x, Nil) => s"let = $x"
      case LetLam(ty, body)  => s"let : $ty = ($body)"
      case LetGlobal(x, args) =>
        s"let = $x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case LetNative(x, args) =>
        s"let = $x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case LetApp(fn, args) =>
        s"let = '$fn${args.map(x => s"'$x").mkString("(", ", ", ")")}"
  export LetEntry.*

  final case class Tm(lets: List[LetEntry], ret: Lvl):
    override def toString: String = lets match
      case Nil  => s"'$ret"
      case lets => s"${lets.mkString("; ")}; '$ret"
  export Tm.*
