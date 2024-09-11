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
    def ty: Ty = if ps.isEmpty then rt else impossible()
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
      case LetLam(ty, body)    => s"let : $ty = ($body)"
      case LetRecLam(ty, body) => s"let rec : $ty = ($body)"
      case LetGlobal(x, Nil)   => s"let = $x"
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

  type LvlBag = Map[Lvl, (Int, TDef)]

  def insertLvlBag(l: Lvl, ty: TDef, a: LvlBag): LvlBag =
    a.get(l) match
      case None         => a + (l -> (1, ty))
      case Some((n, _)) => (a - l) + (l -> (n + 1, ty))
  def mergeLvlBags(a: LvlBag, b: LvlBag): LvlBag =
    (a.keySet ++ b.keySet).map { k =>
      (a.get(k), b.get(k)) match
        case (None, None)                  => impossible()
        case (Some((n, ty)), Some((m, _))) => (k, (n + m, ty))
        case (Some(c), _)                  => (k, c)
        case (_, Some(c))                  => (k, c)
    }.toMap
  def singletonLvlBag(ks: Iterable[(Lvl, TDef)]): LvlBag =
    ks.foldLeft[LvlBag](Map.empty) { case (b, (k, ty)) =>
      insertLvlBag(k, ty, b)
    }

  type CTmId = Int
  type Closure = (LvlBag, Map[Lvl, Lvl], CTmId)
  type ClosureStore = Map[CTmId, (Lvl, CTm)]
  type VLetEntry = LetEntry[Closure]
  type OTm = Tm[Option[(Int, VLetEntry)]]
  type CTm = Tm[(Int, VLetEntry)]
  type CDef = Def[CTm]
