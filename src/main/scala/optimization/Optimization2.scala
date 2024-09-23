package optimization

import common.Common.*
import Syntax.TDef
import Normalization2 as N

import scala.collection.mutable
import scala.annotation.tailrec

object Optimization2:
  type CTmId = Int
  type LvlBag = Map[Lvl, (Int, TDef)]
  type ClosureStore = Map[CTmId, (Lvl, CTm)]

  private def insertLvlBag(l: Lvl, ty: TDef, a: LvlBag): LvlBag =
    a.get(l) match
      case None         => a + (l -> (1, ty))
      case Some((n, _)) => (a - l) + (l -> (n + 1, ty))
  private def mergeLvlBags(a: LvlBag, b: LvlBag): LvlBag =
    (a.keySet ++ b.keySet).map { k =>
      (a.get(k), b.get(k)) match
        case (None, None)                  => impossible()
        case (Some((n, ty)), Some((m, _))) => (k, (n + m, ty))
        case (Some(c), _)                  => (k, c)
        case (_, Some(c))                  => (k, c)
    }.toMap
  private def singletonLvlBag(ks: Iterable[(Lvl, TDef)]): LvlBag =
    ks.foldLeft[LvlBag](Map.empty) { case (b, (k, ty)) =>
      insertLvlBag(k, ty, b)
    }

  enum Val:
    case App(fn: Lvl, args: List[Lvl])
    case Global(x: Name, args: List[Lvl])
    case Con(x: Name, args: List[Lvl])
    case Lam(ty: TDef, fvs: LvlBag, ren: Map[Lvl, Lvl], body: CTmId)
    case Rec(ty: TDef, fvs: LvlBag, ren: Map[Lvl, Lvl], body: CTmId)
  import Val.*

  private enum OTm:
    case Ret(lvl: Lvl)
    case Let(value: Val, body: OTm)
    case DeadLet(body: OTm)
    case If(cond: Lvl, ifTrue: OTm, ifFalse: OTm)
  import OTm as O

  enum CTm:
    case Ret(lvl: Lvl)
    case Let(value: Val, body: CTm)
    case If(cond: Lvl, ifTrue: CTm, ifFalse: CTm)
  import CTm as C

  final case class Def(name: Name, ty: TDef, value: CTm)

  // store
  private type Store = mutable.Map[(Lvl, CTm), CTmId]

  private def storeEntry(entry: (Lvl, CTm))(implicit store: Store): CTmId =
    store.get(entry) match
      case Some(id) => id
      case None =>
        val id = store.size
        store += ((entry, id))
        id

  // closing terms
  private final case class Ren(dom: Lvl, cod: Lvl, ren: Map[Lvl, Lvl]):
    def str: Ren = Ren(dom, cod + 1, ren)
    def lift: Ren = Ren(dom + 1, cod + 1, ren + ((cod, dom)))
    def liftN(n: Int): Ren =
      if n > 0 then lift.liftN(n - 1)
      else this
    def app(x: Lvl): Lvl =
      ren.get(x) match
        case None    => impossible()
        case Some(y) => y
    def renameLvlBag(xs: LvlBag): LvlBag = xs.map((k, v) => (ren(k), v))
    def rename(tm: OTm): CTm =
      def go(ren: Ren, tm: OTm): CTm =
        tm match
          case O.Ret(k) => C.Ret(ren.app(k))
          case O.Let(v, b) =>
            val cv = v match
              case App(fn, args)      => App(ren.app(fn), args.map(ren.app))
              case Global(x, args)    => Global(x, args.map(ren.app))
              case Con(x, args)       => Con(x, args.map(ren.app))
              case Lam(ty, fvs, r, b) => Lam(ty, ren.renameLvlBag(fvs), r, b)
              case Rec(ty, fvs, r, b) =>
                Rec(ty, ren.lift.renameLvlBag(fvs), r, b)
            C.Let(cv, go(ren.lift, b))
          case O.DeadLet(b)  => go(ren.str, b)
          case O.If(c, t, f) => C.If(ren.app(c), go(ren, t), go(ren, f))
      go(this, tm)
  private object Ren:
    def empty: Ren = Ren(lvl0, lvl0, Map.empty)
    def closing(cod: Lvl, arity: Int, xs: LvlBag): Ren =
      (xs -- cod.range(cod + arity))
        .foldLeft[Ren](Ren(lvl0, cod, Map.empty).liftN(arity)) {
          case (Ren(dom, cod, ren), (x, _)) =>
            Ren(dom + 1, cod, ren + ((x, dom)))
        }
    def lifted(n: Int): Ren = Ren.empty.liftN(n)

  // optimization
  private type Globals = Map[Name, TDef]
  private type Memo = Map[Val, (Lvl, TDef)]

  def optimize(ds: List[N.Def]): (ClosureStore, List[Def]) =
    def sanityCheck(is: Iterable[(Lvl, CTm)]): (Lvl, CTm) =
      val res = is.toList.distinct
      if res.size != 1 then impossible()
      res.head
    implicit val store: Store = mutable.Map.empty
    implicit val globals: Globals =
      ds.map { case N.Def(x, ty, _) => (x -> ty) }.toMap
    val res = ds.map { case N.Def(x, ty, tm) =>
      val otm = optimize(ty, tm)
      Def(x, ty, otm)
    }
    (store.groupMap(_._2)(_._1).mapValues(sanityCheck).toMap, res)

  private def optimize(ty: TDef, tm: N.ANF)(implicit
      store: Store,
      globals: Globals
  ): CTm =
    val arity = ty.arity
    @tailrec
    def mkEnv(n: Lvl = lvl0, env: List[Lvl] = Nil): List[Lvl] =
      if n < mkLvl(arity) then mkEnv(n + 1, n :: env)
      else env
    val env = mkEnv().zip(ty.ps.reverse.map(TDef.apply))
    val (otm, xs) = go(mkLvl(arity), env, Map.empty, tm)
    if ((xs -- env.map(_._1)).nonEmpty) impossible()
    Ren.lifted(arity).rename(otm)

  private def go(l: Lvl, env: List[(Lvl, TDef)], memo: Memo, tm: N.ANF)(implicit
      store: Store,
      globals: Globals
  ): (OTm, LvlBag) =
    inline def ix(i: Lvl): (Lvl, TDef) = env(env.size - i.expose - 1)
    ???
