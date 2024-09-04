package optimization

import common.Common.*
import Syntax.*

import scala.collection.mutable
import scala.annotation.tailrec

// algorithm from: https://github.com/AndrasKovacs/staged/blob/main/opt/CSE3.hs
object Optimization:
  // store
  private type Store = mutable.Map[(Lvl, CTm), CTmId]
  type ClosureStore = Map[CTmId, (Lvl, CTm)]

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
  private object Ren:
    def empty: Ren = Ren(lvl0, lvl0, Map.empty)
    def closing(cod: Lvl, xs: LvlBag): Ren =
      xs.foldLeft[Ren](Ren(lvl0, cod, Map.empty)) {
        case (Ren(dom, cod, ren), (x, _)) =>
          Ren(dom + 1, cod, ren + ((x, dom)))
      }
    def lifted(n: Int): Ren = Ren.empty.liftN(n)

  private def rename(ren: Ren, tm: OTm): CTm =
    @tailrec
    def go(
        ren: Ren,
        ls: List[Option[(Int, VLetEntry)]],
        acc: List[(Int, VLetEntry)]
    ): CTm =
      ls match
        case Nil          => Tm(acc.reverse, ren.app(tm.ret))
        case None :: next => go(ren.str, next, acc)
        case Some((n, l)) :: next =>
          val nl = l match
            case LetGlobal(x, args)  => LetGlobal(x, args.map(ren.app))
            case LetApp(fn, args)    => LetApp(ren.app(fn), args.map(ren.app))
            case LetNative(x, args)  => LetNative(x, args.map(ren.app))
            case LetLam(ty, (xs, t)) => LetLam(ty, (ren.renameLvlBag(xs), t))
            case LetRecLam(ty, (xs, t)) =>
              LetRecLam(ty, (ren.renameLvlBag(xs), t))
          go(ren.lift, next, (n, nl) :: acc)
    go(ren, tm.lets, Nil)

  // optimization
  def optimize(ds: List[Def[NTm]]): (ClosureStore, List[Def[CTm]]) =
    def sanityCheck(
        is: Iterable[(common.Common.Lvl, optimization.Syntax.CTm)]
    ): (common.Common.Lvl, optimization.Syntax.CTm) =
      val res = is.toList.distinct
      if res.size != 1 then impossible()
      res.head
    implicit val store: Store = mutable.Map.empty
    val res = ds.map { case DDef(x, ty, tm) =>
      val otm = optimize(ty.arity, tm)
      DDef(x, ty, otm)
    }
    (store.groupMap(_._2)(_._1).mapValues(sanityCheck).toMap, res)

  private type Memo = Map[VLetEntry, Lvl]

  private def optimize(arity: Int, tm: NTm)(implicit store: Store): CTm =
    @tailrec
    def mkEnv(n: Lvl = lvl0, env: List[Lvl] = Nil): List[Lvl] =
      if n < mkLvl(arity) then mkEnv(n + 1, n :: env)
      else env
    val env = mkEnv()
    val (otm, xs) = go(mkLvl(arity), env, Map.empty, tm)
    if ((xs -- env).nonEmpty) impossible()
    rename(Ren.lifted(arity), otm)

  private def go(l: Lvl, env: List[Lvl], memo: Memo, tm: NTm)(implicit
      store: Store
  ): (OTm, LvlBag) =
    inline def ix(env: List[Lvl], i: Lvl): Lvl = env(env.size - i.expose - 1)
    def go(
        k: Lvl,
        ls: List[LetEntry[NTm]],
        acc: List[Option[(Int, VLetEntry)]],
        env: List[Lvl],
        memo: Memo,
        finalret: Lvl
    ): (OTm, LvlBag) =
      ls match
        case Nil =>
          val x = ix(env, finalret)
          (Tm(acc.reverse, x), Map(x -> 1))
        case l :: next =>
          inline def cont(v: VLetEntry, vars: LvlBag): (OTm, LvlBag) =
            memo.get(v) match
              case Some(x) => go(k, next, acc, x :: env, memo, finalret)
              case None =>
                val (Tm(retlets, ret), tvars) =
                  go(k + 1, next, acc, k :: env, memo + ((v, k)), finalret)
                if tvars.contains(k) && tvars(k) > 0 then
                  (
                    Tm(Some((tvars(k), v)) :: retlets, ret),
                    mergeLvlBags(tvars - k, vars)
                  )
                else (Tm(None :: retlets, ret), tvars)
          l match
            case LetGlobal(x, args) =>
              val args2 = args.map(ix(env, _))
              val v: VLetEntry = LetGlobal(x, args2)
              cont(v, singletonLvlBag(args2))
            case LetNative(x, args) =>
              val args2 = args.map(ix(env, _))
              val v: VLetEntry = LetNative(x, args2)
              cont(v, singletonLvlBag(args2))
            case LetApp(fn, args) =>
              val x2 = ix(env, fn)
              val args2 = args.map(ix(env, _))
              val v: VLetEntry = LetApp(x2, args2)
              cont(v, singletonLvlBag(x2 :: args2))
            case LetLam(ty, body) =>
              val arity = ty.arity
              val nenv = (k.expose until (k + arity).expose).map(mkLvl)
              val (t, tvars) =
                go(
                  k + arity,
                  body.tm.lets,
                  Nil,
                  nenv.reverse.toList ++ env,
                  memo,
                  body.tm.ret
                )
              val ren = Ren.closing(k + arity, tvars)
              val t2 = storeEntry((ren.dom, rename(ren, t)))
              val capture = tvars -- nenv
              val v = LetLam(ty, (capture, t2))
              cont(v, capture)
            case LetRecLam(ty, body) =>
              val arity = ty.arity + 1
              val nenv = (k.expose until (k + arity).expose).map(mkLvl)
              val (t, tvars) =
                go(
                  k + arity,
                  body.tm.lets,
                  Nil,
                  nenv.reverse.toList ++ env,
                  memo,
                  body.tm.ret
                )
              val ren = Ren.closing(k + arity, tvars)
              val t2 = storeEntry((ren.dom, rename(ren, t)))
              val capture = tvars -- nenv
              val v = LetRecLam(ty, (capture, t2))
              cont(v, capture)
    go(l, tm.tm.lets, Nil, env, memo, tm.tm.ret)
