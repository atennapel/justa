package optimization

import common.Common.*
import Syntax.*

import scala.collection.mutable
import scala.annotation.tailrec

// algorithm from: https://github.com/AndrasKovacs/staged/blob/main/opt/CSE3.hs
object Optimization:
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
  private object Ren:
    def empty: Ren = Ren(lvl0, lvl0, Map.empty)
    def closing(cod: Lvl, arity: Int, xs: LvlBag): Ren =
      (xs -- cod.range(cod + arity))
        .foldLeft[Ren](Ren(lvl0, cod, Map.empty).liftN(arity)) {
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
            case LetGlobal(x, args) => LetGlobal(x, args.map(ren.app))
            case LetApp(fn, args)   => LetApp(ren.app(fn), args.map(ren.app))
            case LetNative(x, args) => LetNative(x, args.map(ren.app))
            case LetLam(ty, (xs, rs, t)) =>
              LetLam(ty, (ren.renameLvlBag(xs), rs, t))
            case LetRecLam(ty, (xs, rs, t)) =>
              LetRecLam(ty, (ren.renameLvlBag(xs), rs, t))
          go(ren.lift, next, (n, nl) :: acc)
    go(ren, tm.lets, Nil)

  // optimization
  private type Globals = Map[Name, TDef]

  def optimize(ds: List[Def[NTm]]): (ClosureStore, List[CDef]) =
    def sanityCheck(is: Iterable[(Lvl, CTm)]): (Lvl, CTm) =
      val res = is.toList.distinct
      if res.size != 1 then impossible()
      res.head
    implicit val store: Store = mutable.Map.empty
    implicit val globals: Globals =
      ds.map { case DDef(x, ty, _) => (x -> ty) }.toMap
    val res = ds.map { case DDef(x, ty, tm) =>
      val otm = optimize(ty, tm)
      DDef(x, ty, otm)
    }
    (store.groupMap(_._2)(_._1).mapValues(sanityCheck).toMap, res)

  private type Memo = Map[VLetEntry, (Lvl, TDef)]

  private def optimize(ty: TDef, tm: NTm)(implicit
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
    rename(Ren.lifted(arity), otm)

  private def go(l: Lvl, env: List[(Lvl, TDef)], memo: Memo, tm: NTm)(implicit
      store: Store,
      globals: Globals
  ): (OTm, LvlBag) =
    def go(
        k: Lvl,
        ls: List[LetEntry[NTm]],
        acc: List[Option[(Int, VLetEntry)]],
        env: List[(Lvl, TDef)],
        memo: Memo,
        finalret: Lvl
    ): (OTm, LvlBag) =
      inline def ix(i: Lvl): (Lvl, TDef) = env(env.size - i.expose - 1)
      ls match
        case Nil =>
          val (x, ty) = ix(finalret)
          (Tm(acc.reverse, x), Map(x -> (1, ty)))
        case l :: next =>
          inline def cont(v: VLetEntry, ty: TDef, vars: LvlBag): (OTm, LvlBag) =
            memo.get(v) match
              case Some(e) => go(k, next, acc, e :: env, memo, finalret)
              case None =>
                val (Tm(retlets, ret), tvars) =
                  go(
                    k + 1,
                    next,
                    acc,
                    (k, ty) :: env,
                    memo + ((v, (k, ty))),
                    finalret
                  )
                if tvars.contains(k) && tvars(k)._1 > 0 then
                  (
                    Tm(Some((tvars(k)._1, v)) :: retlets, ret),
                    mergeLvlBags(tvars - k, vars)
                  )
                else (Tm(None :: retlets, ret), tvars)
          l match
            case LetGlobal(x, args) =>
              val args2 = args.map(ix(_))
              val v: VLetEntry = LetGlobal(x, args2.map(_._1))
              cont(v, TDef(globals(x).rt), singletonLvlBag(args2))
            case LetNative(x, args) =>
              val args2 = args.map(ix(_))
              val v: VLetEntry = LetNative(x, args2.map(_._1))
              cont(v, nativeReturnTy(x), singletonLvlBag(args2))
            case LetApp(fn, args) =>
              val x2 = ix(fn)
              val args2 = args.map(ix(_))
              val v: VLetEntry = LetApp(x2._1, args2.map(_._1))
              cont(v, TDef(x2._2.rt), singletonLvlBag(x2 :: args2))
            case LetLam(ty, body) =>
              val arity = ty.arity
              val nenv = k.range(k + arity).zip(ty.ps.map(TDef.apply))
              val (t, tvars) =
                go(
                  k + arity,
                  body.tm.lets,
                  Nil,
                  nenv.reverse ++ env,
                  memo,
                  body.tm.ret
                )
              val ren = Ren.closing(k, arity, tvars)
              val t2 = storeEntry((ren.dom - arity, rename(ren, t)))
              val capture = tvars -- nenv.map(_._1)
              val v = LetLam(ty, (capture, ren.ren, t2))
              cont(v, ty, capture)
            case LetRecLam(ty, body) =>
              val arity = ty.arity + 1
              val nenv =
                k.range(k + arity).zip(List(ty) ++ ty.ps.map(TDef.apply))
              val (t, tvars) =
                go(
                  k + arity,
                  body.tm.lets,
                  Nil,
                  nenv.reverse ++ env,
                  memo,
                  body.tm.ret
                )
              val ren = Ren.closing(k, arity, tvars)
              val t2 = storeEntry((ren.dom - arity, rename(ren, t)))
              val capture = tvars -- nenv.map(_._1)
              val v = LetRecLam(ty, (capture, ren.ren, t2))
              cont(v, ty, capture)
    go(l, tm.tm.lets, Nil, env, memo, tm.tm.ret)

  private val tbool = TDef(TNative(Name("Bool")))

  private def nativeReturnTy(x: Name): TDef =
    x.expose match
      case "True"  => tbool
      case "False" => tbool
      case _       => impossible()
