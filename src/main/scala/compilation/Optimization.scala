package compilation

import common.Common.*
import Syntax.*
import Normalization as N

import scala.collection.mutable
import scala.annotation.tailrec

object Optimization:
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

  final case class Closure(fvs: LvlBag, ren: Map[Lvl, Lvl], body: CTmId)

  enum Val:
    case App(fn: Lvl, args: List[Lvl])
    case Global(x: Name, args: List[Lvl])
    case Con(x: Name, args: List[Lvl])
    case Lam(ty: TDef, clos: Closure)
    case Rec(ty: TDef, clos: Closure)

    override def toString: String = this match
      case App(fn, args) =>
        s"'$fn${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Global(x, args) =>
        s"$x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Con(x, Nil) => x.toString
      case Con(x, args) =>
        s"$x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Lam(ty, clos) => s"\\($ty). '${clos.body}"
      case Rec(ty, clos) => s"\\rec ($ty). ${clos.body}"
  import Val.*

  private enum OTm:
    case Ret(lvl: Lvl)
    case Let(usage: Int, value: Val, body: OTm)
    case DeadLet(body: OTm)
    case If(cond: Lvl, rt: Ty, ifTrue: Closure, ifFalse: Closure)
  import OTm as O

  enum CTm:
    case Ret(lvl: Lvl)
    case Let(usage: Int, value: Val, body: CTm)
    case If(cond: Lvl, rt: Ty, ifTrue: Closure, ifFalse: Closure)

    override def toString: String = this match
      case Ret(lvl)        => s"'$lvl"
      case Let(u, v, b)    => s"let $v; $b"
      case If(c, rt, t, f) => s"if '$c then ${t.body} else ${f.body}"
  import CTm as C

  final case class Def(name: Name, ty: TDef, value: CTm):
    override def toString: String = s"def $name : $ty = $value"

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
        inline def goClos(ren: Ren, c: Closure): Closure =
          Closure(ren.renameLvlBag(c.fvs), c.ren, c.body)
        tm match
          case O.Ret(k) => C.Ret(ren.app(k))
          case O.Let(u, v, b) =>
            val cv = v match
              case App(fn, args)   => App(ren.app(fn), args.map(ren.app))
              case Global(x, args) => Global(x, args.map(ren.app))
              case Con(x, args)    => Con(x, args.map(ren.app))
              case Lam(ty, c)      => Lam(ty, goClos(ren, c))
              case Rec(ty, c)      => Rec(ty, goClos(ren.lift, c))
            C.Let(u, cv, go(ren.lift, b))
          case O.DeadLet(b) => go(ren.str, b)
          case O.If(c, rt, t, f) =>
            C.If(ren.app(c), rt, goClos(ren, t), goClos(ren, f))
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
    tm match
      case N.Ret(k) =>
        val (x, ty) = ix(k)
        (O.Ret(x), Map(x -> (1, ty)))
      case N.If(c, rt, t, f) =>
        val (cx, ty) = ix(c)
        val (tt, fvt) = go(l, env, memo, t)
        val (ff, fvf) = go(l, env, memo, f)
        val tren = Ren.closing(l, 0, fvt)
        val fren = Ren.closing(l, 0, fvf)
        val tid = storeEntry((tren.dom, tren.rename(tt)))
        val fid = storeEntry((fren.dom, fren.rename(ff)))
        (
          O.If(
            cx,
            rt,
            Closure(fvt, tren.ren, tid),
            Closure(fvf, fren.ren, fid)
          ),
          mergeLvlBags(Map(cx -> (1, ty)), mergeLvlBags(fvt, fvf))
        )
      case N.Let(v, b) =>
        inline def cont(v: Val, ty: TDef, vars: LvlBag): (OTm, LvlBag) =
          memo.get(v) match
            case Some(e) => go(l, e :: env, memo, b)
            case None =>
              val (rtm, tvars) =
                go(l + 1, (l, ty) :: env, memo + ((v, (l, ty))), b)
              if tvars.contains(l) && tvars(l)._1 > 0 then
                (O.Let(tvars(l)._1, v, rtm), mergeLvlBags(tvars - l, vars))
              else (O.DeadLet(rtm), tvars)
        v match
          case N.Global(x, args) =>
            val args2 = args.map(ix(_))
            val nv = Global(x, args2.map(_._1))
            cont(nv, TDef(globals(x).rt), singletonLvlBag(args2))
          case N.Con(x, args) =>
            val args2 = args.map(ix(_))
            val nv = Con(x, args2.map(_._1))
            cont(nv, nativeReturnTy(x), singletonLvlBag(args2))
          case N.App(fn, args) =>
            val x2 = ix(fn)
            val args2 = args.map(ix(_))
            val v = App(x2._1, args2.map(_._1))
            cont(v, TDef(x2._2.rt), singletonLvlBag(x2 :: args2))
          case N.Lam(ty, b) =>
            val arity = ty.arity
            val nenv = l.range(l + arity).zip(ty.ps.map(TDef.apply))
            val (t, tvars) = go(l + arity, nenv.reverse ++ env, memo, b)
            val ren = Ren.closing(l, arity, tvars)
            val t2 = storeEntry((ren.dom - arity, ren.rename(t)))
            val capture = tvars -- nenv.map(_._1)
            val v = Lam(ty, Closure(capture, ren.ren, t2))
            cont(v, ty, capture)
          case N.Rec(ty, b) =>
            val arity = ty.arity + 1
            val nenv = l.range(l + arity).zip(List(ty) ++ ty.ps.map(TDef.apply))
            val (t, tvars) = go(l + arity, nenv.reverse ++ env, memo, b)
            val ren = Ren.closing(l, arity, tvars)
            val t2 = storeEntry((ren.dom - arity, ren.rename(t)))
            val capture = tvars -- nenv.map(_._1)
            val v = Rec(ty, Closure(capture, ren.ren, t2))
            cont(v, ty, capture)

  private val tbool = TDef(TBool)
  private def nativeReturnTy(x: Name): TDef =
    x.expose match
      case "True"  => tbool
      case "False" => tbool
      case _       => impossible()
