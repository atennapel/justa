import Common.*
import Common.Icit.*
import Core.*
import Core.{Val1 as V1, Val0 as V0, Tm1 as T1, Tm0 as T0}
import Evaluation.*
import Debug.debug

import scala.collection.immutable.IntMap

object Unification:
  case class UnifyError(msg: String) extends RuntimeException(msg)

  // partial substitution
  private enum PSEntry:
    case PS0(value: Val0)
    case PS1(value: Val1)
  import PSEntry.*

  private final case class PSub(
      occ: Option[MetaId],
      dom: Lvl,
      cod: Lvl,
      sub: IntMap[PSEntry]
  ):
    def lift1: PSub =
      PSub(
        occ,
        dom + 1,
        cod + 1,
        sub + (cod.expose -> PS1(V1.Var(dom)))
      )
    def lift0: PSub =
      PSub(
        occ,
        dom + 1,
        cod + 1,
        sub + (cod.expose -> PS0(V0.Var(dom)))
      )
    inline def skip: PSub = copy(cod = cod + 1)

  private object PSub:
    val empty = PSub(None, lvl0, lvl0, IntMap.empty)

  // invert
  private type Invert = (Lvl, Set[Lvl], IntMap[PSEntry], Pruning, Boolean)

  private def invertVal1(v: Val1, rhs: Val1, i: Icit, data: Invert): Invert =
    forceAll1(v) match
      case V1.Var(x) =>
        val (dom, domvars, sub, pr, isLinear) = data
        if domvars.contains(x) then
          (dom + 1, domvars, sub - x.expose, PruneEntry.Skip :: pr, false)
        else
          (
            dom + 1,
            domvars + x,
            sub + (x.expose -> PS1(rhs)),
            PruneEntry.Bind1(i) :: pr,
            isLinear
          )
      case V1.Quote(v) => invertVal0(v, vsplice(rhs), i, data)
      case _           => throw UnifyError("spine error")

  private def invertVal0(v: Val0, rhs: Val0, i: Icit, data: Invert): Invert =
    forceAll0(v) match
      case V0.Var(x) =>
        val (dom, domvars, sub, pr, isLinear) = data
        if domvars.contains(x) then
          (dom + 1, domvars, sub - x.expose, PruneEntry.Skip :: pr, false)
        else
          (
            dom + 1,
            domvars + x,
            sub + (x.expose -> PS0(rhs)),
            PruneEntry.Bind0 :: pr,
            isLinear
          )
      case V0.Splice(v) => invertVal1(v, vquote(rhs), i, data)
      case _            => throw UnifyError("spine error")

  private def invert(sp: Spine)(using lvl: Lvl): (PSub, Option[Pruning]) =
    def go(sp: Spine): Invert =
      sp match
        case Spine.Empty => (lvl0, Set.empty, IntMap.empty, Nil, true)
        case Spine.App(sp, v, i) =>
          val data = go(sp)
          invertVal1(v, V1.Var(data._1), i, data)
        case Spine.MetaApp0(sp, v) =>
          val data = go(sp)
          invertVal0(v, V0.Var(data._1), Expl, data)
        case Spine.MetaApp1(sp, v) =>
          val data = go(sp)
          invertVal1(v, V1.Var(data._1), Expl, data)
    val (dom, _, sub, pr, isLinear) = go(sp)
    (PSub(None, dom, lvl, sub), if isLinear then None else Some(pr))

  // pruning
  private def lams(l1: Lvl, ty: VTy, b: Tm1): Tm1 =
    def go(l2: Lvl, ty: VTy): Tm1 =
      if l1 == l2 then b
      else
        forceAll1(ty) match
          case t @ V1.Pi(x, i, a, c) =>
            T1.Lam(
              x,
              i,
              readback1(a)(using l2, UnfoldOption.None),
              go(l2 + 1, c(V1.Var(l2)))
            )
          case V1.MetaPi1(t, c) =>
            T1.MetaLam1(go(l2 + 1, c(V1.Var(l2))))
          case V1.MetaPi0(t, c) =>
            T1.MetaLam0(go(l2 + 1, c(V0.Var(l2))))
          case _ => impossible()
    go(lvl0, ty)

  private def pruneTy(p: RevPruning, ty: VTy): Ty =
    def go(p: Pruning, psub: PSub, ty: VTy): Ty = (p, forceAll1(ty)) match
      case (Nil, ty) => psubst1(ty)(using psub)

      case (PruneEntry.Skip :: p, V1.Pi(x, i, a, b)) =>
        go(p, psub.skip, b(V1.Var(psub.cod)))
      case (PruneEntry.Bind1(_) :: p, V1.Pi(x, i, a, b)) =>
        T1.Pi(
          x,
          i,
          psubst1(a)(using psub),
          go(p, psub.lift1, b(V1.Var(psub.cod)))
        )

      case (PruneEntry.Skip :: p, V1.MetaPi1(a, b)) =>
        go(p, psub.skip, b(V1.Var(psub.cod)))
      case (PruneEntry.Skip :: p, V1.MetaPi0(a, b)) =>
        go(p, psub.skip, b(V0.Var(psub.cod)))
      case (PruneEntry.Bind1(_) :: p, V1.MetaPi1(a, b)) =>
        T1.MetaPi1(
          psubst1(a)(using psub),
          go(p, psub.lift1, b(V1.Var(psub.cod)))
        )
      case (PruneEntry.Bind0 :: p, V1.MetaPi0(a, b)) =>
        T1.MetaPi0(
          psubst1(a)(using psub),
          go(p, psub.lift0, b(V0.Var(psub.cod)))
        )

      case _ => impossible()
    go(p.expose, PSub.empty, ty)

  private def solveMetaVar(m: MetaId, solution: Val1) = {
    if (State.isMetaFrozen(m))
      throw UnifyError(s"trying to solve frozen meta ?$m")
    State.solveMeta(m, solution)
  }

  private def pruneMeta(p: Pruning, m: MetaId)(using lvl: Lvl): MetaId =
    debug(s"pruneMeta ?$m $p")
    val entry = State.getMetaUnsolved(m)
    val mty = entry.ty
    val prunedty = eval1(pruneTy(RevPruning(p), mty))(using Env.Empty)
    val m2 = State.newMeta(prunedty)
    val solution =
      eval1(lams(mkLvl(p.size), mty, T1.AppPruning(m2, p)))(using Env.Empty)
    solveMetaVar(m, solution)
    m2

  private enum SpinePruneStatus:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import SpinePruneStatus.*

  private enum PruneTm:
    case Prune1(tm: Tm1, i: Icit)
    case PruneMeta1(tm: Tm1)
    case PruneMeta0(tm: Tm0)
  import PruneTm.*

  private def pruneVFlex(m: MetaId, sp: Spine)(using psub: PSub): Tm1 =
    debug(
      s"pruneVFlex ${readback1(V1.Flex(m, sp))(using psub.cod, UnfoldOption.None)}"
    )
    def go(sp: Spine): (List[Option[PruneTm]], SpinePruneStatus) =
      inline def go1(
          sp: Spine,
          v: Val1,
          inline ptm: Tm1 => PruneTm
      ): (List[Option[PruneTm]], SpinePruneStatus) =
        val (sp2, status) = go(sp)
        forceAll1(v) match
          case V1.Var(x) =>
            (psub.sub.get(x.expose), status) match
              case (Some(PS1(_)), _) => (Some(ptm(psubst1(v))) :: sp2, status)
              case (Some(PS0(v)), _) => impossible()
              case (None, OKNonRenaming) => throw UnifyError("failed to prune")
              case _                     => (None :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => throw UnifyError("failed to prune")
              case _            => (Some(ptm(psubst1(t))) :: sp2, OKNonRenaming)
      sp match
        case Spine.Empty           => (Nil, OKRenaming)
        case Spine.App(sp, v, i)   => go1(sp, v, t => Prune1(t, i))
        case Spine.MetaApp1(sp, v) => go1(sp, v, t => PruneMeta1(t))
        case Spine.MetaApp0(sp, v) =>
          val (sp2, status) = go(sp)
          forceAll0(v) match
            case V0.Var(x) =>
              (psub.sub.get(x.expose), status) match
                case (Some(PS1(_)), _) => impossible()
                case (Some(PS0(v)), _) =>
                  (Some(PruneMeta0(psubst0(v))) :: sp2, status)
                case (None, OKNonRenaming) =>
                  throw UnifyError("failed to prune")
                case _ => (None :: sp2, NeedsPruning)
            case t =>
              status match
                case NeedsPruning => throw UnifyError("failed to prune")
                case _ => (Some(PruneMeta0(psubst0(t))) :: sp2, OKNonRenaming)
    val (sp2, status) = go(sp)
    val m2 = status match
      case OKRenaming    => m
      case OKNonRenaming => m
      case NeedsPruning =>
        val pr = sp2.map { m =>
          m match
            case None                => PruneEntry.Skip
            case Some(Prune1(_, i))  => PruneEntry.Bind1(i)
            case Some(PruneMeta1(_)) => PruneEntry.Bind1(Expl)
            case Some(PruneMeta0(_)) => PruneEntry.Bind0
        }
        pruneMeta(pr, m)(using psub.cod)
    sp2.foldRight(T1.Meta(m2)) {
      case (None, t)                => t
      case (Some(Prune1(u, i)), t)  => T1.App(t, u, i)
      case (Some(PruneMeta1(u)), t) => T1.MetaApp1(t, u)
      case (Some(PruneMeta0(u)), t) => T1.MetaApp0(t, u)
    }

  // partial substitution action
  private def psubst0(v: Val0)(using psub: PSub): Tm0 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goClos(c: Clos0) = psubst0(c(V0.Var(psub.cod)))(using psub.lift0)
    forceMetas0(v) match
      case V0.Var(x) =>
        psub.sub.get(x.expose) match
          case None         => throw UnifyError(s"out of scope $x")
          case Some(PS1(_)) => impossible()
          case Some(PS0(v)) => readback0(v)(using psub.dom, UnfoldOption.None)
      case V0.Global(x)           => T0.Global(x)
      case V0.Let(x, ty, v, b)    => T0.Let(x, go1(ty), go0(v), goClos(b))
      case V0.LetRec(x, ty, v, b) => T0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case V0.Lam(x, ty, b)       => T0.Lam(x, go1(ty), goClos(b))
      case V0.App(f, a)           => T0.App(go0(f), go0(a))
      case V0.Splice(v)           => go1(v).splice

  private def psubstSpine(h: Tm1, sp: Spine)(using psub: PSub): Tm1 =
    sp match
      case Spine.Empty           => h
      case Spine.App(sp, v, i)   => T1.App(psubstSpine(h, sp), psubst1(v), i)
      case Spine.MetaApp1(sp, v) => T1.MetaApp1(psubstSpine(h, sp), psubst1(v))
      case Spine.MetaApp0(sp, v) => T1.MetaApp0(psubstSpine(h, sp), psubst0(v))

  private def psubst1(v: Val1)(using psub: PSub): Tm1 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goSp(h: Tm1, sp: Spine) = psubstSpine(h, sp)
    inline def goClos(c: Clos1) = psubst1(c(V1.Var(psub.cod)))(using psub.lift1)
    inline def goClos0(c: Clos1) =
      psubst1(c(V0.Var(psub.cod)))(using psub.lift1)
    forceMetas1(v) match
      case V1.Rigid(Head.Prim(p), sp) => goSp(T1.Prim(p), sp)
      case V1.Rigid(Head.Var(x), sp) =>
        psub.sub.get(x.expose) match
          case None         => throw UnifyError(s"out of scope $x")
          case Some(PS0(_)) => impossible()
          case Some(PS1(v)) =>
            goSp(readback1(v)(using psub.dom, UnfoldOption.None), sp)
      case V1.Flex(m, sp) =>
        if psub.occ.contains(m) then throw UnifyError(s"occurs error ?$m")
        else pruneVFlex(m, sp)
      case V1.Unfold(UnfoldHead.Global(x), sp, _) => goSp(T1.Global(x), sp)
      case V1.Pi(x, i, ty, b)   => T1.Pi(x, i, go1(ty), goClos(b))
      case V1.Lam(x, i, ty, b)  => T1.Lam(x, i, go1(ty), goClos(b))
      case V1.Fun(pty, cv, rty) => T1.Fun(go1(pty), go1(cv), go1(rty))
      case V1.Lift(cv, ty)      => T1.Lift(go1(cv), go1(ty))
      case V1.Quote(tm)         => go0(tm).quote
      case V1.MetaPi1(t, b)     => T1.MetaPi1(go1(t), goClos(b))
      case V1.MetaPi0(t, b)     => T1.MetaPi0(go1(t), goClos0(b))
      case V1.MetaLam1(b)       => T1.MetaLam1(goClos(b))
      case V1.MetaLam0(b)       => T1.MetaLam0(goClos0(b))

  // solving
  private def solve(id: MetaId, sp: Spine, rhs: Val1)(using lvl: Lvl): Unit =
    debug(s"solve ${readback1m(V1.Flex(id, sp))} := ${readback1m(rhs)}")
    solveWithPSub(id, invert(sp), rhs)

  private def solveWithPSub(m: MetaId, iv: (PSub, Option[Pruning]), rhs: Val1)(
      using lvl: Lvl
  ) =
    given psub: PSub = iv._1
    debug(s"solveWithPSub ?$m ($lvl) := ${readback1m(rhs)}")
    val entry = State.getMetaUnsolved(m)
    val mty = entry.ty
    iv._2.foreach(p => pruneTy(RevPruning(p), mty))
    val rhs2 = psubst1(rhs)(using psub.copy(occ = Some(m)))
    debug(s"solution ?$m := $rhs2")
    val rhs2lams = lams(psub.dom, mty, rhs2)
    val sol = eval1(rhs2lams)(using Env.Empty)
    solveMetaVar(m, sol)

  // unification
  def unify0(a: Val0, b: Val0)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos0, b: Clos0) =
      unify0(a(V0.Var(lvl)), b(V0.Var(lvl)))(using lvl + 1)
    debug(s"unify0 ${readback0m(a)} ~ ${readback0m(b)}")
    (forceMetas0(a), forceMetas0(b)) match
      case (V0.Var(x), V0.Var(y)) if x == y => ()
      case (V0.Let(_, ty1, v1, b1), V0.Let(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); unify0(v1, v2); goClos(b1, b2)
      case (V0.LetRec(_, ty1, v1, b1), V0.LetRec(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); goClos(v1, v2); goClos(b1, b2)
      case (V0.Splice(v1), V0.Splice(v2))       => unify1(v1, v2)
      case (V0.Lam(_, _, b1), V0.Lam(_, _, b2)) => goClos(b1, b2)
      case (V0.App(f1, a1), V0.App(f2, a2)) => unify0(f1, f2); unify0(a1, a2)
      case _ =>
        throw UnifyError(s"cannot unify ${readback0n(a)} ~ ${readback0n(b)}")

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    inline def go(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine): Unit =
      try
        val data = invert(sp1)
        solveWithPSub(m1, data, V1.Flex(m2, sp2))
      catch case _: UnifyError => solve(m2, sp2, V1.Flex(m1, sp1))
    if sp1.size < sp2.size then go(m2, sp2, m1, sp1) else go(m1, sp1, m2, sp2)

  private def intersect(m: MetaId, sp1: Spine, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    def go(sp1: Spine, sp2: Spine): Option[Pruning] =
      inline def go1(
          sp1: Spine,
          sp2: Spine,
          i: Icit,
          t1: Val1,
          t2: Val1
      ): Option[Pruning] =
        (forceAll1(t1), forceAll1(t2)) match
          case (V1.Var(x1), V1.Var(x2)) =>
            go(sp1, sp2).map(
              (if x1 == x2 then PruneEntry.Bind1(i) else PruneEntry.Skip) :: _
            )
          case _ => None
      (sp1, sp2) match
        case (Spine.Empty, Spine.Empty) => Some(Nil)

        case (Spine.App(sp1, t1, i), Spine.App(sp2, t2, _)) =>
          go1(sp1, sp2, i, t1, t2)

        case (Spine.MetaApp1(sp1, t1), Spine.MetaApp1(sp2, t2)) =>
          go1(sp1, sp2, Expl, t1, t2)
        case (Spine.MetaApp0(sp1, t1), Spine.MetaApp0(sp2, t2)) =>
          (forceAll0(t1), forceAll0(t2)) match
            case (V0.Var(x1), V0.Var(x2)) =>
              go(sp1, sp2).map(
                (if x1 == x2 then PruneEntry.Bind0 else PruneEntry.Skip) :: _
              )
            case _ => None
        case _ => impossible()
    go(sp1, sp2) match
      case None => unify1(V1.Flex(m, sp1), sp1, V1.Flex(m, sp2), sp2)
      case Some(p) if p.exists(_ == PruneEntry.Skip) => pruneMeta(p, m)
      case _                                         => ()

  private def unify1(top1: Val1, sp1: Spine, top2: Val1, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty) => ()
      case (Spine.App(sp1, a1, _), Spine.App(sp2, a2, _)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case (Spine.MetaApp0(sp1, a1), Spine.MetaApp0(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify0(a1, a2)
      case (Spine.MetaApp1(sp1, a1), Spine.MetaApp1(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case _ =>
        throw UnifyError(
          s"spine mismatch ${readback1n(top1)} ~ ${readback1n(top2)}"
        )

  def unify1(a: Val1, b: Val1)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos1, b: Clos1) =
      val v = V1.Var(lvl)
      unify1(a(v), b(v))(using lvl + 1)
    inline def goClos0(a: Clos1, b: Clos1) =
      val v = V0.Var(lvl)
      unify1(a(v), b(v))(using lvl + 1)
    debug(s"unify1 ${readback1m(a)} ~ ${readback1m(b)}")
    (forceMetas1(a), forceMetas1(b)) match
      case (V1.Rigid(x, sp1), V1.Rigid(y, sp2)) if x == y =>
        unify1(a, sp1, b, sp2)

      case (V1.Lift(cv1, ty1), V1.Lift(cv2, ty2)) =>
        unify1(cv1, cv2); unify1(ty1, ty2)
      case (V1.Quote(v1), V1.Quote(v2)) => unify0(v1, v2)
      case (V1.Pi(_, i1, ty1, b1), V1.Pi(_, i2, ty2, b2)) if i1 == i2 =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (V1.MetaPi1(ty1, b1), V1.MetaPi1(ty2, b2)) =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (V1.MetaPi0(ty1, b1), V1.MetaPi0(ty2, b2)) =>
        unify1(ty1, ty2); goClos0(b1, b2)
      case (V1.Fun(t1, cv1, r1), V1.Fun(t2, cv2, r2)) =>
        unify1(t1, t2); unify1(cv1, cv2); unify1(r1, r2)

      case (V1.Lam(_, _, _, b1), V1.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (V1.Lam(_, i, _, b), f) =>
        val v = V1.Var(lvl)
        unify1(b(v), vapp1(f, v, i))(using lvl + 1)
      case (f, V1.Lam(_, i, _, b)) =>
        val v = V1.Var(lvl)
        unify1(vapp1(f, v, i), b(v))(using lvl + 1)

      case (V1.MetaLam1(b1), V1.MetaLam1(b2)) => goClos(b1, b2)
      case (V1.MetaLam0(b1), V1.MetaLam0(b2)) => goClos0(b1, b2)
      case (V1.MetaLam1(b), f) =>
        val v = V1.Var(lvl)
        unify1(b(v), vmetaapp1(f, v))(using lvl + 1)
      case (V1.MetaLam0(b), f) =>
        val v = V0.Var(lvl)
        unify1(b(v), vmetaapp0(f, v))(using lvl + 1)
      case (f, V1.MetaLam1(b)) =>
        val v = V1.Var(lvl)
        unify1(vmetaapp1(f, v), b(v))(using lvl + 1)
      case (f, V1.MetaLam0(b)) =>
        val v = V0.Var(lvl)
        unify1(vmetaapp0(f, v), b(v))(using lvl + 1)

      case (V1.Flex(id1, sp1), V1.Flex(id2, sp2)) =>
        if id1 == id2 then intersect(id1, sp1, sp2)
        else flexFlex(id1, sp1, id2, sp2)
      case (V1.Flex(id, sp), v) => solve(id, sp, v)
      case (v, V1.Flex(id, sp)) => solve(id, sp, v)

      case (top1 @ V1.Unfold(h1, sp1, v1), top2 @ V1.Unfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then throw UnifyError("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnifyError => unify1(v1(), v2())
      case (V1.Unfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, V1.Unfold(_, _, v2)) => unify1(v1, v2())

      case _ =>
        throw UnifyError(s"cannot unify ${readback1n(a)} ~ ${readback1n(b)}")
