package core

import common.Common.*
import Syntax.*
import core.Value.*
import common.Debug.debug

import scala.collection.immutable.IntMap

object Unification:
  case class UnifyError(msg: String) extends Exception(msg)

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
        sub + (cod.expose -> PS1(VVar1(dom)))
      )
    def lift0: PSub =
      PSub(
        occ,
        dom + 1,
        cod + 1,
        sub + (cod.expose -> PS0(VVar0(dom)))
      )
    inline def skip: PSub = copy(cod = cod + 1)

  private object PSub:
    val empty = PSub(None, lvl0, lvl0, IntMap.empty)

class Unification(evaluation: Evaluation):
  import Evaluation.QuoteOption.*
  import Unification.*
  import Unification.PSEntry.*

  import evaluation.*
  import evaluation.state.*

  // invert
  private type Invert = (Lvl, Set[Lvl], IntMap[PSEntry], Pruning, Boolean)

  private def invertVal1(v: Val1, rhs: Val1, i: Icit, data: Invert): Invert =
    forceAll1(v) match
      case VVar1(x) =>
        val (dom, domvars, sub, pr, isLinear) = data
        if domvars.contains(x) then
          (dom + 1, domvars, sub - x.expose, PESkip :: pr, false)
        else
          (
            dom + 1,
            domvars + x,
            sub + (x.expose -> PS1(rhs)),
            PEBind1(i) :: pr,
            isLinear
          )
      case VQuote(v) => invertVal0(v, vsplice(rhs), i, data)
      case _         => throw UnifyError("spine error")

  private def invertVal0(v: Val0, rhs: Val0, i: Icit, data: Invert): Invert =
    forceAll0(v) match
      case VVar0(x) =>
        val (dom, domvars, sub, pr, isLinear) = data
        if domvars.contains(x) then
          (dom + 1, domvars, sub - x.expose, PESkip :: pr, false)
        else
          (
            dom + 1,
            domvars + x,
            sub + (x.expose -> PS0(rhs)),
            PEBind0 :: pr,
            isLinear
          )
      case VSplice(v) => invertVal1(v, vquote(rhs), i, data)
      case _          => throw UnifyError("spine error")

  private def invert(sp: Spine)(implicit lvl: Lvl): (PSub, Option[Pruning]) =
    def go(sp: Spine): Invert =
      sp match
        case SId => (lvl0, Set.empty, IntMap.empty, Nil, true)
        case SApp(sp, v, i) =>
          val data = go(sp)
          invertVal1(v, VVar1(data._1), i, data)
        case SMetaApp0(sp, v) =>
          val data = go(sp)
          invertVal0(v, VVar0(data._1), Expl, data)
        case SMetaApp1(sp, v) =>
          val data = go(sp)
          invertVal1(v, VVar1(data._1), Expl, data)
    val (dom, _, sub, pr, isLinear) = go(sp)
    (PSub(None, dom, lvl, sub), if isLinear then None else Some(pr))

  // pruning
  private def lams(l1: Lvl, ty: VTy, b: Tm1): Tm1 =
    def go(l2: Lvl, ty: VTy): Tm1 =
      if l1 == l2 then b
      else
        forceAll1(ty) match
          case t @ VPi(x, i, a, c) =>
            Lam1(
              x,
              i,
              quote1(a, UnfoldNone)(l2),
              go(l2 + 1, c(VVar1(l2)))
            )
          case VMetaPi1(t, c) =>
            MetaLam1(go(l2 + 1, c(VVar1(l2))))
          case VMetaPi0(t, c) =>
            MetaLam0(go(l2 + 1, c(VVar0(l2))))
          case _ => impossible()
    go(lvl0, ty)

  private def pruneTy(p: RevPruning, ty: VTy): Ty =
    def go(p: Pruning, psub: PSub, ty: VTy): Ty = (p, forceAll1(ty)) match
      case (Nil, ty) => psubst1(ty)(psub)

      case (PESkip :: p, VPi(x, i, a, b)) =>
        go(p, psub.skip, b(VVar1(psub.cod)))
      case (PEBind1(_) :: p, VPi(x, i, a, b)) =>
        Pi(x, i, psubst1(a)(psub), go(p, psub.lift1, b(VVar1(psub.cod))))

      case (PESkip :: p, VMetaPi1(a, b)) =>
        go(p, psub.skip, b(VVar1(psub.cod)))
      case (PESkip :: p, VMetaPi0(a, b)) =>
        go(p, psub.skip, b(VVar0(psub.cod)))
      case (PEBind1(_) :: p, VMetaPi1(a, b)) =>
        MetaPi1(psubst1(a)(psub), go(p, psub.lift1, b(VVar1(psub.cod))))
      case (PEBind0 :: p, VMetaPi0(a, b)) =>
        MetaPi0(psubst1(a)(psub), go(p, psub.lift0, b(VVar0(psub.cod))))

      case _ => impossible()
    go(p.expose, PSub.empty, ty)

  private def solveMetaVar(m: MetaId, solution: Val1) = {
    if (isMetaFrozen(m)) throw UnifyError(s"trying to solve frozen meta ?$m")
    solveMeta(m, solution)
  }

  private def pruneMeta(p: Pruning, m: MetaId)(implicit lvl: Lvl): MetaId =
    debug(s"pruneMeta ?$m $p")
    val entry = getMetaUnsolved(m)
    val mty = entry.ty
    val prunedty = eval1(pruneTy(RevPruning(p), mty))(EEmpty)
    val m2 = newMeta(prunedty)
    val solution =
      eval1(lams(mkLvl(p.size), mty, AppPruning(m2, p)))(EEmpty)
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

  private def pruneVFlex(m: MetaId, sp: Spine)(implicit psub: PSub): Tm1 =
    debug(s"pruneVFlex ${quote1(VFlex(m, sp), UnfoldNone)(psub.cod)}")
    def go(sp: Spine): (List[Option[PruneTm]], SpinePruneStatus) =
      inline def go1(
          sp: Spine,
          v: Val1,
          inline ptm: Tm1 => PruneTm
      ): (List[Option[PruneTm]], SpinePruneStatus) =
        val (sp2, status) = go(sp)
        forceAll1(v) match
          case VVar1(x) =>
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
        case SId              => (Nil, OKRenaming)
        case SApp(sp, v, i)   => go1(sp, v, t => Prune1(t, i))
        case SMetaApp1(sp, v) => go1(sp, v, t => PruneMeta1(t))
        case SMetaApp0(sp, v) =>
          val (sp2, status) = go(sp)
          forceAll0(v) match
            case VVar0(x) =>
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
            case None                => PESkip
            case Some(Prune1(_, i))  => PEBind1(i)
            case Some(PruneMeta1(_)) => PEBind1(Expl)
            case Some(PruneMeta0(_)) => PEBind0
        }
        pruneMeta(pr, m)(psub.cod)
    sp2.foldRight(Meta(m2)) {
      case (None, t)                => t
      case (Some(Prune1(u, i)), t)  => App1(t, u, i)
      case (Some(PruneMeta1(u)), t) => MetaApp1(t, u)
      case (Some(PruneMeta0(u)), t) => MetaApp0(t, u)
    }

  // partial substitution action
  private def psubst0(v: Val0)(implicit psub: PSub): Tm0 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goClos(c: Clos0) = psubst0(c(VVar0(psub.cod)))(psub.lift0)
    forceMetas0(v) match
      case VVar0(x) =>
        psub.sub.get(x.expose) match
          case None         => throw UnifyError(s"out of scope $x")
          case Some(PS1(_)) => impossible()
          case Some(PS0(v)) => quote0(v, UnfoldNone)(psub.dom)
      case VGlobal0(x) => Global0(x)
      case VLet0(x, ty, v, b) =>
        Let0(x, go1(ty), go0(v), goClos(b))
      case VLetRec(x, ty, v, b) =>
        LetRec(x, go1(ty), goClos(v), goClos(b))
      case VLam0(x, ty, b) => Lam0(x, go1(ty), goClos(b))
      case VApp0(f, a)     => App0(go0(f), go0(a))
      case VSplice(v)      => splice(go1(v))

  private def psubstSp(h: Tm1, sp: Spine)(implicit psub: PSub): Tm1 = sp match
    case SId              => h
    case SApp(sp, v, i)   => App1(psubstSp(h, sp), psubst1(v), i)
    case SMetaApp1(sp, v) => MetaApp1(psubstSp(h, sp), psubst1(v))
    case SMetaApp0(sp, v) => MetaApp0(psubstSp(h, sp), psubst0(v))

  private def psubst1(v: Val1)(implicit psub: PSub): Tm1 =
    inline def go0(v: Val0) = psubst0(v)
    inline def go1(v: Val1) = psubst1(v)
    inline def goSp(h: Tm1, sp: Spine) = psubstSp(h, sp)
    inline def goClos(c: Clos1) = psubst1(c(VVar1(psub.cod)))(psub.lift1)
    inline def goClos0(c: Clos1) = psubst1(c(VVar0(psub.cod)))(psub.lift1)
    forceMetas1(v) match
      case VRigid(HNative(x), sp) => goSp(Native(x), sp)
      case VRigid(HVar(x), sp) =>
        psub.sub.get(x.expose) match
          case None         => throw UnifyError(s"out of scope $x")
          case Some(PS0(_)) => impossible()
          case Some(PS1(v)) => goSp(quote1(v, UnfoldNone)(psub.dom), sp)
      case VFlex(m, sp) =>
        if psub.occ.contains(m) then throw UnifyError(s"occurs error ?$m")
        else pruneVFlex(m, sp)
      case VUnfold(UMeta(m), sp, _)   => goSp(Meta(m), sp)
      case VUnfold(UGlobal(x), sp, _) => goSp(Global1(x), sp)
      case VPi(x, i, ty, b)           => Pi(x, i, go1(ty), goClos(b))
      case VLam1(x, i, ty, b)         => Lam1(x, i, go1(ty), goClos(b))
      case VU0(cv)                    => U0(go1(cv))
      case VU1                        => U1
      case VCV                        => CV
      case VCVV                       => CVV
      case VCVC                       => CVC
      case VFun(pty, cv, rty)         => Fun(go1(pty), go1(cv), go1(rty))
      case VLift(cv, ty)              => Lift(go1(cv), go1(ty))
      case VQuote(tm)                 => quote(go0(tm))
      case VMetaPi1(t, b)             => MetaPi1(go1(t), goClos(b))
      case VMetaPi0(t, b)             => MetaPi0(go1(t), goClos0(b))
      case VMetaLam1(b)               => MetaLam1(goClos(b))
      case VMetaLam0(b)               => MetaLam0(goClos0(b))

  // solving
  private def solve(id: MetaId, sp: Spine, rhs: Val1)(implicit lvl: Lvl): Unit =
    debug(
      s"solve ${quote1(VFlex(id, sp), UnfoldMetas)} := ${quote1(rhs, UnfoldMetas)}"
    )
    solveWithPSub(id, invert(sp), rhs)

  private def solveWithPSub(m: MetaId, iv: (PSub, Option[Pruning]), rhs: Val1)(
      implicit lvl: Lvl
  ) =
    implicit val psub: PSub = iv._1
    debug(
      s"solveWithPSub ?$m ($lvl) := ${quote1(rhs, UnfoldMetas)}"
    )
    val entry = getMetaUnsolved(m)
    val mty = entry.ty
    iv._2.foreach(p => pruneTy(RevPruning(p), mty))
    val rhs2 = psubst1(rhs)(psub.copy(occ = Some(m)))
    debug(s"solution ?$m := $rhs2")
    val rhs2lams = lams(psub.dom, mty, rhs2)
    val sol = eval1(rhs2lams)(EEmpty)
    solveMetaVar(m, sol)

  // unification
  def unify0(a: Val0, b: Val0)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos0, b: Clos0) =
      unify0(a(VVar0(lvl)), b(VVar0(lvl)))(lvl + 1)
    debug(s"unify0 ${quote0(a, UnfoldMetas)} ~ ${quote0(b, UnfoldMetas)}")
    (forceMetas0(a), forceMetas0(b)) match
      case (VVar0(x), VVar0(y)) if x == y => ()
      case (VLet0(_, ty1, v1, b1), VLet0(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); unify0(v1, v2); goClos(b1, b2)
      case (VLetRec(_, ty1, v1, b1), VLetRec(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); goClos(v1, v2); goClos(b1, b2)
      case (VSplice(v1), VSplice(v2))         => unify1(v1, v2)
      case (VLam0(_, _, b1), VLam0(_, _, b2)) => goClos(b1, b2)
      case (VApp0(f1, a1), VApp0(f2, a2))     => unify0(f1, f2); unify0(a1, a2)
      case _ =>
        throw UnifyError(
          s"cannot unify ${quote0(a, UnfoldNone)} ~ ${quote0(b, UnfoldNone)}"
        )

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    inline def go(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine): Unit =
      try
        val data = invert(sp1)
        solveWithPSub(m1, data, VFlex(m2, sp2))
      catch case _: UnifyError => solve(m2, sp2, VFlex(m1, sp1))
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
          case (VVar1(x1), VVar1(x2)) =>
            go(sp1, sp2).map((if x1 == x2 then PEBind1(i) else PESkip) :: _)
          case _ => None
      (sp1, sp2) match
        case (SId, SId) => Some(Nil)

        case (SApp(sp1, t1, i), SApp(sp2, t2, _)) => go1(sp1, sp2, i, t1, t2)

        case (SMetaApp1(sp1, t1), SMetaApp1(sp2, t2)) =>
          go1(sp1, sp2, Expl, t1, t2)
        case (SMetaApp0(sp1, t1), SMetaApp0(sp2, t2)) =>
          (forceAll0(t1), forceAll0(t2)) match
            case (VVar0(x1), VVar0(x2)) =>
              go(sp1, sp2).map((if x1 == x2 then PEBind0 else PESkip) :: _)
            case _ => None
        case _ => impossible()
    go(sp1, sp2) match
      case None => unify1(VFlex(m, sp1), sp1, VFlex(m, sp2), sp2)
      case Some(p) if p.exists(_ == PESkip) => pruneMeta(p, m)
      case _                                => ()

  private def unify1(top1: Val1, sp1: Spine, top2: Val1, sp2: Spine)(implicit
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (SId, SId) => ()
      case (SApp(sp1, a1, _), SApp(sp2, a2, _)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case (SMetaApp0(sp1, a1), SMetaApp0(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify0(a1, a2)
      case (SMetaApp1(sp1, a1), SMetaApp1(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case _ =>
        throw UnifyError(
          s"spine mismatch ${quote1(top1, UnfoldNone)} ~ ${quote1(top2, UnfoldNone)}"
        )

  def unify1(a: Val1, b: Val1)(implicit lvl: Lvl): Unit =
    inline def goClos(a: Clos1, b: Clos1) =
      val v = VVar1(lvl)
      unify1(a(v), b(v))(lvl + 1)
    inline def goClos0(a: Clos1, b: Clos1) =
      val v = VVar0(lvl)
      unify1(a(v), b(v))(lvl + 1)
    debug(s"unify1 ${quote1(a, UnfoldMetas)} ~ ${quote1(b, UnfoldMetas)}")
    (forceMetas1(a), forceMetas1(b)) match
      case (VRigid(x, sp1), VRigid(y, sp2)) if x == y => unify1(a, sp1, b, sp2)

      case (VLift(cv1, ty1), VLift(cv2, ty2)) =>
        unify1(cv1, cv2); unify1(ty1, ty2)
      case (VQuote(v1), VQuote(v2)) => unify0(v1, v2)
      case (VPi(_, i1, ty1, b1), VPi(_, i2, ty2, b2)) if i1 == i2 =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (VMetaPi1(ty1, b1), VMetaPi1(ty2, b2)) =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (VMetaPi0(ty1, b1), VMetaPi0(ty2, b2)) =>
        unify1(ty1, ty2); goClos0(b1, b2)
      case (VFun(t1, cv1, r1), VFun(t2, cv2, r2)) =>
        unify1(t1, t2); unify1(cv1, cv2); unify1(r1, r2)
      case (VU1, VU1)           => ()
      case (VU0(cv1), VU0(cv2)) => unify1(cv1, cv2)
      case (VCV, VCV)           => ()
      case (VCVV, VCVV)         => ()
      case (VCVC, VCVC)         => ()

      case (VLam1(_, _, _, b1), VLam1(_, _, _, b2)) => goClos(b1, b2)
      case (VLam1(_, i, _, b), f) =>
        val v = VVar1(lvl)
        unify1(b(v), vapp1(f, v, i))(lvl + 1)
      case (f, VLam1(_, i, _, b)) =>
        val v = VVar1(lvl)
        unify1(vapp1(f, v, i), b(v))(lvl + 1)

      case (VMetaLam1(b1), VMetaLam1(b2)) => goClos(b1, b2)
      case (VMetaLam0(b1), VMetaLam0(b2)) => goClos0(b1, b2)
      case (VMetaLam1(b), f) =>
        val v = VVar1(lvl)
        unify1(b(v), vmetaapp1(f, v))(lvl + 1)
      case (VMetaLam0(b), f) =>
        val v = VVar0(lvl)
        unify1(b(v), vmetaapp0(f, v))(lvl + 1)
      case (f, VMetaLam1(b)) =>
        val v = VVar1(lvl)
        unify1(vmetaapp1(f, v), b(v))(lvl + 1)
      case (f, VMetaLam0(b)) =>
        val v = VVar0(lvl)
        unify1(vmetaapp0(f, v), b(v))(lvl + 1)

      case (VFlex(id1, sp1), VFlex(id2, sp2)) =>
        if id1 == id2 then intersect(id1, sp1, sp2)
        else flexFlex(id1, sp1, id2, sp2)
      case (VFlex(id, sp), v) => solve(id, sp, v)
      case (v, VFlex(id, sp)) => solve(id, sp, v)

      case (top1 @ VUnfold(h1, sp1, v1), top2 @ VUnfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then throw UnifyError("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnifyError => unify1(v1(), v2())
      case (VUnfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, VUnfold(_, _, v2)) => unify1(v1, v2())

      case _ =>
        throw UnifyError(
          s"cannot unify ${quote1(a, UnfoldNone)} ~ ${quote1(b, UnfoldNone)}"
        )
