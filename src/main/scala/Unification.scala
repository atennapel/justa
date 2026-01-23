import Common.*
import Common.Icit.*
import Core.{
  Spine,
  VTy,
  Ty,
  Head,
  Clos0,
  Clos1,
  Env,
  UnfoldHead,
  Val1 as V,
  Val0 as V0,
  Tm1 as T1,
  Tm0 as T0,
  Cases0,
  Cases1,
  ClosCases0,
  ClosCases1,
  ClosRec
}
import Evaluation.*
import Debug.debug

import scala.collection.immutable.IntMap
import scala.annotation.tailrec

object Unification:
  class UnifyError(msg: String) extends RuntimeException(msg)

  private inline def err(msg: String): Nothing =
    throw new UnifyError(msg)

  // partial substitution
  private enum PSEntry:
    case PS0(value: V0)
    case PS1(value: V)
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
        sub + (cod.expose -> PS1(V.Var(dom)))
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

  private def invert1(v: V, rhs: V, i: Icit, data: Invert): Invert =
    forceAll1(v) match
      case V.Var(x) =>
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
      case V.Quote(v) => invert0(v, vsplice(rhs), i, data)
      case _          => err("spine error")

  private def invert0(v: V0, rhs: V0, i: Icit, data: Invert): Invert =
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
      case V0.Splice(v) => invert1(v, vquote(rhs), i, data)
      case _            => err("spine error")

  private def invert(sp: Spine)(using lvl: Lvl): (PSub, Option[Pruning]) =
    def go(sp: Spine): Invert =
      sp match
        case Spine.Empty => (lvl0, Set.empty, IntMap.empty, Nil, true)
        case Spine.App(sp, v, i) =>
          val data = go(sp)
          invert1(v, V.Var(data._1), i, data)
        case Spine.MetaApp0(sp, v) =>
          val data = go(sp)
          invert0(v, V0.Var(data._1), Expl, data)
        case Spine.MetaApp1(sp, v) =>
          val data = go(sp)
          invert1(v, V.Var(data._1), Expl, data)
        case Spine.Proj(_, p)               => err(s"projection in spine: .$p")
        case Spine.ElimId(_, _, _, _, _, _) => err(s"elimId in spine")
        case Spine.FixIx(_, _, _, _, _, _)  => err(s"fixIx in spine")
        case Spine.Case(_, _)               => err(s"case in spine")
    val (dom, _, sub, pr, isLinear) = go(sp)
    (PSub(None, dom, lvl, sub), if isLinear then None else Some(pr))

  // pruning
  private def lams(l1: Lvl, ty: VTy, b: T1): T1 =
    def go(l2: Lvl, ty: VTy): T1 =
      if l1 == l2 then b
      else
        forceAll1(ty) match
          case t @ V.Pi(x, i, a, c) =>
            T1.Lam(
              x,
              i,
              readback1(a)(using l2, UnfoldOption.None),
              go(l2 + 1, c(V.Var(l2)))
            )
          case V.MetaPi1(t, c) =>
            T1.MetaLam1(go(l2 + 1, c(V.Var(l2))))
          case V.MetaPi0(t, c) =>
            T1.MetaLam0(go(l2 + 1, c(V0.Var(l2))))
          case _ => impossible()
    go(lvl0, ty)

  private def pruneTy(p: RevPruning, ty: VTy): Ty =
    def go(p: Pruning, psub: PSub, ty: VTy): Ty = (p, forceAll1(ty)) match
      case (Nil, ty) => psubst1(ty)(using psub)

      case (PruneEntry.Skip :: p, V.Pi(x, i, a, b)) =>
        go(p, psub.skip, b(V.Var(psub.cod)))
      case (PruneEntry.Bind1(_) :: p, V.Pi(x, i, a, b)) =>
        T1.Pi(
          x,
          i,
          psubst1(a)(using psub),
          go(p, psub.lift1, b(V.Var(psub.cod)))
        )

      case (PruneEntry.Skip :: p, V.MetaPi1(a, b)) =>
        go(p, psub.skip, b(V.Var(psub.cod)))
      case (PruneEntry.Skip :: p, V.MetaPi0(a, b)) =>
        go(p, psub.skip, b(V0.Var(psub.cod)))
      case (PruneEntry.Bind1(_) :: p, V.MetaPi1(a, b)) =>
        T1.MetaPi1(
          psubst1(a)(using psub),
          go(p, psub.lift1, b(V.Var(psub.cod)))
        )
      case (PruneEntry.Bind0 :: p, V.MetaPi0(a, b)) =>
        T1.MetaPi0(
          psubst1(a)(using psub),
          go(p, psub.lift0, b(V0.Var(psub.cod)))
        )

      case _ => impossible()
    go(p.expose, PSub.empty, ty)

  private def solveMetaVar(m: MetaId, solution: V) = {
    if (State.isMetaFrozen(m))
      err(s"trying to solve frozen meta ?$m")
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

  private enum SpinePruneStatus derives CanEqual:
    case OKRenaming
    case OKNonRenaming
    case NeedsPruning
  import SpinePruneStatus.*

  private enum PruneTm:
    case Prune1(tm: T1, i: Icit)
    case PruneMeta1(tm: T1)
    case PruneMeta0(tm: T0)
  import PruneTm.*

  private def pruneVFlex(m: MetaId, sp: Spine)(using psub: PSub): T1 =
    debug(
      s"pruneVFlex ${readback1(V.Flex(m, sp))(using psub.cod, UnfoldOption.None)}"
    )
    def go(sp: Spine): (List[Option[PruneTm]], SpinePruneStatus) =
      inline def go1(
          sp: Spine,
          v: V,
          inline ptm: T1 => PruneTm
      ): (List[Option[PruneTm]], SpinePruneStatus) =
        val (sp2, status) = go(sp)
        forceAll1(v) match
          case V.Var(x) =>
            (psub.sub.get(x.expose), status) match
              case (Some(PS1(_)), _) => (Some(ptm(psubst1(v))) :: sp2, status)
              case (Some(PS0(v)), _) => impossible()
              case (None, OKNonRenaming) => err("failed to prune")
              case _                     => (None :: sp2, NeedsPruning)
          case t =>
            status match
              case NeedsPruning => err("failed to prune")
              case _            => (Some(ptm(psubst1(t))) :: sp2, OKNonRenaming)
      sp match
        case Spine.Empty      => (Nil, OKRenaming)
        case Spine.Proj(_, p) => err(s"cannot prune because of projection .$p")
        case Spine.Case(_, _) => err(s"cannot prune because of match")
        case Spine.ElimId(_, _, _, _, _, _) =>
          err(s"cannot prune because of elimId")
        case Spine.FixIx(_, _, _, _, _, _) =>
          err(s"cannot prune because of fixIx")
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
                  err("failed to prune")
                case _ => (None :: sp2, NeedsPruning)
            case t =>
              status match
                case NeedsPruning => err("failed to prune")
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

  private def splitSpine(sp: Spine): (Spine, Spine) =
    def go(sp: Spine): Option[(Spine, Spine)] = sp match
      case Spine.Empty         => None
      case Spine.App(sp, a, i) => go(sp).map((l, r) => (l, Spine.App(r, a, i)))
      case Spine.MetaApp0(sp, a) =>
        go(sp).map((l, r) => (l, Spine.MetaApp0(r, a)))
      case Spine.MetaApp1(sp, a) =>
        go(sp).map((l, r) => (l, Spine.MetaApp1(r, a)))
      case Spine.Proj(sp, p) =>
        go(sp)
          .orElse(Some((sp, Spine.Empty)))
          .map((l, r) => (l, Spine.Proj(r, p)))
      case Spine.ElimId(sp, a, x, pp, h, y) =>
        go(sp)
          .orElse(Some((sp, Spine.Empty)))
          .map((l, r) => (l, Spine.ElimId(r, a, x, pp, h, y)))
      case Spine.FixIx(sp, ii, a, b, f, i) =>
        go(sp)
          .orElse(Some((sp, Spine.Empty)))
          .map((l, r) => (l, Spine.FixIx(r, ii, a, b, f, i)))
      case Spine.Case(sp, cs) =>
        go(sp)
          .orElse(Some((sp, Spine.Empty)))
          .map((l, r) => (l, Spine.Case(r, cs)))
    go(sp).fold((sp, Spine.Empty))(x => x)

  // partial substitution action
  private def psubst0(v: V0)(using psub: PSub): T0 =
    inline def go0(v: V0) = psubst0(v)
    inline def go1(v: V) = psubst1(v)
    inline def goClos(c: Clos0) = psubst0(c(V0.Var(psub.cod)))(using psub.lift0)
    forceMetas0(v) match
      case V0.Var(x) =>
        psub.sub.get(x.expose) match
          case None         => err(s"out of scope $x")
          case Some(PS1(_)) => impossible()
          case Some(PS0(v)) => readback0(v)(using psub.dom, UnfoldOption.None)
      case V0.Global(m, x)        => T0.Global(m, x)
      case V0.IntLit(v)           => T0.IntLit(v)
      case V0.Let(x, ty, v, b)    => T0.Let(x, go1(ty), go0(v), goClos(b))
      case V0.LetRec(x, ty, v, b) => T0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case V0.Lam(x, ty, b)       => T0.Lam(x, go1(ty), goClos(b))
      case V0.App(f, a)           => T0.App(go0(f), go0(a))
      case V0.If(ty, c, t, f)     => T0.If(go1(ty), go0(c), go0(t), go0(f))
      case V0.Splice(v)           => go1(v).splice
      case V0.Proj(ty, s, p)      => T0.Proj(go1(ty), go0(s), p)
      case V0.RecordCon(ty, fs)   => T0.RecordCon(go1(ty), fs.map(t => go0(t)))
      case V0.Case(rty, dty, s, cs) =>
        def addParams(
            ps: List[(Bind, Ty)]
        )(using psub: PSub, env: Env): (PSub, Env) =
          @tailrec
          def go(n: Int, psub: PSub, env: Env): (PSub, Env) =
            n match
              case 0 => (psub, env)
              case n => go(n - 1, psub.lift0, Env.Ext0(env, V0.Var(psub.cod)))
          go(ps.size, psub, env)
        def goCases(cs: Cases0)(using env: Env): Cases0 =
          cs match
            case Cases0.Ext(x, ps, b, r) =>
              val (innerpsub, innerenv) = addParams(ps)
              val nps = ps.map((x, ty) => (x, go1(eval1(ty))))
              val rb = psubst0(eval0(b)(using innerenv))(using innerpsub)
              Cases0.Ext(x, nps, rb, goCases(r))
            case Cases0.Otherwise(b) => Cases0.Otherwise(go0(eval0(b)))
            case Cases0.Empty        => Cases0.Empty
        T0.Case(
          go1(rty),
          go1(dty),
          go0(s),
          goCases(cs.cases)(using cs.env)
        )

  private def psubstSpine(h: T1, sp: Spine)(using psub: PSub): T1 =
    sp match
      case Spine.Empty           => h
      case Spine.App(sp, v, i)   => T1.App(psubstSpine(h, sp), psubst1(v), i)
      case Spine.Proj(sp, p)     => T1.Proj(psubstSpine(h, sp), p)
      case Spine.MetaApp1(sp, v) => T1.MetaApp1(psubstSpine(h, sp), psubst1(v))
      case Spine.MetaApp0(sp, v) => T1.MetaApp0(psubstSpine(h, sp), psubst0(v))
      case Spine.ElimId(sp, a, x, pp, hh, y) =>
        val p = psubstSpine(h, sp)
        T1.App(
          T1.App(
            T1.App(
              T1.App(
                T1.App(
                  T1.App(T1.Prim(Primitive.ElimId), psubst1(a), Impl),
                  psubst1(x),
                  Impl
                ),
                psubst1(pp),
                Expl
              ),
              psubst1(hh),
              Expl
            ),
            psubst1(y),
            Impl
          ),
          p,
          Expl
        )
      case Spine.FixIx(sp, ii, a, b, f, i) =>
        val x = psubstSpine(h, sp)
        T1.App(
          T1.App(
            T1.App(
              T1.App(
                T1.App(
                  T1.App(T1.Prim(Primitive.FixIx), psubst1(ii), Impl),
                  psubst1(a),
                  Impl
                ),
                psubst1(b),
                Impl
              ),
              psubst1(f),
              Expl
            ),
            psubst1(i),
            Impl
          ),
          x,
          Expl
        )
      case Spine.Case(sp, cs) =>
        def addParams(
            ps: List[(Bind, Icit, Ty)]
        )(using psub: PSub, env: Env): (PSub, Env, List[(Bind, Icit, Ty)]) =
          ps match
            case Nil => (psub, env, Nil)
            case (x, i, ty) :: rest =>
              val ety = psubst1(eval1(ty))
              val (npsub, nenv, nps) = addParams(rest)(using
                psub.lift1,
                Env.Ext1(env, V.Var(psub.cod))
              )
              (npsub, nenv, (x, i, ety) :: nps)
        def go(cs: Cases1)(using env: Env): Cases1 =
          cs match
            case Cases1.Ext(x, ps, b, r) =>
              val (innerpsub, innerenv, nps) = addParams(ps)(using env = env)
              val rb = psubst1(eval1(b)(using innerenv))(using innerpsub)
              Cases1.Ext(x, nps, rb, go(r))
            case Cases1.Otherwise(b) =>
              Cases1.Otherwise(psubst1(eval1(b)(using env)))
            case Cases1.Empty => Cases1.Empty
        T1.Case(psubstSpine(h, sp), go(cs.cases)(using cs.env))

  private def psubst1(v: V)(using psub: PSub): T1 =
    inline def go0(v: V0) = psubst0(v)
    inline def go1(v: V) = psubst1(v)
    inline def goSp(h: T1, sp: Spine) = psubstSpine(h, sp)
    inline def goClos(c: Clos1) = psubst1(c(V.Var(psub.cod)))(using psub.lift1)
    inline def goClos0(c: Clos1) =
      psubst1(c(V0.Var(psub.cod)))(using psub.lift1)
    def goRec(c: ClosRec): AssocBind[Ty] =
      def go(env: Env, psub: PSub, fs: AssocBind[Ty]): AssocBind[Ty] =
        fs match
          case Nil => Nil
          case (x, ty) :: rest =>
            val qty = psubst1(eval1(ty)(using env))(using psub)
            (x, qty) :: go(Env.Ext1(env, V.Var(psub.cod)), psub.lift1, rest)
      go(c.env, psub, c.fields)
    forceMetas1(v) match
      case V.Rigid(Head.Prim(p), sp)         => goSp(T1.Prim(p), sp)
      case V.Rigid(Head.TypeCon1(m, x), sp)  => goSp(T1.TypeCon1(m, x), sp)
      case V.Rigid(Head.Con1(m, dx, cx), sp) => goSp(T1.Con1(m, dx, cx), sp)
      case V.Rigid(Head.TypeCon0(m, x), sp)  => goSp(T1.TypeCon0(m, x), sp)
      case V.Rigid(Head.Con0(m, dx, cx), sp) => goSp(T1.Con0(m, dx, cx), sp)
      case V.Rigid(Head.Var(x), sp) =>
        psub.sub.get(x.expose) match
          case None         => err(s"out of scope $x")
          case Some(PS0(_)) => impossible()
          case Some(PS1(v)) =>
            goSp(readback1(v)(using psub.dom, UnfoldOption.None), sp)
      case V.Flex(m, sp) if psub.occ.contains(m) => err(s"occurs error ?$m")
      case V.Flex(m, sp) =>
        val (inner, outer) = splitSpine(sp)
        goSp(pruneVFlex(m, inner), outer)
      case V.Unfold(UnfoldHead.Global(m, x, v), sp, _) =>
        goSp(T1.Global(m, x, v), sp)
      case V.Pi(x, i, ty, b)   => T1.Pi(x, i, go1(ty), goClos(b))
      case V.Lam(x, i, ty, b)  => T1.Lam(x, i, go1(ty), goClos(b))
      case V.Fun(pty, cv, rty) => T1.Fun(go1(pty), go1(cv), go1(rty))
      case V.Lift(cv, ty)      => T1.Lift(go1(cv), go1(ty))
      case V.Quote(tm)         => go0(tm).quote
      case V.RecordTy1(fs)     => T1.RecordTy1(goRec(fs))
      case V.RecordTy0(fs)     => T1.RecordTy0(fs.map((x, t) => (x, go1(t))))
      case V.RecordCon(fs)     => T1.RecordCon(fs.map(t => go1(t)))
      case V.MetaPi1(t, b)     => T1.MetaPi1(go1(t), goClos(b))
      case V.MetaPi0(t, b)     => T1.MetaPi0(go1(t), goClos0(b))
      case V.MetaLam1(b)       => T1.MetaLam1(goClos(b))
      case V.MetaLam0(b)       => T1.MetaLam0(goClos0(b))

  // solving
  private def solve(m: MetaId, sp: Spine, rhs: V)(using lvl: Lvl): Unit =
    debug(s"solve ${readback1m(V.Flex(m, sp))} := ${readback1m(rhs)}")
    val (inner, outer) = splitSpine(sp)
    val psub = invert(sp)
    if outer.isEmpty then solveWithPSub(m, psub, rhs)
    else
      @tailrec
      def go(x: Head, a: Spine, b: Spine): Unit =
        (a, b) match
          case (Spine.Empty, b) => solveWithPSub(m, psub, V.Rigid(x, b))
          case (Spine.App(s1, a, _), Spine.App(s2, b, _)) =>
            unify1(a, b); go(x, s1, s2)
          case (Spine.MetaApp1(s1, a), Spine.MetaApp1(s2, b)) =>
            unify1(a, b); go(x, s1, s2)
          case (Spine.MetaApp0(s1, a), Spine.MetaApp0(s2, b)) =>
            unify0(a, b); go(x, s1, s2)
          case (Spine.Proj(s1, p1), Spine.Proj(s2, p2)) if p1.ix == p2.ix =>
            go(x, s1, s2)
          case (
                Spine.ElimId(s1, a1, x1, pp1, h1, y1),
                Spine.ElimId(s2, a2, x2, pp2, h2, y2)
              ) =>
            unify1(a1, a2); unify1(x1, x2); unify1(pp1, pp2); unify1(h1, h2)
            unify1(y1, y2)
            go(x, s1, s2)
          case (
                Spine.FixIx(s1, a1, x1, pp1, h1, y1),
                Spine.FixIx(s2, a2, x2, pp2, h2, y2)
              ) =>
            unify1(a1, a2); unify1(x1, x2); unify1(pp1, pp2); unify1(h1, h2)
            unify1(y1, y2)
            go(x, s1, s2)
          case (Spine.Case(s1, a), Spine.Case(s2, b)) =>
            val env1 = a.env
            val env2 = b.env
            @tailrec
            def goCases(a: Cases1, b: Cases1): Unit =
              (a, b) match
                case (Cases1.Empty, Cases1.Empty) => ()
                case (Cases1.Otherwise(b1), Cases1.Otherwise(b2)) =>
                  unify1(eval1(b1)(using env1), eval1(b2)(using env2))
                case (
                      Cases1.Ext(cx1, ps1, b1, rest1),
                      Cases1.Ext(cx2, ps2, b2, rest2)
                    ) if cx1 == cx2 && ps1.size == ps2.size =>
                  val (innerlvl, innerenv1) =
                    addParams(ps1.size)(using env = env1)
                  val (_, innerenv2) = addParams(ps2.size)(using env = env2)
                  val vb1 = eval1(b1)(using innerenv1)
                  val vb2 = eval1(b2)(using innerenv2)
                  unify1(vb1, vb2)(using innerlvl)
                  goCases(rest1, rest2)
                case _ =>
                  err(
                    s"cannot unify cases: case mismatch"
                  )
            goCases(a.cases, b.cases)
            go(x, s1, s2)
          case _ => err(s"solve ?$m, spine mismatch")
      forceAll1(rhs) match
        case V.Rigid(x, rhsSp) => go(x, outer, rhsSp)
        case _                 => err(s"solve ?$m, invalid spine")

  private def solveWithPSub(m: MetaId, iv: (PSub, Option[Pruning]), rhs: V)(
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
  private def unify0(a: ClosCases0, b: ClosCases0, topa: V0, topb: V0)(using
      lvl: Lvl
  ): Unit =
    val env1 = a.env
    val env2 = b.env
    @tailrec
    def go(a: Cases0, b: Cases0): Unit =
      (a, b) match
        case (Cases0.Empty, Cases0.Empty) => ()
        case (Cases0.Otherwise(b1), Cases0.Otherwise(b2)) =>
          unify0(eval0(b1)(using env1), eval0(b2)(using env2))
        case (Cases0.Ext(cx1, ps1, b1, rest1), Cases0.Ext(cx2, ps2, b2, rest2))
            if cx1 == cx2 && ps1.size == ps2.size =>
          val (innerlvl, innerenv1) = addParams(ps1.size)(using env = env1)
          val (_, innerenv2) = addParams(ps2.size)(using env = env2)
          val vb1 = eval0(b1)(using innerenv1)
          val vb2 = eval0(b2)(using innerenv2)
          unify0(vb1, vb2)(using innerlvl)
          go(rest1, rest2)
        case _ =>
          err(
            s"cannot unify ${readback0n(topa)} ~ ${readback0n(topb)}: case mismatch"
          )
    go(a.cases, b.cases)

  private def unify0(a: V0, b: V0)(using lvl: Lvl): Unit =
    inline def goClos(a: Clos0, b: Clos0) =
      unify0(a(V0.Var(lvl)), b(V0.Var(lvl)))(using lvl + 1)
    debug(s"unify0 ${readback0m(a)} ~ ${readback0m(b)}")
    (forceMetas0(a), forceMetas0(b)) match
      case (V0.Var(x), V0.Var(y)) if x == y                           => ()
      case (V0.Global(m1, x), V0.Global(m2, y)) if m1 == m2 && x == y => ()
      case (V0.IntLit(x), V0.IntLit(y)) if x == y                     => ()
      case (V0.Let(_, ty1, v1, b1), V0.Let(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); unify0(v1, v2); goClos(b1, b2)
      case (V0.LetRec(_, ty1, v1, b1), V0.LetRec(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); goClos(v1, v2); goClos(b1, b2)
      case (V0.Splice(v1), V0.Splice(v2))       => unify1(v1, v2)
      case (V0.Lam(_, _, b1), V0.Lam(_, _, b2)) => goClos(b1, b2)
      case (V0.App(f1, a1), V0.App(f2, a2)) => unify0(f1, f2); unify0(a1, a2)
      case (V0.If(ty1, c1, t1, f1), V0.If(ty2, c2, t2, f2)) =>
        unify1(ty1, ty2); unify0(c1, c2); unify0(t1, t2); unify0(f1, f2)
      case (V0.Proj(t1, s1, p1), V0.Proj(t2, s2, p2)) if p1.ix == p2.ix =>
        unify1(t1, t2); unify0(s1, s2)
      case (V0.RecordCon(ty1, fs1), V0.RecordCon(ty2, fs2)) =>
        unify1(ty1, ty2); fs1.zip(fs2).foreach((a, b) => unify0(a, b))
      case (V0.Case(rty1, dty1, s1, cases1), V0.Case(rty2, dty2, s2, cases2)) =>
        unify1(rty1, rty2); unify1(dty1, dty2); unify0(s1, s2)
        unify0(cases1, cases2, a, b)
      case _ => err(s"cannot unify ${readback0n(a)} ~ ${readback0n(b)}")

  private def flexFlex(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    inline def go(m1: MetaId, sp1: Spine, m2: MetaId, sp2: Spine): Unit =
      try
        val (sp, outer) = splitSpine(sp1)
        if !outer.isEmpty then err(s"flex flex ?$m1, invalid spine")
        solveWithPSub(m1, invert(sp), V.Flex(m2, sp2))
      catch case _: UnifyError => solve(m2, sp2, V.Flex(m1, sp1))
    if sp1.size < sp2.size then go(m2, sp2, m1, sp1) else go(m1, sp1, m2, sp2)

  private def intersect(m: MetaId, sp1: Spine, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    def go(sp1: Spine, sp2: Spine): Option[Pruning] =
      inline def go1(
          sp1: Spine,
          sp2: Spine,
          i: Icit,
          t1: V,
          t2: V
      ): Option[Pruning] =
        (forceAll1(t1), forceAll1(t2)) match
          case (V.Var(x1), V.Var(x2)) =>
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
        case (Spine.Proj(_, _), Spine.Proj(_, _)) => None
        case (Spine.ElimId(_, _, _, _, _, _), Spine.ElimId(_, _, _, _, _, _)) =>
          None
        case (Spine.FixIx(_, _, _, _, _, _), Spine.FixIx(_, _, _, _, _, _)) =>
          None
        case (Spine.Case(_, _), Spine.Case(_, _)) => None
        case _                                    => impossible()
    val (sp1inner, outer1) = splitSpine(sp1)
    val (sp2inner, outer2) = splitSpine(sp2)
    if outer1.isEmpty && outer2.isEmpty then
      go(sp1inner, sp2inner) match
        case None =>
          unify1(V.Flex(m, sp1inner), sp1inner, V.Flex(m, sp2inner), sp2inner)
        case Some(p) if p.exists(_ == PruneEntry.Skip) => pruneMeta(p, m)
        case _                                         => ()
    else unify1(V.Flex(m, sp1inner), sp1inner, V.Flex(m, sp2inner), sp2inner)

  private def unify1(a: ClosCases1, b: ClosCases1, topa: V, topb: V)(using
      lvl: Lvl
  ): Unit =
    val env1 = a.env
    val env2 = b.env
    @tailrec
    def go(a: Cases1, b: Cases1): Unit =
      (a, b) match
        case (Cases1.Empty, Cases1.Empty) => ()
        case (Cases1.Otherwise(b1), Cases1.Otherwise(b2)) =>
          unify1(eval1(b1)(using env1), eval1(b2)(using env2))
        case (Cases1.Ext(cx1, ps1, b1, rest1), Cases1.Ext(cx2, ps2, b2, rest2))
            if cx1 == cx2 && ps1.size == ps2.size =>
          val (innerlvl, innerenv1) = addParams(ps1.size)(using env = env1)
          val (_, innerenv2) = addParams(ps2.size)(using env = env2)
          val vb1 = eval1(b1)(using innerenv1)
          val vb2 = eval1(b2)(using innerenv2)
          unify1(vb1, vb2)(using innerlvl)
          go(rest1, rest2)
        case _ =>
          err(
            s"cannot unify ${readback1n(topa)} ~ ${readback1n(topb)}: case mismatch"
          )
    go(a.cases, b.cases)

  private def unify1(top1: V, sp1: Spine, top2: V, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty) => ()
      case (Spine.App(sp1, a1, _), Spine.App(sp2, a2, _)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case (Spine.Proj(sp1, p1), Spine.Proj(sp2, p2)) if p1.ix == p2.ix =>
        unify1(top1, sp1, top2, sp2)
      case (Spine.MetaApp0(sp1, a1), Spine.MetaApp0(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify0(a1, a2)
      case (Spine.MetaApp1(sp1, a1), Spine.MetaApp1(sp2, a2)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case (
            Spine.ElimId(sp1, a1, x1, pp1, h1, y1),
            Spine.ElimId(sp2, a2, x2, pp2, h2, y2)
          ) =>
        unify1(top1, sp1, top2, sp2)
        unify1(a1, a2); unify1(x1, x2); unify1(pp1, pp2); unify1(h1, h2)
        unify1(y1, y2)
      case (
            Spine.FixIx(sp1, a1, x1, pp1, h1, y1),
            Spine.FixIx(sp2, a2, x2, pp2, h2, y2)
          ) =>
        unify1(top1, sp1, top2, sp2)
        unify1(a1, a2); unify1(x1, x2); unify1(pp1, pp2); unify1(h1, h2)
        unify1(y1, y2)
      case (Spine.Case(sp1, cs1), Spine.Case(sp2, cs2)) =>
        unify1(top1, sp1, top2, sp2);
        unify1(cs1, cs1, top1, top2)
      case _ => err(s"spine mismatch ${readback1n(top1)} ~ ${readback1n(top2)}")

  private inline def unfoldHeadEquals(a: UnfoldHead, b: UnfoldHead): Boolean =
    (a, b) match
      case (UnfoldHead.Global(m1, x, _), UnfoldHead.Global(m2, y, _)) =>
        m1 == m2 && x == y

  def unify1(a: V, b: V)(using lvl: Lvl): Unit =
    inline def goClos(a: Clos1, b: Clos1) =
      val v = V.Var(lvl)
      unify1(a(v), b(v))(using lvl + 1)
    inline def goClos0(a: Clos1, b: Clos1) =
      val v = V0.Var(lvl)
      unify1(a(v), b(v))(using lvl + 1)
    def goRec(f1: ClosRec, f2: ClosRec): Unit =
      def go(
          lvl: Lvl,
          env1: Env,
          f1: AssocBind[Ty],
          env2: Env,
          f2: AssocBind[Ty]
      ): Unit =
        (f1, f2) match
          case (Nil, Nil) => ()
          case ((x1, ty1) :: rest1, (x2, ty2) :: rest2) if x1 == x2 =>
            unify1(eval1(ty1)(using env1), eval1(ty2)(using env2))(using lvl)
            val v = V.Var(lvl)
            go(lvl + 1, Env.Ext1(env1, v), rest1, Env.Ext1(env2, v), rest2)
          case _ => err("cannot unify meta record types")
      go(lvl, f1.env, f1.fields, f2.env, f2.fields)
    debug(s"unify1 ${readback1m(a)} ~ ${readback1m(b)}")
    (forceMetas1(a), forceMetas1(b)) match
      case (V.Rigid(x, sp1), V.Rigid(y, sp2)) if x == y =>
        unify1(a, sp1, b, sp2)

      case (V.Lift(cv1, ty1), V.Lift(cv2, ty2)) =>
        unify1(cv1, cv2); unify1(ty1, ty2)
      case (V.Quote(v1), V.Quote(v2)) => unify0(v1, v2)
      case (V.Pi(_, i1, ty1, b1), V.Pi(_, i2, ty2, b2)) if i1 == i2 =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (V.MetaPi1(ty1, b1), V.MetaPi1(ty2, b2)) =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (V.MetaPi0(ty1, b1), V.MetaPi0(ty2, b2)) =>
        unify1(ty1, ty2); goClos0(b1, b2)
      case (V.Fun(t1, cv1, r1), V.Fun(t2, cv2, r2)) =>
        unify1(t1, t2); unify1(cv1, cv2); unify1(r1, r2)
      case (V.RecordTy1(f1), V.RecordTy1(f2)) => goRec(f1, f2)
      case (V.RecordTy0(f1), V.RecordTy0(f2)) if f1.map(_._1) == f2.map(_._1) =>
        f1.zip(f2).foreach { case ((_, t1), (_, t2)) => unify1(t1, t2) }

      case (V.Lam(_, _, _, b1), V.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (V.Lam(_, i, _, b), f) =>
        val v = V.Var(lvl)
        unify1(b(v), vapp(f, v, i.toIcit))(using lvl + 1)
      case (f, V.Lam(_, i, _, b)) =>
        val v = V.Var(lvl)
        unify1(vapp(f, v, i.toIcit), b(v))(using lvl + 1)

      case (V.MetaLam1(b1), V.MetaLam1(b2)) => goClos(b1, b2)
      case (V.MetaLam0(b1), V.MetaLam0(b2)) => goClos0(b1, b2)
      case (V.MetaLam1(b), f) =>
        val v = V.Var(lvl)
        unify1(b(v), vmetaapp1(f, v))(using lvl + 1)
      case (V.MetaLam0(b), f) =>
        val v = V0.Var(lvl)
        unify1(b(v), vmetaapp0(f, v))(using lvl + 1)
      case (f, V.MetaLam1(b)) =>
        val v = V.Var(lvl)
        unify1(vmetaapp1(f, v), b(v))(using lvl + 1)
      case (f, V.MetaLam0(b)) =>
        val v = V0.Var(lvl)
        unify1(vmetaapp0(f, v), b(v))(using lvl + 1)

      case (V.RecordCon(f1), V.RecordCon(f2)) if f1.size == f2.size =>
        f1.zip(f2).foreach((a, b) => unify1(a, b))
      case (V.RecordCon(fs), v) =>
        fs.zipWithIndex.foreach((f, ix) => unify1(f, vprojIx(v, ix)))
      case (v, V.RecordCon(fs)) =>
        fs.zipWithIndex.foreach((f, ix) => unify1(vprojIx(v, ix), f))

      case (V.Flex(id1, sp1), V.Flex(id2, sp2)) =>
        if id1 == id2 then intersect(id1, sp1, sp2)
        else flexFlex(id1, sp1, id2, sp2)
      case (V.Flex(id, sp), v) => solve(id, sp, v)
      case (v, V.Flex(id, sp)) => solve(id, sp, v)

      case (top1 @ V.Unfold(h1, sp1, v1), top2 @ V.Unfold(h2, sp2, v2)) =>
        try
          if !unfoldHeadEquals(h1, h2) then err("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnifyError => unify1(v1(), v2())
      case (V.Unfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, V.Unfold(_, _, v2)) => unify1(v1, v2())

      case _ => err(s"cannot unify ${readback1n(a)} ~ ${readback1n(b)}")
