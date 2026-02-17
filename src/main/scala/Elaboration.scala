import Common.*
import Common.Icit.*
import Common.Bind.*
import Core.{
  VTy,
  Ty,
  Clos1,
  Locals,
  Env,
  Val1 as V,
  Cases0,
  Cases1,
  ProjType,
  ClosRec,
  Tm0,
  Tm1
}
import Evaluation.*
import Surface.Tm as S
import Surface.ArgInfo
import Surface.PiIcit
import Surface.ImplMode
import Ctx.NameInfo
import State.GlobalEntry
import Debug.debug

import scala.annotation.tailrec

object Elaboration:
  private val AutoSearchLimit = 1000
  private val AutoSearchRetryLimit = 1000

  final class ElaborateError(val pos: PosInfo, val module: Name, msg: String)
      extends Exception(msg)

  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborateError(ctx.pos, State.currentModule, msg)

  private enum Infer:
    case Infer0(tm: Tm0, ty: VTy, cv: VTy)
    case Infer1(tm: Tm1, ty: VTy)
  import Infer.*

  // unification
  private def unify(a: VTy, b: VTy)(using ctx: Ctx): Unit =
    debug(s"unify ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}")
    try Unification.unify1(a, b)(using ctx.lvl)
    catch
      case uerr: Unification.UnifyError =>
        err(
          s"failed to unify ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}: ${uerr.getMessage}"
        )

  // metas
  private def closeTy(ty: Ty)(using ctx: Ctx): Ty =
    def go(ls: Locals, xs: List[Bind], ty: Ty): Ty = (ls, xs) match
      case (Locals.Empty, Nil) => ty
      case (Locals.Def(ls, a, v), Bind.DoBind(x) :: xs) =>
        go(ls, xs, Tm1.Let(x, a, v, ty))
      case (Locals.Bind0(ls, a, cv), x :: xs) => go(ls, xs, Tm1.MetaPi0(a, ty))
      case (Locals.Bind1(ls, a), x :: xs)     => go(ls, xs, Tm1.MetaPi1(a, ty))
      case _                                  => impossible()
    go(ctx.locals, ctx.binds, ty)

  private def freshMetaId(ty: VTy)(using ctx: Ctx): MetaId =
    val qa = closeTy(ctx.readback1(ty, UnfoldOption.None))
    debug(s"freshMetaId : ${ctx.pretty1(qa)}")
    val vqa = eval1(qa)(using Env.Empty)
    val m = State.newMeta(Set.empty, vqa)
    debug(s"freshMetaId ?$m : ${ctx.pretty1(ty)}")
    m

  private inline def freshMeta(ty: VTy)(using ctx: Ctx): Tm1 =
    Tm1.AppPruning(freshMetaId(ty), ctx.pruning)

  private inline def freshCV()(using ctx: Ctx): Tm1 = freshMeta(V.CV)

  // autos
  private def checkAutoType(ty: VTy)(using
      ctx: Ctx
  ): (Name, Name, List[(V, Icit)]) =
    forceAll1(ty) match
      case V.TypeCon1(m, dx, args) => (m, dx, args)
      case _ => err(s"invalid auto type: ${ctx.pretty1(ty)}")

  private def checkAutoDef(ty: VTy)(using
      ctx: Ctx
  ): (Name, Name, List[(V, Icit)]) =
    forceAll1(ty) match
      case V.Pi(x, PiIcit.Impl(_), a, b) =>
        checkAutoDef(b(V.Var(ctx.lvl)))(using ctx.bind1(x, ctx.readback1(a), a))
      case ty => checkAutoType(ty)

  private def checkOnlyMetas(ty: VTy, args: List[(V, Icit)])(using
      ctx: Ctx
  ): Option[Set[MetaId]] =
    inline def allMetas = args.flatMap { a =>
      forceAll1(a._1) match
        case V.Flex(m, _) => Some(m)
        case V.Lam(x, i, _, b) =>
          val l = ctx.lvl
          forceAll1(b(V.Var(l))) match
            case V.Flex(m, _) => Some(m)
            case _            => None
        case _ => None
    }.toSet
    if args.isEmpty then None
    else
      val am = allMetas
      if am.size == args.size then Some(allMetas)
      else None

  private inline def transactMetas(inline k: Tm1): Option[Tm1] =
    try
      State.pushMetas()
      State.pushPostponedAutos()
      val etm = k
      State.discardMetas()
      State.discardPostponedAutos()
      Some(etm)
    catch
      case err: ElaborateError =>
        debug(s"transactMetas failed: ${err.getMessage}")
        State.rollbackMetas()
        State.rollbackPostponedAutos()
        None

  private def searchAuto(ty: VTy, depth: Int, failIfAllMetas: Boolean = false)(
      using ctx: Ctx
  ): Tm1 =
    debug(s"search auto ${ctx.pretty1(ty)} (depth = $depth)")
    if depth >= AutoSearchLimit then
      err(s"auto search limit reached for type: ${ctx.pretty1(ty)}")
    val (m, dx, args) = checkAutoType(ty)
    checkOnlyMetas(ty, args) match
      case Some(blocked) =>
        if failIfAllMetas then
          err(s"invalid auto type, all metas: ${ctx.pretty1(ty)}")
        else
          debug(s"postpone auto type, all metas: ${ctx.pretty1(ty)}")
          val m = freshMeta(ty)
          State.postponeAuto(m, ty, blocked)
          m
      case None =>
        val localInstances = tryLocalAutos(ty, ctx.getAutos(m, dx), depth)
        val gautos =
          State
            .getAutos(m, dx)
            .filter((m, x) => State.isAccessibleGlobal(m, x))
        val globalInstances = tryGlobalAutos(ty, gautos, depth)
        (localInstances ++ globalInstances) match
          case Nil => err(s"failed to solve auto of type: ${ctx.pretty1(ty)}")
          case tm :: Nil => tm
          case tms =>
            err(
              s"failed to solve auto of type: ${ctx.pretty1(ty)}, too many options: ${tms.map(t => ctx.pretty1(t)).mkString(", ")}"
            )

  private def tryLocalAutos(
      ty: VTy,
      entries: List[Ctx.AutoMapEntry],
      depth: Int
  )(using
      ctx: Ctx
  ): List[Tm1] =
    entries match
      case Nil => Nil
      case (x, lvl, lty, ov) :: ts =>
        debug(s"try local auto $x : ${ctx.pretty1(lty)} for ${ctx.pretty1(ty)}")
        val tm = ov match
          case None    => Tm1.Var(lvl.toIx(using ctx.lvl))
          case Some(v) => ctx.readback1(v)
        tryAuto(ty, tm, lty, depth) match
          case None => tryLocalAutos(ty, ts, depth)
          case Some(etm) =>
            debug(
              s"using local auto ${ctx.pretty1(etm)} for ${ctx.pretty1(ty)}"
            )
            etm :: tryLocalAutos(ty, ts, depth)

  private def tryGlobalAutos(
      ty: VTy,
      autos: List[(Name, Name)],
      depth: Int
  )(using ctx: Ctx): List[Tm1] =
    autos match
      case Nil => Nil
      case (m, x) :: rest =>
        val (gv, gt) = State.getGlobalDirect(m, x) match
          case Some(GlobalEntry.Def1(_, _, _, _, v, t)) => (v, t)
          case _                                        => impossible()
        debug(s"try auto $m.$x : ${ctx.pretty1(gt)} for ${ctx.pretty1(ty)}")
        tryAuto(ty, Tm1.Global(m, x, gv), gt, depth) match
          case None => tryGlobalAutos(ty, rest, depth)
          case Some(etm) =>
            debug(s"using auto ${ctx.pretty1(etm)} for ${ctx.pretty1(ty)}")
            etm :: tryGlobalAutos(ty, rest, depth)

  private def tryAuto(ty: VTy, atm: Tm1, aty: VTy, depth: Int)(using
      ctx: Ctx
  ): Option[Tm1] =
    transactMetas {
      val (etm, gty) =
        insertPi((atm, aty), depth = depth + 1)
      unify(gty, ty)
      etm
    }

  private def onMetaSolved(m: MetaId, v: V): Unit =
    val ps = State.getPostponedAutosBlockedBy(m)
    if ps.nonEmpty then
      debug(s"solving postponed autos for ?$m")
      ps.foreach { (ctx, m, vty, _) =>
        debug(s"postponed auto: ${ctx.pretty1(vty)}")
        given Ctx = ctx
        val tm = searchAuto(vty, 0)
        unify(ctx.eval1(m), ctx.eval1(tm))
      }

  // meta insertion
  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (Tm1, VTy), mode: InsertMode = All, depth: Int = 0)(
      using ctx: Ctx
  ): (Tm1, VTy) =
    @tailrec
    def go(tm: Tm1, ty: VTy): (Tm1, VTy) =
      forceAll1(ty) match
        case V.Pi(y, PiIcit.Impl(im), a, b) =>
          mode match
            case Until(x) if DoBind(x) == y => (tm, ty)
            case _ =>
              im match
                case ImplMode.Unif =>
                  val m = freshMeta(a)
                  go(Tm1.App(tm, m, Impl), b(ctx.eval1(m)))
                case ImplMode.Default(d) =>
                  val etm = check1(d, a) // TODO: postpone if a is meta
                  go(Tm1.App(tm, etm, Impl), b(ctx.eval1(etm)))
                case ImplMode.Auto =>
                  val etm = searchAuto(a, depth)
                  go(Tm1.App(tm, etm, Impl), b(ctx.eval1(etm)))
        case _ =>
          mode match
            case Until(x) => err(s"no implicit pi found with parameter $x")
            case _        => (tm, ty)
    go(inp._1, inp._2)

  private def insertPi(inp: Infer)(using ctx: Ctx): Infer = inp match
    case Infer0(t, a, cv) => inp
    case Infer1(t, a) =>
      val (t1, a1) = insertPi((t, a))
      Infer1(t1, a1)

  private def insert(inp: (Tm1, VTy))(using ctx: Ctx): (Tm1, VTy) =
    inp._1 match
      case Tm1.Lam(_, PiIcit.Impl(_), _, _) => inp
      case _                                => insertPi(inp)

  private def insert(inp: Infer)(using ctx: Ctx): Infer = inp match
    case Infer0(t, a, cv) => inp
    case Infer1(t, a) =>
      val (t1, a1) = insert((t, a))
      Infer1(t1, a1)

  // coercion lifting helpers
  private def liftFun(a: VTy, b: VTy, bcv: VTy)(using ctx: Ctx): VTy =
    given Lvl = ctx.lvl + 1
    val qbcv = readback1(bcv)(using unfoldOption = UnfoldOption.None)
    val qb = readback1(b)(using unfoldOption = UnfoldOption.None)
    V.Pi(
      DontBind,
      PiIcit.Expl,
      V.Lift(V.Val, a),
      Clos1.Clos(ctx.env, Tm1.Lift(qbcv, qb))
    )

  private def quoteFun(x: Bind, a: VTy, t: Tm1)(using ctx: Ctx): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Tm1.Lam(
      DoBind(y),
      PiIcit.Expl,
      Tm1.Lift(Tm1.Val, ctx.readback1(a)),
      Tm1.Quote(Tm0.App(Tm0.Wk1(t.splice), Tm0.Splice(Tm1.Var(ix0))))
    )

  private def spliceFun(x: Bind, a: VTy, t: Tm1)(using ctx: Ctx): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Tm1.Quote(
      Tm0.Lam(
        DoBind(y),
        ctx.readback1(a),
        Tm0.Splice(Tm1.App(Tm1.Wk0(t), Tm1.Quote(Tm0.Var(ix0)), Expl))
      )
    )

  private def liftRec(cv: VTy, ts: AssocBind[VTy])(using ctx: Ctx): ClosRec =
    def go(lvl: Lvl, ts: AssocBind[VTy]): AssocBind[Ty] =
      ts match
        case Nil => Nil
        case (x, ty) :: tl =>
          val ecv = readback1(cv)(using lvl, UnfoldOption.None)
          val ety = Tm1.Lift(ecv, readback1(ty)(using lvl, UnfoldOption.None))
          (x, ety) :: go(lvl + 1, tl)
    ClosRec(ctx.env, go(ctx.lvl, ts))

  private def quoteRec[A](ty: Ty, tm: Tm1, fs: AssocBind[A])(using
      ctx: Ctx
  ): Tm1 =
    def go(fs: AssocBind[A], ix: Int): List[Tm1] =
      fs match
        case Nil => Nil
        case (x, _) :: tl =>
          val p = Tm0.Proj(ty, tm.splice, ProjType(x.toOption, ix))
          p.quote :: go(tl, ix + 1)
    Tm1.RecordCon(go(fs, 0))

  private def spliceRec[A](ty: Ty, tm: Tm1, fs: AssocBind[A])(using
      ctx: Ctx
  ): Tm1 =
    def go(fs: AssocBind[A], ix: Int): List[Tm0] =
      fs match
        case Nil => Nil
        case (x, _) :: tl =>
          val p = Tm1.Proj(tm, ProjType(x.toOption, ix)).splice
          p :: go(tl, ix + 1)
    Tm0.RecordCon(ty, go(fs, 0)).quote

  // coercion
  private def coe(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Tm1 =
    def goRec1(tm: Tm1, ix: Int, fs1: ClosRec, fs2: ClosRec)(using
        ctx: Ctx
    ): List[(Boolean, Bind, Tm1)] =
      (fs1.fields, fs2.fields) match
        case (Nil, Nil) => Nil
        case ((x, ty1) :: tl1, (y, ty2) :: tl2) if x == y =>
          val va1 = eval1(ty1)(using fs1.env)
          val va2 = eval1(ty2)(using fs2.env)
          val tm1 = Tm1.Proj(tm, ProjType(x.toOption, ix))
          val vt1 = ctx.eval1(tm1)
          go(tm1, va1, va2) match
            case None =>
              (false, x, tm1) :: goRec1(
                tm,
                ix + 1,
                ClosRec(Env.Ext1(fs1.env, vt1), tl1),
                ClosRec(Env.Ext1(fs2.env, vt1), tl2)
              )
            case Some(coet1) =>
              (true, x, coet1) :: goRec1(
                tm,
                ix + 1,
                ClosRec(Env.Ext1(fs1.env, vt1), tl1),
                ClosRec(Env.Ext1(fs2.env, ctx.eval1(coet1)), tl2)
              )
        case _ =>
          err(s"coercion failure: ${ctx.pretty1(a1)} ~ ${ctx.pretty1(a2)}")

    def refineRec0(fs: AssocBind[Ty])(using ctx: Ctx): AssocBind[VTy] =
      fs match
        case Nil => Nil
        case (x, ty) :: tl =>
          val ety = ctx.eval1(freshMeta(V.TypeV))
          (x, ety) :: refineRec0(tl)

    def go(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Option[Tm1] =
      debug(
        s"coe ${ctx.pretty1(t)} from ${ctx.pretty1(a1)} to ${ctx.pretty1(a2)}"
      )
      (forceAll1(a1), forceAll1(a2)) match
        case (V.Flex(x, sp), _) => unify(a1, a2); None
        case (_, V.Flex(x, sp)) => unify(a1, a2); None

        case (V.Type(cv), V.Meta) => Some(Tm1.Lift(ctx.readback1(cv), t))

        case (V.Pi(x, i, a1, b1), V.Pi(x2, i2, a2, b2)) =>
          if i != i2 then err(s"icit mismatch in coercion")(using ctx)
          given ctx2: Ctx = ctx.bind1(x, ctx.readback1(a2), a2)
          go(Tm1.Var(ix0), a2, a1) match
            case None =>
              go(
                Tm1.App(Tm1.Wk1(t), Tm1.Var(ix0), i.toIcit),
                b1(ctx2.eval1(Tm1.Var(ix0))),
                b2(V.Var(ctx.lvl))
              ).map(b => Tm1.Lam(x, i, ctx.readback1(a2), b))
            case Some(coev0) =>
              Some(
                Tm1.Lam(
                  x,
                  i,
                  ctx.readback1(a2),
                  coe(
                    Tm1.App(Tm1.Wk1(t), coev0, i.toIcit),
                    b1(ctx2.eval1(coev0)),
                    b2(V.Var(ctx.lvl))
                  )
                )
              )

        case (V.RecordTy1(ts1), V.RecordTy1(ts2)) =>
          val fs = goRec1(t, 0, ts1, ts2)
          if fs.exists((b, _, _) => b) then
            Some(Tm1.RecordCon(fs.map((_, _, t) => t)))
          else None

        case (V.Lift(_, V.Fun(a, cv, b)), V.Pi(x, _, _, _)) =>
          Some(coe(quoteFun(x, a, t), liftFun(a, b, cv), a2))
        case (V.Lift(_, V.Fun(a, cv, b)), _) =>
          Some(coe(quoteFun(DontBind, a, t), liftFun(a, b, cv), a2))
        case (V.Pi(x, _, _, _), V.Lift(_, V.Fun(t1, cv, t2))) =>
          Some(spliceFun(x, t1, coe(t, a1, liftFun(t1, t2, cv))))
        case (_, V.Lift(_, V.Fun(t1, cv, t2))) =>
          Some(spliceFun(DontBind, t1, coe(t, a1, liftFun(t1, t2, cv))))

        case (V.Lift(_, ty @ V.RecordTy0(cv, fs)), a) =>
          val qty = ctx.readback1(ty)
          Some(coe(quoteRec(qty, t, fs), V.RecordTy1(liftRec(cv, fs)), a))
        case (a, V.Lift(_, ty @ V.RecordTy0(cv, fs))) =>
          val qty = ctx.readback1(ty)
          Some(spliceRec(qty, coe(t, a, V.RecordTy1(liftRec(cv, fs))), fs))

        case (pi @ V.Pi(x, PiIcit.Expl, a, b), V.Lift(cv, a2)) =>
          unify(cv, V.Comp)
          val a1 = ctx.eval1(freshMeta(V.TypeV))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2_ = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2_)
          unify(a2, fun)
          go(t, pi, V.Lift(V.Comp, fun))
        case (V.Lift(cv, a), pi @ V.Pi(x, PiIcit.Expl, t1, t2)) =>
          unify(cv, V.Comp)
          val a1 = ctx.eval1(freshMeta(V.TypeV))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2 = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2)
          unify(a, fun)
          go(t, V.Lift(V.Comp, fun), pi)

        case (V.RecordTy1(ClosRec(env, as)), V.Lift(cv2, a2)) =>
          val as2 = refineRec0(as)
          val recty = V.RecordTy0(cv2, as2)
          unify(a2, recty)
          go(t, V.RecordTy1(ClosRec(env, as)), V.Lift(cv2, recty))
        case (V.Lift(cv, a), V.RecordTy1(ClosRec(env, as))) =>
          val as2 = refineRec0(as)
          val recty = V.RecordTy0(cv, as2)
          unify(a, recty)
          go(t, V.Lift(V.Val, recty), V.RecordTy1(ClosRec(env, as)))

        case (_, _) => unify(a1, a2); None

    go(t, a1, a2).getOrElse(t)

  // helpers
  private inline def enter[A](pos: PosInfo)(inline action: Ctx ?=> A)(using
      ctx: Ctx
  ): A =
    action(using ctx.enter(pos))

  private def tyAnnot(ma: Option[S], ty: VTy)(using ctx: Ctx): Ty =
    ma.fold(freshMeta(ty))(a => check1(a, ty))

  private def ensureFun(a: VTy, acv: VTy)(using ctx: Ctx): (VTy, VTy, VTy) =
    forceAll1(a) match
      case V.Fun(a, bcv, b) => (a, bcv, b)
      case _ =>
        unify(acv, V.Comp)
        val a2 = ctx.eval1(freshMeta(V.TypeV))
        val vbcv2 = ctx.eval1(freshCV())
        val b2 = ctx.eval1(freshMeta(V.Type(vbcv2)))
        unify(a, V.Fun(a2, vbcv2, b2))
        (a2, vbcv2, b2)

  private def ensureFunN(n: Int, a: VTy, acv: VTy)(using
      ctx: Ctx
  ): (List[VTy], VTy, VTy) =
    if n == 0 then (Nil, acv, a)
    else
      val (t1, cv, t2) = ensureFun(a, acv)
      val (ps, rcv, rt) = ensureFunN(n - 1, t2, cv)
      (t1 :: ps, rcv, rt)

  private def ensureLift(t: VTy)(using ctx: Ctx): (VTy, VTy) =
    forceAll1(t) match
      case V.Lift(cv, ty) => (cv, ty)
      case _ =>
        val cv = ctx.eval1(freshCV())
        val ty = ctx.eval1(freshMeta(V.Type(cv)))
        unify(t, V.Lift(cv, ty))
        (cv, ty)

  private def apply1(a: VTy, i: Icit, t: Tm1, u: S)(using ctx: Ctx): Infer =
    debug(s"apply1 ${ctx.pretty1(a)} $i @ $u")
    forceAll1(a) match
      case V.Pi(x, i2, a, b) =>
        if i != i2.toIcit then err(s"icit mismatch in apply1")
        val u2 = check1(u, a)
        Infer1(Tm1.App(t, u2, i), b(ctx.eval1(u2)))
      case V.Lift(_, V.Fun(a, bcv, b)) =>
        if i != Expl then err(s"icit mismatch in apply1")
        val u2 = check0(u, a, V.Val)
        Infer0(Tm0.App(t.splice, u2), b, bcv)
      case _ =>
        val a2 = freshMeta(V.Meta)
        val va2 = ctx.eval1(a2)
        val x = DoBind(Name("x"))
        val b2 =
          Clos1.Clos(ctx.env, freshMeta(V.Meta)(using ctx.bind1(x, a2, va2)))
        val t2 = coe(t, a, V.Pi(x, PiIcit(i), va2, b2))
        val u2 = check1(u, ctx.eval1(a2))
        Infer1(Tm1.App(t2, u2, i), b2(ctx.eval1(u2)))

  private def coeQuote(t: Tm1, a1: VTy, a2: VTy, cv: VTy)(using ctx: Ctx): Tm0 =
    coe(t, a1, V.Lift(cv, a2)).splice

  private def icitMatch(i: ArgInfo[PiIcit], x: Bind, i2: PiIcit): Boolean =
    i match
      case ArgInfo.Named(y) =>
        x match
          case DontBind  => false
          case DoBind(x) => x == y
      case ArgInfo.Icit(i) => i == i2

  private def varHasUnknownType1(x: Name)(using ctx: Ctx): Boolean =
    ctx.lookup(x) match
      case Some(NameInfo.Name1(_, ty)) =>
        forceAll1(ty) match
          case V.Flex(_, _) => true
          case _            => false
      case _ => false

  private def orderFields[T](
      topty: VTy,
      fs: Assoc[S],
      ts: AssocBind[T]
  )(using ctx: Ctx): Assoc[S] =
    if fs.size != ts.size then
      err(
        s"record fields mismatch, checking against type: ${ctx.pretty1(topty)}"
      )
    val xs = fs.map(_._1)
    if xs.toSet.size != xs.size then
      err(
        s"duplicate name in record, checking against type: ${ctx.pretty1(topty)}"
      )
    def go(ts: AssocBind[T]): Assoc[S] =
      ts match
        case Nil => Nil
        case (x, _) :: _ if x == DontBind =>
          err(
            s"cannot re-order because record type has unnamed field: ${ctx.pretty1(topty)}"
          )
        case (x, _) :: tl =>
          fs.find((y, _) => x.toName == y) match
            case None =>
              err(
                s"expected $x in record, checking against type: ${ctx.pretty1(topty)}"
              )
            case Some(hd) => hd :: go(tl)
    go(ts)

  // checking
  private def check0(tm: S, ty: VTy, cv: VTy)(using ctx: Ctx): Tm0 =
    debug(s"check0 $tm : ${ctx.pretty1(ty)} : ${ctx.pretty1(cv)}")
    enter(tm.pos):
      tm match
        case S.Lam(_, x, i, ma, b) =>
          if i != ArgInfo.PiExpl then err(s"implicit lambda in Ty")
          val (t1, fcv, t2) = ensureFun(ty, cv)
          ma.foreach { sty => unify(ctx.eval1(check1(sty, V.TypeV)), t1) }
          val qt1 = ctx.readback1(t1)
          Tm0.Lam(
            x,
            qt1,
            check0(b, t2, fcv)(using ctx.bind0(x, qt1, t1, Tm1.Val, V.Val))
          )

        case S.LetRec(_, x, ma, v, b) =>
          val (ety, cv2, vcv2) = (tyAnnot(ma, V.TypeC), Tm1.Comp, V.Comp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using nctx)
          val eb = check0(b, ty, cv)(using nctx)
          Tm0.LetRec(x, ety, ev, eb)

        case S.Let0(_, x, ma, v, b) =>
          val (ety, cv2, vcv2) =
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(ma, V.Type(vcv2))
            (ety, cv2, vcv2)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using ctx)
          val eb = check0(b, ty, cv)(using nctx)
          Tm0.Let(x, ety, ev, eb)

        case tm @ S.Let1(_, _, _, _, _, _) =>
          val mty = V.Lift(cv, ty)
          val etm = check1(tm, mty)
          Tm0.Splice(etm)

        case S.StringLit(_, v) =>
          unify(cv, V.Val)
          unify(ty, V.String)
          Tm0.StringLit(v)

        case S.If(_, c, t, f) =>
          val ec = check0(c, V.Bool, V.Val)
          val et = check0(t, ty, cv)
          val ef = check0(f, ty, cv)
          Tm0.If(ctx.readback1(ty), ec, et, ef)

        case S.Hole(_, ox) =>
          val mty = V.Lift(cv, ty)
          ox.foreach(x => State.addHole(x, mty))
          freshMeta(mty).splice

        case S.Splice(_, t) => check1(t, V.Lift(cv, ty)).splice

        case S.Match(_, Some(s), sty, cs) => checkMatch0(s, sty, cs, ty, cv)

        case S.Match(_, None, sty, cs) =>
          if sty.isDefined then err(s"runtime level match cannot have type")
          val (t1, fcv, t2) = ensureFun(ty, cv)
          val bx = DoBind(Name("x"))
          val rt1 = ctx.readback1(t1)
          val nctx = ctx.insert0(bx, rt1, Tm1.Val)
          val ecs = checkCases0(t1, cs, t2, fcv)(using nctx)
          val nrt1 = nctx.readback1(t1)
          val rt2 = nctx.readback1(t2)
          Tm0.Lam(bx, rt1, Tm0.Case(rt2, nrt1, Tm0.Var(ix0), ecs))

        case S.UnitLit(_) =>
          forceAll1(ty) match
            case V.TypeCon0(m, dx, dps) =>
              State.getGlobalDirect(m, dx) match
                case Some(GlobalEntry.Data0(_, _, _, _, _, _, unitCon, _, _)) =>
                  unitCon match
                    case Some(cx) =>
                      State.getGlobalDirect(m, cx) match
                        case Some(
                              GlobalEntry.Con0(_, _, _, _, _, _, tm, _, _)
                            ) =>
                          dps
                            .foldLeft(tm) { case (tm, (ty, _)) =>
                              Tm1.App(tm, ctx.readback1(ty), Impl)
                            }
                            .splice
                        case _ => impossible()
                    case None =>
                      err(
                        s"cannot check unit against ${ctx.pretty1(ty)}, datatype does not have a 0-parameter constructor"
                      )
                case _ => impossible()
            case V.RecordTy0(cv, Nil) => Tm0.RecordConEmpty(ctx.readback1(cv))
            case _ => err(s"cannot check unit against ${ctx.pretty1(ty)}")

        case S.EmptyRecord(_) =>
          unify(ty, V.RecordTy0Empty(cv))
          Tm0.RecordConEmpty(ctx.readback1(cv))

        case S.Tuple(_, fs) =>
          forceAll1(ty) match
            case V.RecordTy0(cv, ts) =>
              def go(fs: List[S], ts: AssocBind[VTy]): List[Tm0] =
                (fs, ts) match
                  case (Nil, Nil) => Nil
                  case (tm :: fs, (y, vty) :: ts) =>
                    check0(tm, vty, cv) :: go(fs, ts)
                  case _ =>
                    err(
                      s"record field mismatch, checking against type: ${ctx.pretty1(ty)}"
                    )
              Tm0.RecordCon(ctx.readback1(ty), go(fs, ts))
            case _ => err(s"cannot check tuple against ${ctx.pretty1(ty)}")

        case S.RecordCon0(_, fs0) =>
          forceAll1(ty) match
            case V.RecordTy0(cv, ts) =>
              val fs = orderFields(ty, fs0, ts)
              def go(fs: Assoc[S], ts: AssocBind[VTy]): List[Tm0] =
                (fs, ts) match
                  case (Nil, Nil) => Nil
                  case ((x, tm) :: fs, (y, vty) :: ts) if x == y.toName =>
                    check0(tm, vty, cv) :: go(fs, ts)
                  case _ =>
                    err(
                      s"record field mismatch, checking against type: ${ctx.pretty1(ty)}"
                    )
              Tm0.RecordCon(ctx.readback1(ty), go(fs, ts))
            case _ => err(s"cannot check record against ${ctx.pretty1(ty)}")

        case S.Unsafe(_, io, l, args) =>
          val el = check1(l, V.Label)
          val eargs = args.map { a =>
            val (ea, _, acv) = infer0(a)
            unify(acv, V.Val)
            ea
          }
          val rty = if io then
            unify(cv, V.Comp)
            val m = ctx.eval1(freshMeta(V.TypeV))
            unify(ty, V.IO(m))
            m
          else
            unify(cv, V.Val)
            ty
          Tm0.Unsafe(ctx.readback1(rty), io, el, eargs)

        case tm =>
          infer(tm) match
            case Infer0(etm, vty, vcv) =>
              unify(vcv, cv)
              unify(vty, ty)
              etm
            case Infer1(etm, vty) =>
              val (etm2, vty2) = insert((etm, vty))
              coeQuote(etm2, vty2, ty, cv)

  private def shouldNotPostpone(tm: S): Boolean =
    tm match
      case S.Var(_, _)       => true
      case S.Prim(_, _)      => true
      case S.IntLit(_, _)    => true
      case S.Hole(_, _)      => true
      case S.App(_, _, _, _) => true
      case _                 => false

  private def check1(tm: S, ty: VTy)(using ctx: Ctx): Tm1 =
    debug(s"check1 $tm : ${ctx.pretty1(ty)}")
    enter(tm.pos):
      (tm, forceAll1(ty)) match
        case (S.Lam(_, x, i, ma, b), V.Pi(x2, i2, t1, t2))
            if icitMatch(i, x2, i2) =>
          ma.foreach { sty => unify(ctx.eval1(check1(sty, V.Meta)), t1) }
          val autod = i2 match // TODO: do this when elaborating the pi type
            case Surface.PiIcit.Impl(Surface.ImplMode.Auto) =>
              val (m, dx, _) = checkAutoDef(t1)
              Some((m, dx))
            case _ => None
          val qt1 = ctx.readback1(t1)
          val nctx = ctx.bind1(x, qt1, t1, autod)
          val eb = check1(b, t2(V.Var(ctx.lvl)))(using nctx)
          Tm1.Lam(x, i2, qt1, eb)

        case (S.Var(_, x), V.Pi(_, PiIcit.Impl(_), _, _))
            if varHasUnknownType1(x) =>
          val Some(NameInfo.Name1(lvl, ty2)) = ctx.lookup(x): @unchecked
          unify(ty2, ty)
          Tm1.Var(lvl.toIx(using ctx.lvl))

        case (tm, V.Pi(x, i @ PiIcit.Impl(im), t1, t2)) =>
          val autod = im match // TODO: do this when elaborating the pi type
            case Surface.ImplMode.Auto =>
              val (m, dx, _) = checkAutoDef(t1)
              Some((m, dx))
            case _ => None
          val qt1 = ctx.readback1(t1)
          val nctx = ctx.insert1(x, qt1, autod)
          val eb = check1(tm, t2(V.Var(ctx.lvl)))(using nctx)
          Tm1.Lam(x, i, qt1, eb)

        case (tm, V.Flex(m, _)) if !shouldNotPostpone(tm) =>
          val pl = freshMetaId(ty)
          val c = State.newCheck(tm, ty, pl)
          State.addBlocking(c, m)
          debug(s"postpone $tm : ${ctx.pretty1(ty)} as ??$c, placeholder ?$pl")
          Tm1.PostponedCheck(c)

        case (S.Pi(_, DontBind, PiIcit.Expl, t1, t2), V.Type(cv)) =>
          unify(cv, V.Comp)
          val et1 = check1(t1, V.TypeV)
          val fcv = freshCV()
          val vfcv = ctx.eval1(fcv)
          val et2 = check1(t2, V.Type(vfcv))
          Tm1.Fun(et1, fcv, et2)
        case (S.Pi(_, x, i, t1, t2), V.Meta) =>
          val et1 = check1(t1, V.Meta)
          val et2 = check1(t2, V.Meta)(using ctx.bind1(x, et1, ctx.eval1(et1)))
          Tm1.Pi(x, i, et1, et2)

        case (S.Lift(_, tm), V.Meta) =>
          val cv = freshCV()
          Tm1.Lift(cv, check1(tm, V.Type(ctx.eval1(cv))))

        case (S.Let1(_, auto, x, mlty, v, b), _) =>
          val lty = tyAnnot(mlty, V.Meta)
          val vlty = ctx.eval1(lty)
          val autod =
            if auto then
              val (m, dx, _) = checkAutoDef(vlty)
              Some((m, dx))
            else None
          val ev = check1(v, vlty)
          val nctx = ctx.define(x, lty, vlty, ev, ctx.eval1(ev), autod)
          val eb = check1(b, ty)(using nctx)
          Tm1.Let(x, lty, ev, eb)

        case (S.Quote(_, tm), V.Lift(cv, ty)) => check0(tm, ty, cv).quote
        case (tm, V.Lift(cv, ty))             => check0(tm, ty, cv).quote

        case (S.Hole(_, ox), _) =>
          ox.foreach(x => State.addHole(x, ty))
          freshMeta(ty)

        case (S.Match(_, Some(s), sty, cs), _) => checkMatch1(s, sty, cs, ty)

        case (S.Match(_, None, sty, cs), V.Pi(x, PiIcit.Expl, a, b)) =>
          forceAll1(a) match
            case V.Lift(dcv, vdty) =>
              if sty.isDefined then err(s"runtime level match cannot have type")
              unify(dcv, V.Val)
              val ra = ctx.readback1(a)
              val nctx = ctx.insert1(x, ra)
              val vrcv = nctx.eval1(freshCV()(using nctx))
              val vrty = nctx.eval1(freshMeta(V.Type(vrcv))(using nctx))
              unify(b(V.Var(ctx.lvl)), V.Lift(vrcv, vrty))(using nctx)
              val ndty = nctx.readback1(vdty)
              val nvrty = nctx.readback1(vrty)
              val ecs = checkCases0(vdty, cs, vrty, vrcv)(using nctx)
              val casetm = Tm0.Case(nvrty, ndty, Tm1.Var(ix0).splice, ecs)
              val y = x.orElse(DoBind(Name("x")))
              Tm1.Lam(y, PiIcit.Expl, ra, casetm.quote)
            case _ =>
              val ra = ctx.readback1(a)
              val nctx = ctx.insert1(x, ra)
              val escrut = Tm1.Var(ix0)
              val res = inferMatch1ExType(a, sty)
              val rexty = res.getOrElse(b)
              val ecs = checkCases1(escrut, a, cs, rexty)(using nctx)
              res.foreach { rexty2 =>
                val v = ctx.eval1(escrut)
                unify(rexty2(v), b(v))
              }
              val casetm = Tm1.Case(escrut, ecs)
              val y = x.orElse(DoBind(Name("x")))
              Tm1.Lam(y, PiIcit.Expl, ra, casetm)

        case (S.UnitLit(_), V.RecordTy1(ClosRec(_, Nil))) => Tm1.RecordConEmpty

        case (S.UnitLit(_), V.TypeCon1(m, dx, dps)) =>
          State.getGlobalDirect(m, dx) match
            case Some(GlobalEntry.Data1(_, _, _, _, _, _, unitCon, _)) =>
              unitCon match
                case Some(cx) =>
                  State.getGlobalDirect(m, cx) match
                    case Some(
                          GlobalEntry.Con1(_, _, _, _, _, _, tm, _, _)
                        ) =>
                      dps
                        .foldLeft(tm) { case (tm, (ty, _)) =>
                          Tm1.App(tm, ctx.readback1(ty), Impl)
                        }
                    case _ => impossible()
                case None =>
                  err(
                    s"cannot check unit against ${ctx.pretty1(ty)}, datatype does not have a 0-parameter constructor"
                  )
            case _ => impossible()

        case (S.EmptyRecord(_), V.Type(cv)) =>
          Tm1.RecordTy0Empty(ctx.readback1(cv))
        case (S.EmptyRecord(_), V.Meta) => Tm1.RecordTy1Empty

        case (S.EmptyRecord(_), V.RecordTy1(ts)) =>
          Tm1.RecordCon(checkTuple1(ty, Nil, ts))
        case (S.Tuple(_, fs), V.RecordTy1(ts)) =>
          Tm1.RecordCon(checkTuple1(ty, fs, ts))

        case (S.RecordTy(_, fs), vrty @ V.Type(vcv)) =>
          val xs = fs.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record type")
          def go(fs: AssocBind[S]): AssocBind[Ty] =
            fs match
              case Nil => Nil
              case (x, ty) :: rest =>
                val ety = check1(ty, vrty)
                (x, ety) :: go(rest)
          Tm1.RecordTy0(ctx.readback1(vcv), go(fs))

        case (S.RecordTy(_, fs), V.Meta) =>
          val xs = fs.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record type")
          def go(ctx: Ctx, fs: AssocBind[S]): AssocBind[Ty] =
            fs match
              case Nil => Nil
              case (x, ty) :: rest =>
                val ety = check1(ty, V.Meta)(using ctx)
                val vty = ctx.eval1(ety)
                (x, ety) :: go(ctx.bind1(x, ety, vty), rest)
          Tm1.RecordTy1(go(ctx, fs))

        case (S.Tuple(_, fs), vrty @ V.Type(vcv)) =>
          Tm1.RecordTy0(
            ctx.readback1(vcv),
            fs.map(ty => (DontBind, check1(ty, vrty)))
          )

        case (S.Tuple(_, fs), V.Meta) =>
          def go(fs: List[S])(using ctx: Ctx): AssocBind[Ty] =
            fs match
              case Nil => Nil
              case ty :: rest =>
                val ety = check1(ty, V.Meta)
                val nctx = ctx.bind1(DontBind, ety, ctx.eval1(ety))
                (DontBind, ety) :: go(rest)(using nctx)
          Tm1.RecordTy1(go(fs))

        case (S.RecordCon1(_, fs0), topty @ V.RecordTy1(ts)) =>
          val fs = orderFields(topty, fs0, ts.fields)
          def go(
              env: Env,
              fs: Assoc[S],
              ts: AssocBind[Ty]
          ): List[Tm1] =
            (fs, ts) match
              case (Nil, Nil) => Nil
              case ((x, tm) :: fs, (y, ty) :: ts) if x == y.toName =>
                val vty = eval1(ty)(using env)
                val qty = ctx.readback1(vty)
                val etm = check1(tm, vty)
                val vtm = ctx.eval1(etm)
                val rest = go(Env.Ext1(env, vtm), fs, ts)
                etm :: rest
              case _ =>
                err(
                  s"record fields mismatch, checking against type: ${ctx.pretty1(topty)}"
                )
          Tm1.RecordCon(go(ts.env, fs, ts.fields))

        case (tm, _) =>
          val (etm, vty) = insert(infer1(tm))
          coe(etm, vty, ty)

  private def checkTuple1(topty: VTy, fs: List[S], ts: ClosRec)(using
      ctx: Ctx
  ): List[Tm1] =
    def go(env: Env, fs: List[S], ts: AssocBind[Ty]): List[Tm1] =
      (fs, ts) match
        case (Nil, Nil) => Nil
        case (tm :: fs, (x, ty) :: ts) =>
          val vty = eval1(ty)(using env)
          val qty = ctx.readback1(vty)
          val etm = check1(tm, vty)
          val vtm = ctx.eval1(etm)
          val rest = go(Env.Ext1(env, vtm), fs, ts)
          etm :: rest
        case _ =>
          err(s"failed to check tuple against type: ${ctx.pretty1(topty)}")
    go(ts.env, fs, ts.fields)

  // inference
  private def infer0(tm: S)(using ctx: Ctx): (Tm0, VTy, VTy) =
    debug(s"infer0 $tm")
    enter(tm.pos):
      tm match
        case S.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_)             => err(s"implicit lambda in type")
            case ArgInfo.Icit(PiIcit.Impl(_)) => err(s"implicit lambda in type")
            case ArgInfo.Icit(PiIcit.Expl) =>
              val acv = Tm1.Val
              val avcv = ctx.eval1(acv)
              val ety = tyAnnot(mty, V.Type(avcv))
              val cv = freshCV()
              val vcv = ctx.eval1(cv)
              val rt = freshMeta(V.Type(vcv))
              val vrt = ctx.eval1(rt)
              val vty = ctx.eval1(ety)
              val eb =
                check0(b, vrt, vcv)(using ctx.bind0(x, ety, vty, acv, avcv))
              (Tm0.Lam(x, ety, eb), V.Fun(vty, vcv, vrt), V.Comp)

        case S.Hole(_, _) => err("cannot infer hole")

        case S.EmptyRecord(_) =>
          val cv = freshCV()
          val vcv = ctx.eval1(cv)
          (Tm0.RecordConEmpty(cv), V.RecordTy0Empty(vcv), vcv)

        case S.StringLit(_, v) => (Tm0.StringLit(v), V.String, V.Val)

        case tm =>
          insert(infer(tm)) match
            case Infer0(etm, ty, cv) => (etm, ty, cv)
            case Infer1(etm, ty) =>
              forceAll1(ty) match
                case V.Lift(cv, vty) => (etm.splice, vty, cv)
                case _ =>
                  val cv = freshCV()
                  val vcv = ctx.eval1(cv)
                  val vty = ctx.eval1(freshMeta(V.Type(vcv)))
                  val etm2 = coe(etm, ty, V.Lift(vcv, vty)).splice
                  (etm2, vty, vcv)

  private def infer1(tm: S)(using ctx: Ctx): (Tm1, VTy) =
    debug(s"infer1 $tm")
    enter(tm.pos):
      tm match
        case S.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_) => err(s"cannot infer named lambda")
            case ArgInfo.Icit(i) =>
              val ety = tyAnnot(mty, V.Meta)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = insert(infer1(b)(using ctx2))(using ctx2)
              val ert = ctx2.readback1(vrt)
              (
                Tm1.Lam(x, i, ety, eb),
                V.Pi(x, i, vty, Clos1.Clos(ctx.env, ert))
              )

        case S.Hole(_, _) =>
          val ty = ctx.eval1(freshMeta(V.Meta))
          val tm = freshMeta(ty)
          (tm, ty)

        case S.StringLit(_, v) => (Tm1.LabelLit(v), V.Label)

        case tm =>
          infer(tm) match
            case Infer0(tm, ty, cv) => (tm.quote, V.Lift(cv, ty))
            case Infer1(tm, ty)     => (tm, ty)

  private val primTypes: Map[Primitive, VTy] = Map(
    Primitive.Meta -> V.Meta,
    Primitive.Type -> V.fun1(V.CV, V.Meta),
    Primitive.CV -> V.Meta,
    Primitive.Comp -> V.CV,
    Primitive.Val -> V.CV,
    Primitive.Bool -> V.TypeV,
    Primitive.True -> V.Lift(V.Val, V.Bool),
    Primitive.False -> V.Lift(V.Val, V.Bool),
    Primitive.Int -> V.TypeV,
    Primitive.Lt ->
      V.Lift(V.Comp, V.Fun(V.Int, V.Comp, V.Fun(V.Int, V.Val, V.Bool))),
    Primitive.Add ->
      V.Lift(V.Comp, V.Fun(V.Int, V.Comp, V.Fun(V.Int, V.Val, V.Int))),
    Primitive.Sub ->
      V.Lift(V.Comp, V.Fun(V.Int, V.Comp, V.Fun(V.Int, V.Val, V.Int))),
    Primitive.Mul ->
      V.Lift(V.Comp, V.Fun(V.Int, V.Comp, V.Fun(V.Int, V.Val, V.Int))),
    // type val -> type comp
    Primitive.IO -> V.fun1(V.TypeV, V.TypeC),
    // {A : type val} -> ^A -> ^(IO A)
    Primitive.ReturnIO ->
      V.piI(
        "A",
        V.TypeV,
        a => V.fun1(V.liftV(a), V.liftC(V.IO(a)))
      ),
    // {A : type val} -> {B : type val} -> ^(IO A) -> ^(A -> IO B) -> ^(IO B)
    Primitive.BindIO ->
      V.piI(
        "A",
        V.TypeV,
        a =>
          V.piI(
            "B",
            V.TypeV,
            b =>
              V.fun1(
                V.liftC(V.IO(a)),
                V.fun1(V.liftC(V.Fun(a, V.Comp, V.IO(b))), V.liftC(V.IO(b)))
              )
          )
      ),
    // {A B : meta} -> A -> B -> meta
    Primitive.Id -> V.piI(
      "A",
      V.Meta,
      a => V.piI("B", V.Meta, b => V.fun1(a, V.fun1(b, V.Meta)))
    ),
    // {A : meta} {x : A} -> Id {A} {A} x x
    Primitive.Refl -> V.piI(
      "A",
      V.Meta,
      a => V.piI("x", a, x => V.Id(a, a, x, x))
    ),
    /*
    {A : meta} {x : A}
      (P : {y : A} -> Id {A} {A} x y -> meta)
      (h : P {x} (refl {A} {x}))
      {y : A}
      (p : Id {A} {A} x y)
      -> P {y} p
     */
    Primitive.ElimId ->
      V.piI(
        "A",
        V.Meta,
        a =>
          V.piI(
            "x",
            a,
            x =>
              V.pi(
                "P",
                V.piI("y", a, y => V.fun1(V.Id(a, a, x, y), V.Meta)),
                pp =>
                  V.pi(
                    "h",
                    vappE(vappI(pp, x), V.Refl(a, x)),
                    h =>
                      V.piI(
                        "y",
                        a,
                        y =>
                          V.pi(
                            "p",
                            V.Id(a, a, x, y),
                            p => vappE(vappI(pp, y), p)
                          )
                      )
                  )
              )
          )
      ),
    /*
    {I : meta} {A : I -> meta} {B : (i : I) -> A i -> meta}
    -> (({i : I} (x : A i) -> B i x) -> {i : I} (x : A i) -> B i x)
    -> {i : I} (x : A i)
    -> B i x
     */
    Primitive.FixIx ->
      V.piI(
        "I",
        V.Meta,
        ii =>
          V.piI(
            "A",
            V.fun1(ii, V.Meta),
            a =>
              V.piI(
                "B",
                V.pi("i", ii, i => V.fun1(vappE(a, i), V.Meta)),
                b =>
                  V.fun1(
                    V.fun1(
                      V.piI(
                        "i",
                        ii,
                        i => V.pi("x", vappE(a, i), x => vappE(vappE(b, i), x))
                      ),
                      V.piI(
                        "i",
                        ii,
                        i => V.pi("x", vappE(a, i), x => vappE(vappE(b, i), x))
                      )
                    ),
                    V.piI(
                      "i",
                      ii,
                      i => V.pi("x", vappE(a, i), x => vappE(vappE(b, i), x))
                    )
                  )
              )
          )
      ),
    Primitive.Label -> V.Meta,
    Primitive.Class -> V.fun1(V.Label, V.TypeV),
    Primitive.Array -> V.fun1(V.TypeV, V.TypeV),
    Primitive.Void -> V.TypeV,
    // {A : type val} -> ^(IO A) -> ^A
    Primitive.UnsafeRunIO -> V.piI(
      "A",
      V.TypeV,
      a => V.fun1(V.liftC(V.IO(a)), V.liftV(a))
    )
  )

  private inline def inferPrimType(p: Primitive): VTy = primTypes(p)

  private def inferGlobal(m: Option[Name], x: Name)(using ctx: Ctx): Infer =
    State.getGlobal(m, x) match
      case Left((m, x, State.GlobalLookupFailure.ModuleNotFound)) =>
        err(s"undefined variable $m.$x: undefined module")
      case Left((m, x, State.GlobalLookupFailure.GlobalNotFound)) =>
        err(s"undefined variable $m.$x")
      case Left(
            (m, x, State.GlobalLookupFailure.GlobalIsNotAccessible)
          ) =>
        err(s"inaccessible variable $m.$x")
      case Right((m, x, GlobalEntry.Def0(_, _, _, _, _, _, ty, cv))) =>
        Infer0(Tm0.Global(m, x), ty, cv)
      case Right((m, x, GlobalEntry.Def1(_, _, _, _, v, ty))) =>
        Infer1(Tm1.Global(m, x, v), ty)
      case Right((_, _, GlobalEntry.Data0(_, _, _, _, tm, ty, _, _, _))) =>
        Infer1(tm, ty)
      case Right((_, _, GlobalEntry.Con0(_, _, _, _, _, _, tm, _, ty))) =>
        Infer1(tm, ty)
      case Right((_, _, GlobalEntry.Data1(_, _, _, _, tm, ty, _, _))) =>
        Infer1(tm, ty)
      case Right((_, _, GlobalEntry.Con1(_, _, _, _, _, _, tm, _, ty))) =>
        Infer1(tm, ty)
      case Right((_, _, GlobalEntry.DeclaredData(_, tm, ty))) =>
        Infer1(tm, ty)

  private def infer(tm: S)(using ctx: Ctx): Infer =
    debug(s"infer $tm")
    enter(tm.pos):
      tm match
        case S.Prim(_, p)      => Infer1(Tm1.Prim(p), inferPrimType(p))
        case S.IntLit(_, v)    => Infer0(Tm0.IntLit(v), V.Int, V.Val)
        case S.StringLit(_, v) => err(s"cannot infer string literal")

        case S.Var(_, x) =>
          ctx.lookup(x) match
            case Some(NameInfo.Name0(x, ty, cv)) =>
              Infer0(Tm0.Var(x.toIx(using ctx.lvl)), ty, cv)
            case Some(NameInfo.Name1(x, ty)) =>
              Infer1(Tm1.Var(x.toIx(using ctx.lvl)), ty)
            case None => inferGlobal(None, x)

        case proj @ S.Proj(_, tm, p) =>
          val (hd, tl) = proj.splitProjs
          hd match
            case S.Var(pos, x) =>
              if ctx.lookup(x).isEmpty && State.getGlobal(None, x).isLeft then
                def createMod(
                    tl: List[(PosInfo, Surface.ProjType)]
                ): List[Name] =
                  tl match
                    case Nil => Nil
                    case (pos, Surface.ProjType.Indexed(_)) :: _ =>
                      err("indexed projection for module is invalid")(using
                        ctx.enter(pos)
                      )
                    case (pos, Surface.ProjType.Named(x)) :: tl =>
                      x :: createMod(tl)
                val xs = x :: createMod(tl)
                val m = Name(xs.init.mkString("."))
                inferGlobal(Some(m), xs.last)(using ctx.enter(tl.last._1))
              else inferProj(tm, p)
            case _ => inferProj(tm, p)

        case S.LetRec(_, x, mty, v, b) =>
          val (ety, cv2, vcv2) = (tyAnnot(mty, V.TypeC), Tm1.Comp, V.Comp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using nctx)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(Tm0.LetRec(x, ety, ev, eb), rty, rcv)

        case S.Let0(_, x, mty, v, b) =>
          val (ety, cv2, vcv2) =
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(mty, V.Type(vcv2))
            (ety, cv2, vcv2)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using ctx)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(Tm0.Let(x, ety, ev, eb), rty, rcv)

        case S.Let1(_, auto, x, mty, v, b) =>
          val lty = tyAnnot(mty, V.Meta)
          val vlty = ctx.eval1(lty)
          val autod =
            if auto then
              val (m, dx, _) = checkAutoDef(vlty)
              Some((m, dx))
            else None
          val ev = check1(v, vlty)
          val nctx = ctx.define(x, lty, vlty, ev, ctx.eval1(ev), autod)
          val (eb, rty) = infer1(b)(using nctx)
          Infer1(Tm1.Let(x, lty, ev, eb), rty)

        case S.Pi(_, DontBind, PiIcit.Expl, a, b) =>
          val (ea, vta) = insert(infer1(a))
          forceAll1(vta) match
            case V.Type(cv) =>
              unify(cv, V.Val)
              val bcv = freshCV()
              val vbcv = ctx.eval1(bcv)
              val eb = check1(b, V.Type(vbcv))
              Infer1(Tm1.Fun(ea, bcv, eb), V.TypeC)
            case V.Meta =>
              val eb =
                check1(b, V.Meta)(using ctx.bind1(DontBind, ea, ctx.eval1(ea)))
              Infer1(Tm1.Pi(DontBind, PiIcit.Expl, ea, eb), V.Meta)
            case _ => err("expected type for Pi parameter")
        case S.Pi(_, x, i, a, b) =>
          val ea = check1(a, V.Meta)
          val eb = check1(b, V.Meta)(using ctx.bind1(x, ea, ctx.eval1(ea)))
          Infer1(Tm1.Pi(x, i, ea, eb), V.Meta)

        case S.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_)          => err("cannot infer")
            case ArgInfo.Icit(PiIcit.Expl) => err("cannot infer")
            case ArgInfo.Icit(i @ PiIcit.Impl(_)) =>
              val ety = tyAnnot(mty, V.Meta)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = insert(infer1(b)(using ctx2))(using ctx2)
              val qrt = ctx2.readback1(vrt)
              Infer1(
                Tm1.Lam(x, i, ety, eb),
                V.Pi(x, i, vty, Clos1.Clos(ctx.env, qrt))
              )

        case s @ S.App(_, f, a, i) =>
          i match
            case ArgInfo.Named(x) =>
              val (ef, fty) = insertPi(infer1(f), Until(x))
              apply1(fty, Impl, ef, a)
            case ArgInfo.Icit(Impl) =>
              val (ef, fty) = infer1(f)
              apply1(fty, Impl, ef, a)
            case ArgInfo.Icit(Expl) =>
              insertPi(infer(f)) match
                case Infer0(ef, fty, fcv) =>
                  val (t1, rcv, t2) = ensureFun(fty, fcv)
                  val ea = check0(a, t1, V.Val)
                  Infer0(Tm0.App(ef, ea), t2, rcv)
                case Infer1(ef, fty) => apply1(fty, Expl, ef, a)

        case S.Lift(_, ty) =>
          val cv = freshCV()
          val vcv = ctx.eval1(cv)
          Infer1(Tm1.Lift(cv, check1(ty, V.Type(vcv))), V.Meta)
        case S.Quote(_, tm) =>
          val (etm, vty, vcv) = infer0(tm)
          Infer1(etm.quote, V.Lift(vcv, vty))
        case S.Splice(_, tm) =>
          val (etm, vty) = insert(infer1(tm))
          forceAll1(vty) match
            case V.Lift(cv, a) => Infer0(etm.splice, a, cv)
            case vty =>
              val cv = freshCV()
              val vcv = ctx.eval1(cv)
              val vty2 = ctx.eval1(freshMeta(V.Type(vcv)))
              val etm2 = coe(etm, vty, V.Lift(vcv, vty2)).splice
              Infer0(etm2, vty2, vcv)

        case S.If(_, c, t, f) =>
          val ec = check0(c, V.Bool, V.Val)
          val (et, ty, cv) = infer0(t)
          val ef = check0(f, ty, cv)
          Infer0(Tm0.If(ctx.readback1(ty), ec, et, ef), ty, cv)

        case S.Hole(_, ox) =>
          val ty = ctx.eval1(freshMeta(V.Meta))
          ox.foreach(x => State.addHole(x, ty))
          val tm = freshMeta(ty)
          Infer1(tm, ty)

        case S.Match(_, None, _, _)       => err("cannot infer lambda match")
        case S.Match(_, Some(s), sty, cs) => inferMatch(s, sty, cs)

        case S.Unsafe(_, io, _, _) =>
          err(s"cannot infer unsafe${if io then "IO" else ""}")

        case S.UnitLit(_)       => err("cannot infer unit")
        case S.EmptyRecord(_)   => err("cannot infer empty record")
        case S.RecordCon1(_, _) => err("cannot infer meta record")
        case S.Tuple(_, _)      => err("cannot infer tuple")
        case S.RecordTy(_, _)   => err("cannot infer record type")

        case S.RecordCon0(_, fields) =>
          val xs = fields.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record")
          val cv = freshCV()
          val vcv = ctx.eval1(cv)
          def go(fs: Assoc[S]): (List[Tm0], AssocBind[VTy]) =
            fs match
              case Nil => (Nil, Nil)
              case (x, tm) :: rest =>
                val (etm, vty, vcv2) = infer0(tm)
                unify(vcv2, vcv)
                val (efields, tfields) = go(rest)
                (etm :: efields, (x.toBind, vty) :: tfields)
          val (efields, tfields) = go(fields)
          val vty = V.RecordTy0(vcv, tfields)
          val ty = ctx.readback1(vty)
          Infer0(Tm0.RecordCon(ty, efields), vty, vcv)

  // projection elaboration
  private def inferProj(tm: S, p: Surface.ProjType)(using ctx: Ctx): Infer =
    debug(s"inferProj $tm.$p")
    insertPi(infer(tm)) match
      case Infer0(etm, vty, _) =>
        val (x, i, vrty) = inferProjTy0(vty, p)
        val rty = ctx.readback1(vrty)
        Infer0(Tm0.Proj(rty, etm, ProjType(x, i)), vrty, V.Val)
      case Infer1(etm, vty) =>
        forceAll1(vty) match
          case V.Lift(_, vty2) =>
            val (x, i, vrty) = inferProjTy0(vty2, p)
            val rty = ctx.readback1(vrty)
            Infer0(Tm0.Proj(rty, etm.splice, ProjType(x, i)), vrty, V.Val)
          case V.RecordTy1(fs) =>
            val (x, i, vrty) = inferProjRecordTy1(etm, fs, p)
            Infer1(Tm1.Proj(etm, ProjType(x, i)), vrty)
          case V.TypeCon1(m, dx, dps) =>
            val (x, i, vrty) = inferProjTypeCon1(etm, vty, m, dx, dps, p)
            Infer1(Tm1.Proj(etm, ProjType(x, dps.size + i)), vrty)
          case _ => err(s"cannot project from ${ctx.pretty1(vty)}")

  private def inferProjTy0(vty: VTy, p: Surface.ProjType)(using
      ctx: Ctx
  ): (Option[Name], Int, VTy) =
    forceAll1(vty) match
      case V.TypeCon0(m, dx, dps) =>
        State.getGlobalDirect(m, dx) match
          case Some(GlobalEntry.Data0(_, _, _, _, _, _, _, singleCon, _)) =>
            singleCon match
              case None =>
                err(
                  s"cannot project from ${ctx.pretty1(vty)}, type has multiple constructors"
                )
              case Some(cx) =>
                State.getGlobalDirect(m, cx) match
                  case Some(GlobalEntry.Con0(_, _, _, params, _, _, _, _, _)) =>
                    p match
                      case Surface.ProjType.Indexed(i) if i >= params.size =>
                        err(
                          s"cannot project from ${ctx.pretty1(vty)}, not enough parameters in constructor $cx"
                        )
                      case Surface.ProjType.Indexed(i) =>
                        val rty = eval1(params(i)._2)(using Env(dps.map(_._1)))
                        (None, i, rty)
                      case Surface.ProjType.Named(x) =>
                        params.zipWithIndex.find { case ((y, _), _) =>
                          y.equals(x)
                        } match
                          case None =>
                            err(
                              s"cannot project from ${ctx.pretty1(vty)}, no parameter named $x in constructor $cx"
                            )
                          case Some(((_, ty), i)) =>
                            val rty =
                              eval1(ty)(using Env(dps.map(_._1)))
                            (Some(x), i, rty)
                  case _ => impossible()
          case _ => impossible()
      case V.RecordTy0(_, fs) =>
        @tailrec
        def go(fs: AssocBind[VTy], ix: Int): (Option[Name], Int, VTy) =
          fs match
            case Nil => err(s"failed to project .$p")
            case (x, ty) :: fs =>
              val found = p match
                case Surface.ProjType.Named(y)     => x.equals(y)
                case Surface.ProjType.Indexed(ix2) => ix == ix2
              if found then (x.toOption, ix, ty)
              else go(fs, ix + 1)
        go(fs, 0)
      case _ => err(s"cannot project from ${ctx.pretty1(vty)}")

  private def inferProjRecordTy1(tm: Tm1, clos: ClosRec, p: Surface.ProjType)(
      using ctx: Ctx
  ): (Option[Name], Int, VTy) =
    @tailrec
    def go(
        env: Env,
        fs: AssocBind[Ty],
        ix: Int
    ): (Option[Name], Int, VTy) =
      fs match
        case Nil => err(s"failed to project .$p")
        case (x, ty) :: fs =>
          val found = p match
            case Surface.ProjType.Named(y)     => x.equals(y)
            case Surface.ProjType.Indexed(ix2) => ix == ix2
          if found then (x.toOption, ix, eval1(ty)(using env))
          else
            val proj = ctx.eval1(Tm1.Proj(tm, ProjType(x.toOption, ix)))
            go(Env.Ext1(env, proj), fs, ix + 1)
    go(clos.env, clos.fields, 0)

  private def inferProjTypeCon1(
      tm: Tm1,
      dty: VTy,
      m: Name,
      dx: Name,
      dps: List[(V, Icit)],
      p: Surface.ProjType
  )(using ctx: Ctx): (Option[Name], Int, VTy) =
    State.getGlobalDirect(m, dx) match
      case Some(GlobalEntry.Data1(_, _, _, _, _, _, _, singleCon)) =>
        singleCon match
          case None =>
            err(
              s"cannot project from ${ctx.pretty1(dty)}, type has multiple constructors"
            )
          case Some(cx) =>
            State.getGlobalDirect(m, cx) match
              case Some(GlobalEntry.Con1(_, _, _, params, _, _, _, _, _)) =>
                val (ox, i) = p match
                  case Surface.ProjType.Indexed(i) if i >= params.size =>
                    err(
                      s"cannot project from ${ctx.pretty1(dty)}, not enough parameters in constructor $cx"
                    )
                  case Surface.ProjType.Indexed(i) => (None, i)
                  case Surface.ProjType.Named(x) =>
                    params.zipWithIndex.find { case ((y, _, _), _) =>
                      y.equals(x)
                    } match
                      case None =>
                        err(
                          s"cannot project from ${ctx.pretty1(dty)}, no parameter named $x in constructor $cx"
                        )
                      case Some(((_, _, _), i)) => (Some(x), i)
                def go(
                    env: Env,
                    ps: List[(Bind, PiIcit, Ty)],
                    ix: Int,
                    ix2: Int
                ): VTy =
                  (ix, ix2, ps) match
                    case (0, _, (_, _, ty) :: _) => eval1(ty)(using env)
                    case (n, ix, (x, _, _) :: rest) =>
                      val proj =
                        ctx.eval1(Tm1.Proj(tm, ProjType(x.toOption, ix)))
                      val nenv = Env.Ext1(env, proj)
                      go(nenv, rest, n - 1, ix + 1)
                    case _ => impossible()
                val rty = go(Env(dps.map(_._1)), params, i, 0)
                (ox, i, rty)
              case _ => impossible()
      case _ => impossible()

  // match elaboration
  private def inferMatch1ExType(vscrutty: VTy, sty: Option[(Bind, S)])(using
      ctx: Ctx
  ): Option[Clos1] =
    sty match
      case None => None
      case Some((x, b)) =>
        val nctx = ctx.bind1(x, ctx.readback1(vscrutty), vscrutty)
        val eb = check1(b, V.Meta)(using nctx)
        Some(Clos1.Clos(ctx.env, eb))

  private def inferMatch(
      scrut: S,
      sty: Option[(Bind, S)],
      cs: List[Surface.Case]
  )(using
      ctx: Ctx
  ): Infer =
    debug(
      s"inferMatch $scrut${sty.fold("")((x, t) => s" : $x => $t")} { ${cs.mkString(" | ")} }"
    )
    infer(scrut) match
      case Infer0(escrut, vscrutty, vscrutcv) =>
        if sty.isDefined then err("runtime level match cannot have type")
        unify(vscrutcv, V.Val)
        val excv = ctx.eval1(freshCV())
        val exty = ctx.eval1(freshMeta(V.Type(excv)))
        val ecs = checkCases0(vscrutty, cs, exty, excv)
        val ematch =
          Tm0.Case(ctx.readback1(exty), ctx.readback1(vscrutty), escrut, ecs)
        Infer0(ematch, exty, excv)
      case Infer1(escrut, vscrutty) =>
        forceAll1(vscrutty) match
          case V.Lift(vscrutcv, dty) =>
            if sty.isDefined then err("runtime level match cannot have type")
            unify(vscrutcv, V.Val)
            val excv = ctx.eval1(freshCV())
            val exty = ctx.eval1(freshMeta(V.Type(excv)))
            val ecs = checkCases0(dty, cs, exty, excv)
            val ematch =
              Tm0.Case(
                ctx.readback1(exty),
                ctx.readback1(dty),
                escrut.splice,
                ecs
              )
            Infer0(ematch, exty, excv)
          case fty =>
            val exty = inferMatch1ExType(vscrutty, sty) match
              case None =>
                val m = ctx.eval1(freshMeta(V.Meta))
                Clos1.Fun(_ => m)
              case Some(c) => c
            val ecs = checkCases1(escrut, fty, cs, exty)
            val rty = exty(ctx.eval1(escrut))
            Infer1(Tm1.Case(escrut, ecs), rty)

  private def checkMatch0(
      scrut: S,
      sty: Option[(Bind, S)],
      cs: List[Surface.Case],
      exty: VTy,
      excv: VTy
  )(using
      ctx: Ctx
  ): Tm0 =
    debug(
      s"checkMatch0 $scrut${sty.fold("")((x, t) => s" : $x => $t")} { ${cs.mkString(" | ")} } : ${ctx.pretty1(exty)}"
    )
    infer(scrut) match
      case Infer0(escrut, vscrutty, vscrutcv) =>
        if sty.isDefined then err("runtime level match cannot have type")
        unify(vscrutcv, V.Val)
        val ecs = checkCases0(vscrutty, cs, exty, excv)
        Tm0.Case(ctx.readback1(exty), ctx.readback1(vscrutty), escrut, ecs)
      case Infer1(escrut, vscrutty) =>
        forceAll1(vscrutty) match
          case V.Lift(vscrutcv, dty) =>
            if sty.isDefined then err("runtime level match cannot have type")
            unify(vscrutcv, V.Val)
            val ecs = checkCases0(dty, cs, exty, excv)
            Tm0.Case(
              ctx.readback1(exty),
              ctx.readback1(dty),
              escrut.splice,
              ecs
            )
          case fty =>
            val res = inferMatch1ExType(vscrutty, sty)
            val rexty1 = Clos1.Fun(_ => V.Lift(excv, exty))
            val rexty2 = res.getOrElse(rexty1)
            val tm =
              Tm1.Case(escrut, checkCases1(escrut, fty, cs, rexty2)).splice
            res.foreach { a =>
              val v = ctx.eval1(escrut)
              unify(a(v), rexty1(v))
            }
            tm

  private def checkMatch1(
      scrut: S,
      sty: Option[(Bind, S)],
      cs: List[Surface.Case],
      exty: VTy
  )(using
      ctx: Ctx
  ): Tm1 =
    debug(
      s"checkMatch1 $scrut${sty.fold("")((x, t) => s" : $x => $t")} { ${cs.mkString(" | ")} } : ${ctx.pretty1(exty)}"
    )
    infer(scrut) match
      case Infer0(escrut, vscrutty, vscrutcv) =>
        if sty.isDefined then err("runtime level match cannot have type")
        unify(vscrutcv, V.Val)
        val excv = ctx.eval1(freshCV())
        val exty2 = ctx.eval1(freshMeta(V.Type(excv)))
        unify(exty, V.Lift(excv, exty2))
        val ecs = checkCases0(vscrutty, cs, exty2, excv)
        Tm0
          .Case(ctx.readback1(exty2), ctx.readback1(vscrutty), escrut, ecs)
          .quote
      case Infer1(escrut, vscrutty) =>
        forceAll1(vscrutty) match
          case V.Lift(vscrutcv, dty) =>
            if sty.isDefined then err("runtime level match cannot have type")
            unify(vscrutcv, V.Val)
            val excv = ctx.eval1(freshCV())
            val exty2 = ctx.eval1(freshMeta(V.Type(excv)))
            unify(exty, V.Lift(excv, exty2))
            val ecs = checkCases0(dty, cs, exty2, excv)
            Tm0
              .Case(
                ctx.readback1(exty2),
                ctx.readback1(dty),
                escrut.splice,
                ecs
              )
              .quote
          case fty =>
            val res = inferMatch1ExType(vscrutty, sty)
            val rexty1 = Clos1.Fun(_ => exty)
            val rexty2 = res.getOrElse(rexty1)
            val tm = Tm1.Case(
              escrut,
              checkCases1(escrut, fty, cs, rexty2)
            )
            res.foreach { a =>
              val v = ctx.eval1(escrut)
              unify(a(v), rexty1(v))
            }
            tm

  private def checkCases0(
      vscrutty: VTy,
      cs: List[Surface.Case],
      exty: VTy,
      excv: VTy
  )(using
      ctx: Ctx
  ): Cases0 =
    debug(
      s"checkCases0 ${ctx.pretty1(vscrutty)} { ${cs.mkString(" | ")} } : ${ctx.pretty1(exty)}"
    )
    val (m, dx, ps) = forceAll1(vscrutty) match
      case V.TypeCon0(m, dx, ps) => (m, dx, ps.map((t, _) => t))
      case _ =>
        err(s"expected datatype in match but got ${ctx.pretty1(vscrutty)}")
    val (dps, cons) = State.getGlobalDirect(m, dx) match
      case Some(GlobalEntry.Data0(_, _, dps, cs, _, _, _, _, _)) =>
        (dps, cs.toSet)
      case _ => impossible()
    val psenv = Env(ps)
    inline def conTypes(m: Name, cx: Name): List[VTy] =
      State.getGlobalDirect(m, cx) match
        case Some(GlobalEntry.Con0(_, _, _, params, _, _, _, _, _)) =>
          params.map((_, ty) => eval1(ty)(using psenv))
        case _ => impossible()
    inline def goBranch(m: Name, cx: Name, ps: List[(Bind, Icit)], b: S)(using
        ctx: Ctx
    ): (List[(Bind, Ty)], Tm0) =
      val (innerctx, nps) =
        ps.zip(conTypes(m, cx)).foldLeft[(Ctx, List[(Bind, Ty)])]((ctx, Nil)) {
          case ((innerctx, nps), ((x, i), ty)) =>
            if i == Impl then
              err(s"runtime match cases cannot have implicit parameters")
            val rty = ctx.readback1(ty)
            (
              innerctx.bind0(x, rty, ty, Tm1.Val, V.Val),
              nps :+ (x, rty)
            )
        }
      val nb = check0(b, exty, excv)(using innerctx)
      (nps, nb)
    def goCases(
        cs: List[Surface.Case],
        cons: Set[Name],
        seen: Set[Name]
    ): Cases0 =
      cs match
        case Nil =>
          if cons.nonEmpty then
            err(
              s"match is not exhaustive, constructors left: ${cons.mkString(", ")}"
            )
          Cases0.Empty
        case Surface.Case(pos, cx, ps, b) :: r =>
          enter(pos):
            cx match
              case DontBind =>
                if r.nonEmpty then err(s"otherwise branch must be the last one")
                if ps.nonEmpty then
                  err(s"otherwise branch cannot have parameters")
                Cases0.Otherwise(check0(b, exty, excv))
              case DoBind(cx) =>
                if !cons.contains(cx) then
                  err(s"constructor not part of datatype in match: $cx")
                if seen.contains(cx) then
                  err(s"duplicate constructor in match: $cx")
                val (eps, eb) = goBranch(m, cx, ps, b)
                val er = goCases(r, cons - cx, seen + cx)
                Cases0.Ext(cx, eps, eb, er)
    goCases(cs, cons, Set.empty)

  private def checkCases1(
      escrut: Tm1,
      vscrutty: VTy,
      cs: List[Surface.Case],
      exty: Clos1
  )(using
      ctx: Ctx
  ): Cases1 =
    debug(
      s"checkCases1 $escrut : ${ctx.pretty1(vscrutty)} { ${cs.mkString(" | ")} } : ${ctx.prettyClos1(Name("x").toBind, exty)}"
    )
    val (m, dx, ps) = forceAll1(vscrutty) match
      case V.TypeCon1(m, dx, ps) => (m, dx, ps.map((t, _) => t))
      case _ =>
        err(s"expected datatype in match but got ${ctx.pretty1(vscrutty)}")
    val (dps, cons) = State.getGlobalDirect(m, dx) match
      case Some(GlobalEntry.Data1(_, _, dps, cs, _, _, _, _)) => (dps, cs.toSet)
      case _                                                  => impossible()
    val psenv = Env(ps)
    inline def conInfo(m: Name, cx: Name): (Tm1, List[(Bind, PiIcit, Ty)]) =
      State.getGlobalDirect(m, cx) match
        case Some(GlobalEntry.Con1(_, _, _, params, _, _, con, _, _)) =>
          (con, params)
        case _ => impossible()
    inline def goBranch(m: Name, cx: Name, ps: List[(Bind, Icit)], b: S)(using
        ctx: Ctx
    ): (List[(Bind, Icit, Ty)], Tm1) =
      val (con, cps) = conInfo(m, cx)
      def goParams(
          env: Env,
          con: V,
          ps: List[(Bind, Icit)],
          cps: List[(Bind, PiIcit, Ty)]
      )(using
          ctx: Ctx
      ): (Ctx, V, List[(Bind, Icit, Ty)]) =
        (ps, cps) match
          case (Nil, Nil) => (ctx, con, Nil)
          case ((x, i) :: psr, (_, i2, pty) :: cpsr)
              if i == i2.toIcit => // match
            val ety = ctx.readback1(eval1(pty)(using env))
            val nctx1 = ctx.bind1(x, ety, ctx.eval1(ety))
            val (nctx2, rcon, nps) =
              goParams(
                Env.Ext1(env, V.Var(ctx.lvl)),
                vapp(con, V.Var(ctx.lvl), i),
                psr,
                cpsr
              )(using nctx1)
            (nctx2, rcon, (x, i, ety) :: nps)
          case (ps, (x, PiIcit.Impl(_), pty) :: cpsr) => // insertion
            val ety = ctx.readback1(eval1(pty)(using env))
            val nctx1 = ctx.insert1(x, ety)
            val (nctx2, rcon, nps) =
              goParams(
                Env.Ext1(env, V.Var(ctx.lvl)),
                vappI(con, V.Var(ctx.lvl)),
                ps,
                cpsr
              )(using nctx1)
            (nctx2, rcon, (DontBind, Impl, ety) :: nps)
          case _ => err(s"match case mismatch")
      val (innerctx, vcon, nps) = goParams(psenv, ctx.eval1(con), ps, cps)
      val nb = check1(b, exty(vcon))(using innerctx)
      (nps, nb)
    def goCases(
        cs: List[Surface.Case],
        cons: Set[Name],
        seen: Set[Name]
    ): Cases1 =
      cs match
        case Nil =>
          if cons.nonEmpty then
            err(
              s"match is not exhaustive, constructors left: ${cons.mkString(", ")}"
            )
          Cases1.Empty
        case Surface.Case(pos, cx, ps, b) :: r =>
          enter(pos):
            cx match
              case DontBind =>
                if r.nonEmpty then err(s"otherwise branch must be the last one")
                if ps.nonEmpty then
                  err(s"otherwise branch cannot have parameters")
                Cases1.Otherwise(check1(b, exty(ctx.eval1(escrut))))
              case DoBind(cx) =>
                if !cons.contains(cx) then
                  err(s"constructor not part of datatype in match: $cx")
                if seen.contains(cx) then
                  err(s"duplicate constructor in match: $cx")
                val (eps, eb) = goBranch(m, cx, ps, b)
                val er = goCases(r, cons - cx, seen + cx)
                Cases1.Ext(cx, eps, eb, er)
    goCases(cs, cons, Set.empty)

  // elaboration
  private def retryAllChecks(): Unit =
    val unchecked = State.getUnchecked()
    if unchecked.nonEmpty then
      debug(s"retrying all checks ($unchecked.size)")
      unchecked.foreach { (c, ctx, tm, ty, m) =>
        given Ctx = ctx
        debug(s"resolve check ??$c")
        val (etm, ety) = insert(infer1(tm))
        val ctm = coe(etm, ety, ty)
        State.checkDone(c, ctm)
        Unification.unifyPlaceholder(ctx, ctm, m)
      }

  private def checkUnsolvedMetas()(using ctx: Ctx): Unit =
    val ums = State.unsolvedMetas()
    if ums.nonEmpty then
      val str =
        ums.map((id, ty) => s"?$id : ${ctx.pretty1(ty)}").mkString("\n")
      err(s"there are unsolved metas:\n$str")

  private def checkDeclaredDataTypes()(using ctx: Ctx): Unit =
    State.declaredDataTypes() match
      case Nil => ()
      case ds =>
        err(
          s"there are declared datatypes without a definition: ${ds.mkString(", ")}"
        )

  private def freeze()(using ctx: Ctx): Unit =
    // checkUnsolvedMetas()
    State.freezeMetas()

  private def checkAccessibility(ty: VTy)(using ctx: Ctx): Unit =
    debug(s"checkAccessibility ${ctx.pretty1(ty)}")
    def checkGlobal(m: Name, x: Name): Option[String] =
      if !State.checkAccessibility(m, x) then
        Some(s"escaping private definition $m.$x in type: ${ctx.pretty1(ty)}")
      else None
    val errs = allGlobals(ty).flatMap(checkGlobal)
    if errs.nonEmpty then err(errs.mkString("\n"))

  private def elaborateDefInner(d: Surface.Def)(using ctx: Ctx): Unit =
    d match
      case Surface.Def.Def0(_, pub, x, mty, v) =>
        if State.currentModuleHasName(x) || State.hasImport(x) then
          err(s"duplicate definition $x")
        val (ev, ty, cv, vty, vcv) = mty match
          case None =>
            val (ev, vty, vcv) = infer0(v)
            (ev, ctx.readback1(vty), ctx.readback1(vcv), vty, vcv)
          case _ =>
            val cv = freshCV()
            val vcv = ctx.eval1(cv)
            val ety = mty match
              case None      => freshMeta(V.Type(vcv))
              case Some(sty) => check1(sty, V.Type(vcv))
            val vty = ctx.eval1(ety)
            val ev = check0(v, vty, vcv)(using ctx)
            (ev, ety, cv, vty, vcv)
        if pub then checkAccessibility(vty)
        State.addGlobal(
          GlobalEntry.Def0(pub, x, ev, ty, cv, ctx.eval0(ev), vty, vcv)
        )
      case Surface.Def.Def1(_, pub, auto, x, mty, v) =>
        given ctx: Ctx = State.getBaseCtx.enter(d.pos)
        if State.currentModuleHasName(x) || State.hasImport(x) then
          err(s"duplicate definition $x")
        val (ev0, ty0, vty0) = mty match
          case None =>
            val (ev, vty) = infer1(v)
            (ev, ctx.readback1(vty), vty)
          case Some(sty) =>
            val ety = check1(sty, V.Meta)
            val vty = ctx.eval1(ety)
            val ev = check1(v, vty)
            (ev, ety, vty)
        val (ev, ty) = generalize(State.getVars, ev0, ctx.eval1(ev0), ty0, vty0)
        val vv = ctx.eval1(ev)
        val vty = ctx.eval1(ty)
        if pub then checkAccessibility(vty)
        if auto then
          val (m, dx, _) = checkAutoDef(vty)
          State.addAuto(State.currentModule, x, m, dx)
        State.addGlobal(GlobalEntry.Def1(pub, x, ev, ty, vv, vty))
      case Surface.Def.Data(_, pub, meta, opts, x, ps, univ, cs) =>
        val u = univ match
          case Some(ty) =>
            val ety = check1(ty, V.Meta)
            val vty = ctx.eval1(ety)
            forceAll1(vty) match
              case V.Meta  => Some(true)
              case V.TypeV => Some(false)
              case _ =>
                err(s"invalid universe type for datatype: ${ctx.pretty1(ety)}")
          case None => None
        val isMeta = (meta, u) match
          case (Some(true), Some(true))   => true
          case (Some(false), Some(false)) => false
          case (Some(b), None)            => b
          case (None, Some(b))            => b
          case _ =>
            val hasImplParam = ps.exists((_, i, _) => i.isImpl) ||
              cs.exists(c => c.params.exists((_, i, _) => i.isImpl))
            // TODO: adjust this is runtime datatypes allow implicit parameters
            if hasImplParam then true
            else err(s"ambigious universe for datatype")
        if isMeta then
          if opts.nonEmpty then err(s"only runtime datatypes can have options")
          elaborateData1(pub, x, ps, cs)
        else elaborateData0(pub, opts, x, ps, cs)
      case d @ Surface.Def.DeclareData(_, x, ty) =>
        if State.currentModuleHasName(x) || State.hasImport(x) then
          err(s"duplicate definition $x")
        val ety = check1(ty, V.Meta)
        val vty = ctx.eval1(ety)
        val isMeta = checkDeclaredType(x, vty)
        val tm =
          if isMeta then Tm1.TypeCon1(State.currentModule, x)
          else Tm1.TypeCon0(State.currentModule, x)
        State.addGlobal(GlobalEntry.DeclaredData(x, tm, vty))
      case Surface.Def.Variable(_, vs) =>
        given ctx: Ctx = State.getBaseCtx.enter(d.pos)
        val (basectx, evs) =
          vs.foldLeft[(Ctx, List[(Bind, PiIcit, Ty)])]((ctx, Nil)) {
            case ((ctx, evs), (p, x, i, ty)) =>
              val ety = check1(ty, V.Meta)(using ctx.enter(p))
              val bx = DoBind(x)
              (ctx.bind1(bx, ety, ctx.eval1(ety)), evs :+ ((bx, i, ety)))
          }
        State.addVars(basectx, evs)
      case Surface.Def.VariableEnd(_) =>
        if State.hasVars then State.endVars()
        else err("there are no generalized variables to end")

  private def generalize(
      vars: List[(Bind, PiIcit, Ty)],
      tm: Tm1,
      v: V,
      ty: Ty,
      vty: VTy
  ): (Tm1, Ty) =
    @tailrec
    def go(
        lvl: Lvl,
        rvars: List[(Bind, PiIcit, Ty)],
        res: List[Boolean],
        lvls: Set[Lvl]
    ): List[Boolean] =
      rvars match
        case Nil => res
        case hd :: tl =>
          go(lvl - 1, tl, lvls.contains(lvl) :: res, lvls)
    if vars.isEmpty then (tm, ty)
    else
      val slvl = mkLvl(vars.size)
      val rvars = vars.reverse
      val uty = go(slvl, rvars, Nil, allLocals(vty))
      val utm = go(slvl, rvars, Nil, allLocals(v))
      val u = uty.zip(utm).map(_ || _)
      val ety = vars.zip(u).foldRight(ty) { case (((x, i, t), u), ty) =>
        if u then Tm1.Pi(x, i, t, ty) else Tm1.Wk1(ty)
      }
      val etm = vars.zip(u).foldRight(tm) { case (((x, i, t), u), tm) =>
        if u then Tm1.Lam(x, i, t, tm) else Tm1.Wk1(tm)
      }
      (etm, ety)

  // returns true if meta, false if type
  private def checkDeclaredType(dx: Name, ty: VTy)(using ctx: Ctx): Boolean =
    forceAll1(ty) match
      case V.Pi(x, i, a, b) =>
        val nctx = ctx.bind1(x, ctx.readback1(a), a)
        checkDeclaredType(dx, b(V.Var(ctx.lvl)))(using nctx)
      case V.Meta  => true
      case V.TypeV => false
      case _ =>
        err(s"invalid universe for declared datatype $dx: ${ctx.pretty1(ty)}")

  private def elaborateData1(
      pub: Boolean,
      x: Name,
      ps: List[(Name, Icit, S)],
      cs: List[Surface.Constructor]
  )(using ctx: Ctx): Unit =
    val declaredTy = State.getDeclaredDataType(x)
    declaredTy match
      case None if State.currentModuleHasName(x) || State.hasImport(x) =>
        err(s"duplicate definition $x")
      case Some(_) => State.removeDeclaredDataType(x)
      case _       => ()
    def goParams(
        ctx: Ctx,
        ps: List[(Name, Icit, S)]
    ): (Ctx, List[(Name, Icit, Ty)]) =
      ps match
        case Nil => (ctx, Nil)
        case (px, i, ty) :: rest =>
          val ety = check1(ty, V.Meta)(using ctx)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind1(px.toBind, ety, vty)
          val (fnctx, erest) = goParams(nctx, rest)
          (fnctx, (px, i, ety) :: erest)
    val (datactx, eps) = goParams(ctx, ps)
    val unitCons = cs.filter(c =>
      c.params.isEmpty
    ) // TODO: this should ignore implicit params
    val unitCon =
      if unitCons.size == 1 then Some(unitCons.head.name) else None
    val singleCon = if cs.size == 1 then Some(cs.head.name) else None
    val ty = Tm1.TypeCon1(State.currentModule, x)
    val fulltype = eps.foldRight(Tm1.MetaU) { case ((px, i, ty), rt) =>
      Tm1.Pi(px.toBind, PiIcit(i), ty, rt)
    }
    val vty = ctx.eval1(fulltype)
    declaredTy.foreach(vty2 => unify(vty2, vty))
    if pub then checkAccessibility(vty)
    State.addGlobal(
      GlobalEntry.Data1(
        pub,
        x,
        eps,
        cs.map(_.name),
        ty,
        vty,
        unitCon,
        singleCon
      )
    )
    cs.zipWithIndex.foreach {
      case (Surface.Constructor(pos, cpub, cx, cps), ix) =>
        given conctx: Ctx = datactx.enter(pos)
        if State.currentModuleHasName(cx) || State.hasImport(cx) then
          err(s"duplicate name $cx")
        def goConParams(
            ctx: Ctx,
            cps: List[(Bind, PiIcit, S)]
        ): List[(Bind, PiIcit, Ty)] =
          cps match
            case Nil => Nil
            case (px, i, ty) :: rest =>
              val ety = check1(ty, V.Meta)(using ctx)
              val vty = ctx.eval1(ety)
              val nctx = ctx.bind1(px, ety, vty)
              (px, i, ety) :: goConParams(nctx, rest)
        val ecps = goConParams(conctx, cps)
        val tyapp =
          ps.zipWithIndex.foldRight(ty) { case (((_, i, _), ix), ty) =>
            Tm1.App(ty, Tm1.Var(mkIx(ix + ecps.size)), i)
          }
        val cty0 = ecps.foldRight(tyapp) { case ((x, i, pty), rty) =>
          Tm1.Pi(x, i, pty, rty)
        }
        val cty =
          eps.foldRight(cty0) { case ((x, _, ty), rty) =>
            Tm1.Pi(x.toBind, PiIcit.ImplU, ty, rty)
          }
        val vcty = ctx.eval1(cty)
        if cpub then checkAccessibility(vcty)
        State.addGlobal(
          GlobalEntry.Con1(
            cpub,
            cx,
            eps,
            ecps,
            x,
            ix,
            Tm1.Con1(State.currentModule, x, cx),
            cty,
            vcty
          )
        )
    }

  private def elaborateData0(
      pub: Boolean,
      opts: List[DataOption],
      x: Name,
      ps0: List[(Name, Icit, S)],
      cs: List[Surface.Constructor]
  )(using ctx: Ctx): Unit =
    if opts.contains(DataOption.Record) && cs.size != 1 then
      err(s"data with record option should have exactly on constructor: $x")
    val declaredTy = State.getDeclaredDataType(x)
    declaredTy match
      case None if State.currentModuleHasName(x) || State.hasImport(x) =>
        err(s"duplicate definition $x")
      case Some(_) => State.removeDeclaredDataType(x)
      case _       => ()
    val ps = ps0.map { (x, i, ty) =>
      if (i == Impl) err("runtime datatypes cannot have implicit parameters")
      val ety = check1(ty, V.Meta)
      unify(ctx.eval1(ety), V.TypeV)
      x
    }
    val unitCons = cs.filter(c => c.params.isEmpty)
    val unitCon =
      if unitCons.size == 1 then Some(unitCons.head.name) else None
    val singleCon = if cs.size == 1 then Some(cs.head.name) else None
    val ty = Tm1.TypeCon0(State.currentModule, x)
    val vty = ps.foldRight(V.TypeV)((_, rt) => V.fun1(V.TypeV, rt))
    declaredTy.foreach(vty2 => unify(vty2, vty))
    if pub then checkAccessibility(vty)
    State.addGlobal(
      GlobalEntry.Data0(
        pub,
        x,
        ps,
        cs.map(_.name),
        ty,
        vty,
        unitCon,
        singleCon,
        opts
      )
    )
    val datactx =
      ps.foldLeft(ctx)((ctx, x) => ctx.bind1(x.toBind, Tm1.TypeV, V.TypeV))
    cs.zipWithIndex.foreach {
      case (Surface.Constructor(pos, cpub, cx, cps), ix) =>
        given conctx: Ctx = datactx.enter(pos)
        if State.currentModuleHasName(cx) || State.hasImport(cx) then
          err(s"duplicate name $cx")
        val eps = cps.map { (x, i, t) =>
          if (i.isImpl)
            err("runtime datatype constructors cannot have implicit parameters")
          (x, check1(t, V.TypeV))
        }
        val tyapp =
          ps.indices.foldRight(ty)((i, ty) =>
            Tm1.App(ty, Tm1.Var(mkIx(i)), Expl)
          )
        val cty0 = eps.foldRight(Tm1.Lift(Tm1.Val, tyapp)) {
          case ((x, pty), rty) =>
            Tm1.Pi(x, PiIcit.Expl, Tm1.Lift(Tm1.Val, pty), Tm1.Wk1(rty))
        }
        val cty =
          ps.foldRight(cty0)((x, rty) =>
            Tm1.Pi(x.toBind, PiIcit.ImplU, Tm1.TypeV, rty)
          )
        val vcty = ctx.eval1(cty)
        if cpub then checkAccessibility(vcty)
        State.addGlobal(
          GlobalEntry.Con0(
            cpub,
            cx,
            ps,
            eps,
            x,
            ix,
            Tm1.Con0(State.currentModule, x, cx),
            cty,
            vcty
          )
        )
    }

  private def elaborateDef(d: Surface.Def): Unit =
    debug(s"elaborate $d")
    given ctx: Ctx = Ctx.empty(d.pos)
    elaborateDefInner(d)
    var attempt = 0
    var continue = true
    debug(s"perform postponed autos ($attempt)")
    while continue do
      val autos = State.getPostponedAutos()
      if autos.isEmpty then continue = false
      else
        autos.foreach { (ctx, m, vty, _) =>
          debug(s"postponed auto: ${ctx.pretty1(vty)}")
          given Ctx = ctx
          val tm = searchAuto(vty, 0, true)
          unify(ctx.eval1(m), ctx.eval1(tm))
        }
        attempt += 1
        if attempt >= AutoSearchRetryLimit then continue = false
    retryAllChecks()
    val leftovers = State.getPostponedAutos()
    if leftovers.nonEmpty then
      val str =
        leftovers.map((ctx, _, vty, _) => ctx.pretty1(vty)).mkString(", ")
      err(s"unsolved autos: $str")
    freeze()

  private inline def showNamedHole(ctx: Ctx, x: Name, ty: VTy): String =
    s"hole _$x : ${ctx.pretty1(ty)}\n${ctx.show}"

  private def elaborate(mod: Surface.Module): Unit =
    debug(s"elaborate module ${mod.name}")
    State.enterModule(mod.pos, mod.name)
    mod.moduleAliases.foreach((m, r) => State.addModuleRenaming(m, r))
    mod.imports.foreach { case (p1, p2, rex, m, x, r) =>
      val ctx = Ctx.empty(mod.pos)
      val y = r.getOrElse(x)
      if !State.moduleExists(m) then
        err(s"undefined module $m in imports")(using ctx.enter(p1))
      else if !State.moduleHasName(m, x) then
        err(s"undefined name $m.$x in imports")(using ctx.enter(p2))
      else if !State.checkAccessibility(m, x) then
        err(s"inaccessible name $m.$x in imports")(using ctx.enter(p2))
      else if State.hasImport(y) then
        err(s"duplicate name in imports: $y")(using ctx.enter(p2))
      else State.addImport(m, x, y)
      if rex then State.addReexport(mod.name, y, m, x)
    }
    mod.defs.toList.foreach(elaborateDef)
    val holes = State.getHoles()
    if holes.nonEmpty then
      val hstr =
        holes.map((ctx, x, ty) => showNamedHole(ctx, x, ty)).mkString("\n\n")
      err(s"there are ${holes.size} holes:\n\n$hstr")(using Ctx.empty(mod.pos))
    checkUnsolvedMetas()(using Ctx.empty(mod.pos))
    checkDeclaredDataTypes()(using Ctx.empty(mod.pos))

  def elaborate(mod: List[Surface.Module]): Unit =
    debug(s"elaborate modules ${mod.map(_.name).mkString("[", ",", "]")}")
    State.setMetaSolveCallback(onMetaSolved)
    State.setCheckHandler((ctx, tm, ty) => check1(tm, ty)(using ctx))
    mod.foreach(elaborate)
