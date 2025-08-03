package surface

import common.Common.*
import common.Common.Icit.*
import common.Common.Bind.*
import common.Debug.debug
import core.Core.*
import core.Evaluation.*
import core.Evaluation.QuoteOption.UnfoldNone
import core.Unification
import Ctx.*
import Surface2.Tm
import State.GlobalEntry

object Elaboration:
  class ElaborationError(val pos: PosInfo, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"elaboration error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborationError(ctx.pos, msg)

  private enum Infer:
    case Infer0(tm: Tm0, ty: VTy, cv: VTy)
    case Infer1(tm: Tm1, ty: VTy)
  import Infer.*

  // unification
  private def unify1(a: VTy, b: VTy)(using ctx: Ctx): Unit =
    debug(s"unify1 ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}")
    try Unification.unify1(a, b)(using ctx.lvl)
    catch
      case ue: Unification.UnificationError =>
        err(
          s"failed to unify ${ctx.pretty1(a)} ~ ${ctx.pretty1(b)}: ${ue.msg}"
        )

  // coercion lifting helpers
  private def liftFun(a: VTy, b: VTy, bcv: VTy)(using ctx: Ctx): VTy =
    given l: Lvl = ctx.lvl + 1
    val qbcv = quote1(bcv, UnfoldNone)
    val qb = quote1(b, UnfoldNone)
    Val1.Pi(
      DontBind,
      Expl,
      Val1.Lift(Val1.Val, a),
      Clos1.Clos(ctx.env, Tm1.Lift(qbcv, qb))
    )

  private def quoteFun(x: Bind, a: VTy, t: Tm1)(using ctx: Ctx): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Tm1.Lam(
      DoBind(y),
      Expl,
      Tm1.Lift(Tm1.Val, ctx.quote1(a)),
      Tm1.Quote(Tm0.App(Tm0.Wk1(t.splice), Tm0.Splice(Tm1.Var(ix0))))
    )

  private def spliceFun(x: Bind, a: VTy, t: Tm1)(using ctx: Ctx): Tm1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    Tm1.Quote(
      Tm0.Lam(
        DoBind(y),
        ctx.quote1(a),
        Tm0.Splice(Tm1.App(Tm1.Wk0(t), Tm1.Quote(Tm0.Var(ix0)), Expl))
      )
    )

  // coercion
  private def coe(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Tm1 =
    def go(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Option[Tm1] =
      debug(
        s"coe ${ctx.pretty1(t)} from ${ctx.pretty1(a1)} to ${ctx.pretty1(a2)}"
      )
      (forceAll1(a1), forceAll1(a2)) match
        case (Val1.UTy(cv), Val1.UMeta) => Some(Tm1.Lift(ctx.quote1(cv), t))

        case (Val1.Pi(x, i, a1, b1), Val1.Pi(_, i2, a2, b2)) =>
          if i != i2 then err(s"icit mismatch in coercion")(using ctx)
          implicit val ctx2: Ctx = ctx.bind1(x, ctx.quote1(a2), a2)
          go(Tm1.Var(ix0), a2, a1) match
            case None =>
              go(
                Tm1.App(Tm1.Wk1(t), Tm1.Var(ix0), i),
                b1(ctx2.eval1(Tm1.Var(ix0))),
                b2(Var1(ctx.lvl))
              ).map(b => Tm1.Lam(x, i, ctx.quote1(a2), b))
            case Some(coev0) =>
              Some(
                Tm1.Lam(
                  x,
                  i,
                  ctx.quote1(a2),
                  coe(
                    Tm1.App(Tm1.Wk1(t), coev0, i),
                    b1(ctx2.eval1(coev0)),
                    b2(Var1(ctx.lvl))
                  )
                )
              )

        case (Val1.Lift(_, Val1.Fun(a, cv, b)), Val1.Pi(x, _, _, _)) =>
          Some(coe(quoteFun(x, a, t), liftFun(a, b, cv), a2))
        case (Val1.Lift(_, Val1.Fun(a, cv, b)), _) =>
          Some(coe(quoteFun(DontBind, a, t), liftFun(a, b, cv), a2))
        case (Val1.Pi(x, _, _, _), Val1.Lift(_, Val1.Fun(t1, cv, t2))) =>
          Some(spliceFun(x, t1, coe(t, a1, liftFun(t1, t2, cv))))
        case (_, Val1.Lift(_, Val1.Fun(t1, cv, t2))) =>
          Some(spliceFun(DontBind, t1, coe(t, a1, liftFun(t1, t2, cv))))

        case (_, _) => unify1(a1, a2); None
    go(t, a1, a2).getOrElse(t)

  // helpers

  // checking
  private def check0(tm: Tm, ty: VTy, cv: VTy)(using ctx: Ctx): Tm0 = ???

  private def check1(tm: Tm, ty: VTy)(using ctx: Ctx): Tm1 = ???

  // inference
  private def infer0(tm: Tm)(implicit ctx: Ctx): (Tm0, VTy, VTy) = ???

  private def infer1(tm: Tm)(using ctx: Ctx): (Tm1, VTy) = ???

  private def infer(tm: Tm)(using state: State, ctx: Ctx): Infer =
    enter(tm.pos):
      debug(s"infer $tm")
      tm match
        case Tm.CV(_)      => Infer1(Tm1.CV, Val1.UMeta)
        case Tm.Val(_)     => Infer1(Tm1.Val, Val1.CV)
        case Tm.Comp(_)    => Infer1(Tm1.Comp, Val1.CV)
        case Tm.UTy(_, cv) => Infer1(Tm1.UTy(check1(cv, Val1.CV)), Val1.UMeta)
        case Tm.UMeta(_)   => Infer1(Tm1.UMeta, Val1.UMeta)
        case Tm.Hole(_, _) => err("cannot infer hole")

        case Tm.Var(_, om, x) =>
          ctx.lookup(x) match
            case Some(NameInfo.Name0(x, ty, cv)) =>
              Infer0(Tm0.Var(x.toIx(using ctx.lvl)), ty, cv)
            case Some(NameInfo.Name1(x, ty)) =>
              Infer1(Tm1.Var(x.toIx(using ctx.lvl)), ty)
            case None =>
              val m = om.getOrElse(Name("xxx")) // TOOD: modules
              state.getGlobal(m, x) match
                case None => err(s"undefined variable $x")
                case Some(GlobalEntry.Def0(_, _, _, _, _, ty, cv)) =>
                  Infer0(Tm0.Global(m, x), ty, cv)
                case Some(GlobalEntry.Def1(_, _, _, v, ty)) =>
                  Infer1(Tm1.Global(m, x, v), ty)

        case Tm.LetRec(_, x, Some(ty), v, b) =>
          val ety = check1(ty, Val1.UTy(Val1.Comp))
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, Tm1.Comp, Val1.Comp)
          val ev = check0(v, vty, Val1.Comp)(using nctx)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(Tm0.LetRec(x, ety, ev, eb), rty, rcv)
        case Tm.LetRec(_, _, _, _, _) =>
          err("let rec requires a type annotation")

        case Tm.Let0(_, x, mty, v, b) =>
          val (ety, cv2, vcv2) =
            val cv2 = freshCV()
            val vcv2 = ctx.eval1(cv2)
            val ety = tyAnnot(mty, Val1.UTy(vcv2))
            (ety, cv2, vcv2)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(Tm0.Let(x, ety, ev, eb), rty, rcv)

        case Tm.Let1(_, x, mty, v, b) =>
          val (ev, lty, vlty) = mty match
            case None =>
              val (ev, vlty) = infer1(v)
              val lty = ctx.quote1(vlty)
              (ev, lty, vlty)
            case Some(ty) =>
              val lty = check1(ty, Val1.UMeta)
              val vlty = ctx.eval1(lty)
              val ev = check1(v, vlty)
              (ev, lty, vlty)
          val (eb, rty) =
            infer1(b)(using ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
          Infer1(Tm1.Let(x, lty, ev, eb), rty)

        case Tm.Pi(_, DontBind, Expl, a, b) =>
          val (ea, vta) = insert(infer1(a))
          forceAll1(vta) match
            case VU0(cv) =>
              unify1(cv, VCVV)
              val bcv = freshCV()
              val vbcv = ctx.eval1(bcv)
              val eb = check1(b, VU0(vbcv))
              Infer1(Fun(ea, bcv, eb), VU0(VCVC))
            case VU1 =>
              val eb = check1(b, VU1)(ctx.bind1(DontBind, ea, ctx.eval1(ea)))
              Infer1(Pi(DontBind, Expl, ea, eb), VU1)
            case _ => error("expected type for Pi parameter")
        case Tm.Pi(_, x, i, a, b) =>
          val ea = check1(a, VU1)
          val eb = check1(b, VU1)(ctx.bind1(x, ea, ctx.eval1(ea)))
          Infer1(Pi(x, i, ea, eb), VU1)

        case Tm.Lam(_, x, i, mty, b) =>
          i match
            case S.ArgNamed(_)   => error("cannot infer")
            case S.ArgIcit(Expl) => error("cannot infer")
            case S.ArgIcit(Impl) =>
              val ety = tyAnnot(mty, VU1)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = insert(infer1(b)(ctx2))(ctx2)
              val qrt = ctx2.quote1(vrt)
              Infer1(
                Lam1(x, Impl, ety, eb),
                VPi(x, Impl, vty, CClos1(ctx.env, qrt))
              )

        case Tm.App(_, f, a, i) =>
          i match
            case S.ArgNamed(x) =>
              val (ef, fty) = insertPi(infer1(f), Until(x))
              apply1(fty, Impl, ef, a)
            case S.ArgIcit(Impl) =>
              val (ef, fty) = infer1(f)
              apply1(fty, Impl, ef, a)
            case S.ArgIcit(Expl) =>
              insertPi(infer(f)) match
                case Infer0(ef, fty, fcv) =>
                  val (t1, rcv, t2) = ensureFun(fty, fcv)
                  val ea = check0(a, t1, VCVV)
                  Infer0(App0(ef, ea), t2, rcv)
                case Infer1(ef, fty) => apply1(fty, Expl, ef, a)

        case Tm.Lift(_, ty) =>
          val cv = freshCV()
          val vcv = ctx.eval1(cv)
          Infer1(Lift(cv, check1(ty, VU0(vcv))), VU1)
        case Tm.Quote(_, tm) =>
          val (etm, vty, vcv) = infer0(tm)
          Infer1(quote(etm), VLift(vcv, vty))
        case Tm.Splice(_, tm) =>
          val (etm, vty) = insert(infer1(tm))
          forceAll1(vty) match
            case VLift(cv, a) => Infer0(splice(etm), a, cv)
            case vty          =>
              val cv = freshCV()
              val vcv = ctx.eval1(cv)
              val vty2 = ctx.eval1(freshMeta(VU0(vcv)))
              val etm2 = splice(coe(etm, vty, VLift(vcv, vty2)))
              Infer0(etm2, vty2, vcv)

  private inline def enter[A](pos: PosInfo)(inline action: Ctx ?=> A)(using
      ctx: Ctx
  ): A =
    action(using ctx.enter(pos))
