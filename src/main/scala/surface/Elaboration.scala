package surface

import common.Common.*
import common.Common.Icit.*
import common.Common.Bind.*
import common.Debug.debug
import core.Core.*
import core.Evaluation.*
import core.Evaluation.QuoteOption.UnfoldNone
import core.{Core, Unification}
import Ctx.*
import Surface.{ArgInfo, Tm}
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
  private inline def enter[A](pos: PosInfo)(inline action: Ctx ?=> A)(using
      ctx: Ctx
  ): A =
    action(using ctx.enter(pos))

  private def ensureFun(a: VTy)(using ctx: Ctx): (VTy, VTy, VTy) =
    forceAll1(a) match
      case Val1.Fun(a, bcv, b) => (a, bcv, b)
      case _ => err(s"expected function type but got ${ctx.pretty1(a)}")

  private def ensureFunN(n: Int, a: VTy, acv: VTy)(using
      ctx: Ctx
  ): (List[VTy], VTy, VTy) =
    if n == 0 then (Nil, acv, a)
    else
      val (t1, cv, t2) = ensureFun(a)
      val (ps, rcv, rt) = ensureFunN(n - 1, t2, cv)
      (t1 :: ps, rcv, rt)

  private def apply1(a: VTy, i: Icit, t: Tm1, u: Tm)(using ctx: Ctx): Infer =
    debug(s"apply1 ${ctx.pretty1(a)} $i @ $u")
    forceAll1(a) match
      case Val1.Pi(_, i2, a, b) =>
        if i != i2 then err(s"icit mismatch in apply1")
        val u2 = check1(u, a)
        Infer1(Tm1.App(t, u2, i), b(ctx.eval1(u2)))
      case Val1.Lift(_, Val1.Fun(a, bcv, b)) =>
        if i != Expl then err(s"icit mismatch in apply1")
        val u2 = check0(u, a, Val1.Val)
        Infer0(Tm0.App(t.splice, u2), b, bcv)
      case _ => err(s"cannot apply ${ctx.pretty1(a)}")

  // checking
  private def check0(tm: Tm, ty: VTy, cv: VTy)(using ctx: Ctx): Tm0 = ???

  private def check1(tm: Tm, ty: VTy)(using ctx: Ctx): Tm1 = ???

  // inference
  private def infer0(tm: Tm)(implicit ctx: Ctx): (Tm0, VTy, VTy) = ???

  private def infer1(tm: Tm)(using ctx: Ctx): (Tm1, VTy) = ???

  private def infer(tm: Tm)(using ctx: Ctx): Infer =
    enter(tm.pos):
      debug(s"infer $tm")
      tm match
        case Tm.CV(_)      => Infer1(Tm1.CV, Val1.UMeta)
        case Tm.Val(_)     => Infer1(Tm1.Val, Val1.CV)
        case Tm.Comp(_)    => Infer1(Tm1.Comp, Val1.CV)
        case Tm.UTy(_, cv) => Infer1(Tm1.UTy(check1(cv, Val1.CV)), Val1.UMeta)
        case Tm.UMeta(_)   => Infer1(Tm1.UMeta, Val1.UMeta)
        case Tm.Hole(_, _) => err("cannot infer hole")

        case Tm.Var(_, m, x) =>
          ctx.lookup(x) match
            case Some(NameInfo.Name0(x, ty, cv)) =>
              Infer0(Tm0.Var(x.toIx(using ctx.lvl)), ty, cv)
            case Some(NameInfo.Name1(x, ty)) =>
              Infer1(Tm1.Var(x.toIx(using ctx.lvl)), ty)
            case None =>
              State.getGlobal(m, x) match
                case Left((m, x, State.GlobalLookupFailure.ModuleNotFound)) =>
                  err(s"undefined variable $m.$x: undefined module")
                case Left((m, x, State.GlobalLookupFailure.GlobalNotFound)) =>
                  err(s"undefined variable $m.$x")
                case Left(
                      (m, x, State.GlobalLookupFailure.GlobalIsNotAccessible)
                    ) =>
                  err(s"inaccessible variable $m.$x")
                case Right((m, GlobalEntry.Def0(_, _, _, _, _, _, ty, cv))) =>
                  Infer0(Tm0.Global(m, x), ty, cv)
                case Right((m, GlobalEntry.Def1(_, _, _, _, v, ty))) =>
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
          val (ev, ety, ecv, vty, vcv) = mty match
            case None =>
              val (ev, vty, vcv) = infer0(v)
              (ev, ctx.quote1(vty), ctx.quote1(vcv), vty, vcv)
            case Some(ty) =>
              val (ety, k) = infer1(ty)
              val vcv = forceAll1(k) match
                case Val1.UTy(cv) => cv
                case _            => err("expected value type in let")
              val ecv = ctx.quote1(vcv)
              val vty = ctx.eval1(ety)
              val ev = check0(v, vty, vcv)
              (ev, ety, ecv, vty, vcv)
          val nctx = ctx.bind0(DoBind(x), ety, vty, ecv, vcv)
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
          val (ea, vta) = infer1(a)
          forceAll1(vta) match
            case Val1.UTy(cv) =>
              unify1(cv, Val1.Val)
              val (eb, k) = infer1(b)
              val vbcv = forceAll1(k) match
                case Val1.UTy(cv) => cv
                case _            => err("expected value type in pi")
              val bcv = ctx.quote1(vbcv)
              Infer1(Tm1.Fun(ea, bcv, eb), Val1.UTy(Val1.Comp))
            case Val1.UMeta =>
              val eb =
                check1(b, Val1.UMeta)(using
                  ctx.bind1(DontBind, ea, ctx.eval1(ea))
                )
              Infer1(Tm1.Pi(DontBind, Expl, ea, eb), Val1.UMeta)
            case _ => err("expected type for Pi parameter")
        case Tm.Pi(_, x, i, a, b) =>
          val ea = check1(a, Val1.UMeta)
          val eb = check1(b, Val1.UMeta)(using ctx.bind1(x, ea, ctx.eval1(ea)))
          Infer1(Tm1.Pi(x, i, ea, eb), Val1.UMeta)

        case Tm.Lam(_, x, i, Some(ty), b) =>
          i match
            case ArgInfo.Named(_)   => err("cannot infer")
            case ArgInfo.Icit(Expl) =>
              val (ety, k) = infer1(ty)
              val vty = ctx.eval1(ety)
              forceAll1(k) match
                case Val1.UMeta =>
                  val ctx2 = ctx.bind1(x, ety, vty)
                  val (eb, vrt) = infer1(b)(using ctx2)
                  val qrt = ctx2.quote1(vrt)
                  Infer1(
                    Tm1.Lam(x, Expl, ety, eb),
                    Val1.Pi(x, Expl, vty, Clos1.Clos(ctx.env, qrt))
                  )
                case Val1.UTy(cv) =>
                  unify1(cv, Val1.Val)
                  val ctx2 = ctx.bind1(x, ety, vty)
                  val (eb, vrt, vcv) = infer0(b)(using ctx2)
                  Infer0(
                    Tm0.Lam(x, ety, eb),
                    Val1.Fun(vty, vcv, vrt),
                    Val1.Comp
                  )
                case _ =>
                  err(
                    s"expected type or meta for lambda parameter type but got ${ctx.pretty1(k)}"
                  )
            case ArgInfo.Icit(Impl) =>
              val ety = check1(ty, Val1.UMeta)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = infer1(b)(using ctx2)
              val qrt = ctx2.quote1(vrt)
              Infer1(
                Tm1.Lam(x, Impl, ety, eb),
                Val1.Pi(x, Impl, vty, Clos1.Clos(ctx.env, qrt))
              )
        case Tm.Lam(_, _, _, _, _) => err("cannot infer")

        case Tm.App(_, f, a, i) =>
          i match
            case ArgInfo.Named(_)   => err("cannot infer named application")
            case ArgInfo.Icit(Impl) =>
              val (ef, fty) = infer1(f)
              apply1(fty, Impl, ef, a)
            case ArgInfo.Icit(Expl) =>
              infer(f) match
                case Infer0(ef, fty, _) =>
                  val (t1, rcv, t2) = ensureFun(fty)
                  val ea = check0(a, t1, Val1.Val)
                  Infer0(Tm0.App(ef, ea), t2, rcv)
                case Infer1(ef, fty) => apply1(fty, Expl, ef, a)

        case Tm.Lift(_, ty) =>
          val (ety, k) = infer1(ty)
          val cv = forceAll1(k) match
            case Val1.UTy(vcv) => ctx.quote1(vcv)
            case _             => err("expected value type in lift")
          Infer1(Tm1.Lift(cv, ety), Val1.UMeta)
        case Tm.Quote(_, tm) =>
          val (etm, vty, vcv) = infer0(tm)
          Infer1(etm.quote, Val1.Lift(vcv, vty))
        case Tm.Splice(_, tm) =>
          val (etm, vty) = infer1(tm)
          forceAll1(vty) match
            case Val1.Lift(cv, a) => Infer0(etm.splice, a, cv)
            case _                =>
              err(s"expected lifted type in splice but got ${ctx.pretty1(vty)}")

  // TODO: check that private types don't escape
  private def elaborate(defn: Surface.Def): Def = defn match
    case Surface.Def.D0(pos, public, name, ty, value) => ???
    case Surface.Def.D1(pos, public, name, ty, value) => ???

  private def elaborate(mod: Surface.Module): Module =
    State.enterModule(mod.name)
    mod.moduleAliases.foreach((m, r) => State.addModuleRenaming(m, r))
    mod.imports.foreach { case (x, (p1, p2, m, r)) =>
      val ctx = Ctx.empty
      if (!State.moduleExists(m))
        err(s"undefined module $m in imports")(using ctx.enter(p1))
      else if (!State.moduleHasName(m, x))
        err(s"undefined name $m.$x in imports")(using ctx.enter(p2))
      else State.addImport(m, x, r.getOrElse(x))
    }
    val ds = mod.defs.toList.map(elaborate)
    Module(mod.name, Defs(ds))

  def elaborate(mod: List[Surface.Module]): List[Module] =
    mod.map(elaborate)
