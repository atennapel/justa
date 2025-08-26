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
import Surface as S
import common.State
import common.State.GlobalEntry

object Elaboration:
  class ElaborationError(val pos: PosInfo, val module: Name, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"elaboration error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborationError(ctx.pos, State.currentModule, msg)

  private enum Infer:
    case Infer0(tm: Tm0, ty: VTy, cv: VTy)
    case Infer1(tm: Tm1, ty: VTy)
  import Infer.*

  // unification
  private def unify(a: VTy, b: VTy)(using ctx: Ctx): Unit =
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

  private def liftRec(ts: Assoc[VTy])(using ctx: Ctx): ClosRec =
    def go(lvl: Lvl, ts: Assoc[VTy]): Assoc[Ty] =
      ts match
        case Nil           => Nil
        case (x, ty) :: tl =>
          val ety = Tm1.Lift(Tm1.Val, quote1(ty, UnfoldNone)(using lvl))
          (x, ety) :: go(lvl + 1, tl)
    ClosRec(ctx.env, go(ctx.lvl, ts))

  private def quoteRec(tm: Tm1, ts: Assoc[VTy])(using ctx: Ctx): Tm1 =
    ??? // TODO: requires projection

  private def spliceRec()(using ctx: Ctx): Tm1 =
    ??? // TODO: requires projection

  // coercion
  // TODO: handle records
  private def coe(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Tm1 =
    def goRec(tm: Tm1, ix: Int, fs1: ClosRec, fs2: ClosRec)(using
        ctx: Ctx
    ): List[(Boolean, Name, Tm1)] =
      (fs1.fields, fs2.fields) match
        case (Nil, Nil)                                   => Nil
        case ((x, ty1) :: tl1, (y, ty2) :: tl2) if x == y =>
          val va1 = eval1(ty1)(using fs1.env)
          val va2 = eval1(ty2)(using fs2.env)
          ??? // TODO: requires projection
        case _ =>
          err(s"coercion failure: ${ctx.pretty1(a1)} ~ ${ctx.pretty1(a2)}")

    def refineRec(fs: Assoc[Ty])(using ctx: Ctx): Assoc[VTy] =
      fs match
        case Nil           => Nil
        case (x, ty) :: tl =>
          val ety = ??? // TODO: needs metas
          (x, ety) :: refineRec(tl)

    def go(t: Tm1, a1: VTy, a2: VTy)(using ctx: Ctx): Option[Tm1] =
      debug(
        s"coe ${ctx.pretty1(t)} from ${ctx.pretty1(a1)} to ${ctx.pretty1(a2)}"
      )
      (forceAll1(a1), forceAll1(a2)) match
        case (Val1.UTy(cv), Val1.UMeta) => Some(Tm1.Lift(ctx.quote1(cv), t))

        case (Val1.Pi(x, i, a1, b1), Val1.Pi(_, i2, a2, b2)) =>
          if i != i2 then err(s"icit mismatch in coercion")(using ctx)
          given ctx2: Ctx = ctx.bind1(x, ctx.quote1(a2), a2)
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

        case (Val1.RecordTy1(ts1), Val1.RecordTy1(ts2)) =>
          val fs = goRec(t, 0, ts1, ts2)
          if fs.exists((b, _, _) => b) then
            Some(Tm1.RecordCon(fs.map((_, _, t) => t)))
          else None

        case (Val1.Lift(_, Val1.Fun(a, cv, b)), Val1.Pi(x, _, _, _)) =>
          Some(coe(quoteFun(x, a, t), liftFun(a, b, cv), a2))
        case (Val1.Lift(_, Val1.Fun(a, cv, b)), _) =>
          Some(coe(quoteFun(DontBind, a, t), liftFun(a, b, cv), a2))
        case (Val1.Pi(x, _, _, _), Val1.Lift(_, Val1.Fun(t1, cv, t2))) =>
          Some(spliceFun(x, t1, coe(t, a1, liftFun(t1, t2, cv))))
        case (_, Val1.Lift(_, Val1.Fun(t1, cv, t2))) =>
          Some(spliceFun(DontBind, t1, coe(t, a1, liftFun(t1, t2, cv))))

        case (_, _) => unify(a1, a2); None
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

  private def icitMatch(i: ArgInfo, x: Bind, i2: Icit): Boolean = i match
    case ArgInfo.Named(y) =>
      x match
        case DontBind  => false
        case DoBind(x) => x == y
    case ArgInfo.Icit(i) => i == i2

  private def isNotVar(t: Tm): Boolean = t match
    case Tm.Var(_, _) => false
    case _            => true

  private def coeQuote(t: Tm1, a1: VTy, a2: VTy, cv: VTy)(using ctx: Ctx): Tm0 =
    coe(t, a1, Val1.Lift(cv, a2)).splice

  private def splitLift(ty: VTy)(using ctx: Ctx): (VTy, VTy) =
    forceAll1(ty) match
      case Val1.Lift(cv, rty) => (rty, cv)
      case _ => err(s"expected quoted type but got ${ctx.pretty1(ty)}")

  // checking
  private def check0(tm: Tm, ty: VTy, cv: VTy)(using ctx: Ctx): Tm0 =
    debug(s"check0 $tm : ${ctx.pretty1(ty)} : ${ctx.pretty1(cv)}")
    enter(tm.pos):
      tm match
        case Tm.Lam(_, x, i, ma, b) =>
          if i != ArgInfo.Icit(Expl) then err(s"implicit lambda in Ty")
          val (t1, fcv, t2) = ensureFun(ty)
          ma.foreach { sty =>
            unify(ctx.eval1(check1(sty, VTyVal)), t1)
          }
          val qt1 = ctx.quote1(t1)
          Tm0.Lam(
            x,
            qt1,
            check0(b, t2, fcv)(using ctx.bind0(x, qt1, t1, Tm1.Val, Val1.Val))
          )

        case Tm.LetRec(_, x, Some(pty), v, b) =>
          val ety = check1(pty, VTyComp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, Tm1.Comp, Val1.Comp)
          val ev = check0(v, vty, Val1.Comp)(using nctx)
          val eb = check0(b, ty, cv)(using nctx)
          Tm0.LetRec(x, ety, ev, eb)
        case Tm.LetRec(_, _, None, _, _) =>
          err("let rec requires type annotation")

        case Tm.Let0(_, x, ma, v, b) =>
          val (ev, ety, ecv, vty, vcv) = ma match
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
          val eb = check0(b, ty, cv)(using nctx)
          Tm0.Let(x, ety, ev, eb)

        case Tm.Hole(_, x) =>
          err(s"checking _${x.getOrElse("")} against ${ctx.pretty1(ty)}")

        case Tm.Tuple(_, Nil) =>
          forceAll1(ty) match
            case VTypeCon(_, m, x, dps) =>
              val uc = State.getGlobal(m, x) match
                case Some(GlobalEntry.Data(_, _, _, _, _, _, uc)) => uc
                case _ => impossible()
              uc match
                case None =>
                  err(
                    s"cannot check () against ${ctx.pretty1(ty)}: type does not have exactly one constructor with zero parameters"
                  )
                case Some(cx) =>
                  State.getGlobal(m, cx) match
                    case Some(
                          GlobalEntry.DataCon(_, _, _, ps, _, _, tm, _, _)
                        ) =>
                      if ps.nonEmpty then
                        err(
                          s"cannot check () against ${ctx.pretty1(ty)}: too many parameters for suitable constructor $cx"
                        )
                      dps
                        .foldLeft(tm) { case (tm, (ty, _)) =>
                          Tm1.App(tm, ctx.quote1(ty), Impl)
                        }
                        .splice
                    case _ => impossible()
            case _ => err(s"cannot check () against ${ctx.pretty1(ty)}")

        case Tm.Splice(_, t) => check1(t, Val1.Lift(cv, ty)).splice

        case Tm.Instr(_, op, args) =>
          forceAll1(cv) match
            case Val1.Val => ()
            case _        =>
              err(
                s"instr can only be checked against a value type but got ${ctx.pretty1(ty)}"
              )
          val (eargs, vts) = args.map(inferValue).unzip
          Tm0.Instr(op, vts.map(t => ctx.quote1(t)), ctx.quote1(ty), eargs)

        case Tm.If(p, c, a, b) =>
          val (ec, dt) = checkIfCond(p, c)
          val ea = check0(a, ty, cv)
          val eb = check0(b, ty, cv)
          val cs =
            List((Name("True"), Tm0.Wk0(ea)), (Name("False"), Tm0.Wk0(eb)))
          Tm0.Match(ctx.quote1(ty), dt, ec, cs, None)

        case Tm.Match(_, Some(scrut), cs, o) =>
          val (escrut, vdty, _) = infer0(scrut)
          val (etm, _, _) = inferMatch(escrut, vdty, cs, o, Some((ty, cv)))
          etm
        case Tm.Match(_, None, cs, o) =>
          val (pty, rcv, rty) = forceAll1(ty) match
            case Val1.Fun(pty, rcv, rty) => (pty, rcv, rty)
            case _                       =>
              err(
                s"match without scrutinee can only be matched against a function type, but got ${ctx.pretty1(ty)}"
              )
          val qpty = ctx.quote1(pty)
          val nctx =
            ctx.bind0(DontBind, qpty, pty, Tm1.Val, Val1.Val)
          val (etm, _, _) =
            inferMatch(Tm0.Var(ix0), pty, cs, o, Some((rty, rcv)))(using
              nctx
            )
          Tm0.Lam(DoBind(Name("x")), qpty, etm)

        case Tm.RecordCon0(_, fs0) =>
          forceAll1(ty) match
            case Val1.RecordTy0(ts) =>
              val fs = orderFields(ty, fs0, ts)
              def go(fs: Assoc[Tm], ts: Assoc[VTy]): List[Tm0] =
                (fs, ts) match
                  case (Nil, Nil)                                => Nil
                  case ((x, tm) :: fs, (y, vty) :: ts) if x == y =>
                    check0(tm, vty, Val1.Val) :: go(fs, ts)
                  case _ =>
                    err(
                      s"record field mismatch, checking against type: ${ctx.pretty1(ty)}"
                    )
              Tm0.RecordCon(ctx.quote1(ty), go(fs, ts))
            case _ =>
              unify(cv, Val1.Val)
              val (etm, ity, _) = infer0(tm)
              unify(ty, ity)
              etm

        case Tm.Tuple(_, fs) =>
          forceAll1(ty) match
            case Val1.RecordTy0(ts) =>
              def go(fs: List[Tm], ts: Assoc[VTy]): List[Tm0] =
                (fs, ts) match
                  case (Nil, Nil)                 => Nil
                  case (tm :: fs, (y, vty) :: ts) =>
                    check0(tm, vty, Val1.Val) :: go(fs, ts)
                  case _ =>
                    err(
                      s"record field mismatch, checking against type: ${ctx.pretty1(ty)}"
                    )
              Tm0.RecordCon(ctx.quote1(ty), go(fs, ts))
            case _ =>
              err(s"cannot check tuple against type: ${ctx.pretty1(ty)}")

        case tm =>
          infer(tm) match
            case Infer0(etm, vty, vcv) =>
              unify(vcv, cv)
              unify(vty, ty)
              etm
            case Infer1(etm, vty) =>
              val (etm2, vty2) = (etm, vty)
              coeQuote(etm2, vty2, ty, cv)

  private def inferValue(tm: Tm)(using ctx: Ctx): (Tm0, VTy) =
    val (etm, vty, vcv) = infer0(tm)
    forceAll1(vcv) match
      case Val1.Val => ()
      case _        => err(s"expected value but got ${ctx.pretty1(vcv)}")
    (etm, vty)

  private def check1(tm: Tm, ty: VTy)(using ctx: Ctx): Tm1 =
    debug(s"check1 $tm : ${ctx.pretty1(ty)}")
    enter(tm.pos):
      (tm, forceAll1(ty)) match
        case (Tm.Lam(_, x, i, ma, b), Val1.Pi(x2, i2, t1, t2))
            if icitMatch(i, x2, i2) =>
          ma.foreach { sty => unify(ctx.eval1(check1(sty, Val1.UMeta)), t1) }
          val qt1 = ctx.quote1(t1)
          Tm1.Lam(
            x,
            i2,
            qt1,
            check1(b, t2(Var1(ctx.lvl)))(using ctx.bind1(x, qt1, t1))
          )

        case (tm, Val1.Pi(x, Impl, t1, t2)) =>
          val qt1 = ctx.quote1(t1)
          Tm1.Lam(
            x,
            Impl,
            qt1,
            check1(tm, t2(Var1(ctx.lvl)))(using ctx.insert1(x, qt1))
          )

        case (Tm.Pi(_, DontBind, Expl, t1, t2), Val1.UTy(cv)) =>
          unify(cv, Val1.Comp)
          val et1 = check1(t1, VTyVal)
          val (et2, k) = infer1(t2)
          val vfcv = forceAll1(k) match
            case Val1.UTy(vfcv) => vfcv
            case _ => err(s"expected value type but got ${ctx.pretty1(k)}")
          val fcv = ctx.quote1(vfcv)
          Tm1.Fun(et1, fcv, et2)
        case (Tm.Pi(_, x, i, t1, t2), Val1.UMeta) =>
          val et1 = check1(t1, Val1.UMeta)
          val et2 =
            check1(t2, Val1.UMeta)(using ctx.bind1(x, et1, ctx.eval1(et1)))
          Tm1.Pi(x, i, et1, et2)

        case (Tm.Lift(_, tm), Val1.UMeta) =>
          val (etm, k) = infer1(tm)
          val cv = forceAll1(k) match
            case Val1.UTy(vcv) => ctx.quote1(vcv)
            case _             => err("expected value type in lift")
          Tm1.Lift(cv, etm)

        case (Tm.Let1(_, x, mlty, v, b), _) =>
          val (ev, lty, vlty) = mlty match
            case None =>
              val (ev, vlty) = infer1(v)
              val lty = ctx.quote1(vlty)
              (ev, lty, vlty)
            case Some(ty) =>
              val lty = check1(ty, Val1.UMeta)
              val vlty = ctx.eval1(lty)
              val ev = check1(v, vlty)
              (ev, lty, vlty)
          val eb =
            check1(b, ty)(using ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
          Tm1.Let(x, lty, ev, eb)

        case (Tm.Quote(_, tm), Val1.Lift(cv, ty)) => check0(tm, ty, cv).quote
        case (tm, Val1.Lift(cv, ty))              => check0(tm, ty, cv).quote

        case (Tm.Hole(_, x), _) =>
          err(s"checking _${x.getOrElse("")} against ${ctx.pretty1(ty)}")

        case (Tm.Match(pos, None, cs, o), Val1.Pi(x, Expl, pty, rty)) =>
          val (vdty, _) = splitLift(pty)
          val v = Var1(ctx.lvl)
          val (vrty, vrcv) = splitLift(rty(v))
          val qpty = ctx.quote1(pty)
          val nctx = ctx.bind1(DontBind, qpty, pty)
          val (etm, _, _) =
            inferMatch(Tm1.Var(ix0).splice, vdty, cs, o, Some((vrty, vrcv)))(
              using nctx
            )
          Tm1.Lam(x, Expl, qpty, etm.quote)

        case (Tm.Tuple(_, Nil), Val1.UTy(vcv)) =>
          unify(vcv, Val1.Val)
          Tm1.RecordTy0(Nil)
        case (Tm.Tuple(_, Nil), Val1.UMeta) =>
          Tm1.RecordTy1(Nil)

        case (Tm.Tuple(_, fs), Val1.RecordTy1(ts)) =>
          Tm1.RecordCon(checkTuple1(ty, fs, ts))

        case (Tm.RecordTy(_, fs), Val1.UTy(vcv)) =>
          val xs = fs.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record type")
          unify(vcv, Val1.Val)
          def go(fs: Assoc[Tm]): Assoc[Ty] =
            fs match
              case Nil             => Nil
              case (x, ty) :: rest =>
                val ety = check1(ty, VTyVal)
                (x, ety) :: go(rest)
          val efields = go(fs)
          Tm1.RecordTy0(efields)
        case (Tm.RecordTy(_, fs), Val1.UMeta) =>
          val xs = fs.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record type")
          def go(ctx: Ctx, fs: Assoc[Tm]): Assoc[Ty] =
            fs match
              case Nil             => Nil
              case (x, ty) :: rest =>
                val ety = check1(ty, Val1.UMeta)(using ctx)
                val vty = ctx.eval1(ety)
                (x, ety) :: go(ctx.bind1(DoBind(x), ety, vty), rest)
          val efields = go(ctx, fs)
          Tm1.RecordTy1(efields)

        case (Tm.RecordCon1(_, fs0), topty @ Val1.RecordTy1(ts)) =>
          val fs = orderFields(topty, fs0, ts.fields)
          def go(
              env: Env,
              fs: Assoc[Tm],
              ts: Assoc[Ty]
          ): List[Tm1] =
            (fs, ts) match
              case (Nil, Nil)                               => Nil
              case ((x, tm) :: fs, (y, ty) :: ts) if x == y =>
                val vty = eval1(ty)(using env)
                val qty = ctx.quote1(vty)
                val etm = check1(tm, vty)
                val vtm = ctx.eval1(etm)
                val rest = go(Env.E1(env, vtm), fs, ts)
                etm :: rest
              case _ =>
                err(
                  s"record fields mismatch, checking against type: ${ctx.pretty1(topty)}"
                )
          Tm1.RecordCon(go(ts.env, fs, ts.fields))

        case (tm, _) =>
          val (etm, vty) = infer1(tm)
          coe(etm, vty, ty)

  private def orderFields[T](
      topty: VTy,
      fs: Assoc[Tm],
      ts: Assoc[T]
  )(using ctx: Ctx): Assoc[Tm] =
    if fs.size != ts.size then
      err(
        s"record fields mismatch, checking against type: ${ctx.pretty1(topty)}"
      )
    val xs = fs.map(_._1)
    if xs.toSet.size != xs.size then
      err(
        s"duplicate name in record, checking against type: ${ctx.pretty1(topty)}"
      )
    def go(ts: Assoc[T]): Assoc[Tm] =
      ts match
        case Nil          => Nil
        case (x, _) :: tl =>
          fs.find((y, _) => x == y) match
            case None =>
              err(
                s"expected $x in record, checking against type: ${ctx.pretty1(topty)}"
              )
            case Some(hd) => hd :: go(tl)
    go(ts)

  private def checkTuple1(topty: VTy, fs: List[Tm], ts: ClosRec)(using
      ctx: Ctx
  ): List[Tm1] =
    def go(env: Env, fs: List[Tm], ts: Assoc[Ty]): List[Tm1] =
      (fs, ts) match
        case (Nil, Nil)                => Nil
        case (tm :: fs, (x, ty) :: ts) =>
          val vty = eval1(ty)(using env)
          val qty = ctx.quote1(vty)
          val etm = check1(tm, vty)
          val vtm = ctx.eval1(etm)
          val rest = go(Env.E1(env, vtm), fs, ts)
          etm :: rest
        case _ =>
          err(s"failed to check tuple against type: ${ctx.pretty1(topty)}")
    go(ts.env, fs, ts.fields)

  // inference
  private def infer0(tm: Tm)(using ctx: Ctx): (Tm0, VTy, VTy) =
    debug(s"infer0 $tm")
    enter(tm.pos):
      tm match
        case Tm.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_)   => err("implicit lambda in type")
            case ArgInfo.Icit(Impl) => err("implicit lambda in type")
            case ArgInfo.Icit(Expl) =>
              val (ety, vcv) = mty match
                case None     => err("cannot infer unannotated lambda")
                case Some(ty) =>
                  val (ety, k) = infer1(ty)
                  val vcv = forceAll1(k) match
                    case Val1.UTy(vcv) => vcv
                    case _             =>
                      err(
                        s"expected value type in lambda but got ${ctx.pretty1(k)}"
                      )
                  (ety, vcv)
              val vty = ctx.eval1(ety)
              val cv = ctx.quote1(vcv)
              val nctx = ctx.bind0(x, ety, vty, cv, vcv)
              val (eb, vrt, vrcv) = infer0(b)(using nctx)
              (Tm0.Lam(x, ety, eb), Val1.Fun(vty, vrcv, vrt), Val1.Comp)

        case Tm.Tuple(_, Nil) =>
          (Tm0.RecordCon(Tm1.RecordTy0(Nil), Nil), Val1.RecordTy0(Nil), VTyVal)

        case tm =>
          infer(tm) match
            case Infer0(etm, ty, cv) => (etm, ty, cv)
            case Infer1(etm, ty)     =>
              forceAll1(ty) match
                case Val1.Lift(cv, vty) => (etm.splice, vty, cv)
                case _                  =>
                  err(s"expected lifted type but got ${ctx.pretty1(ty)}")

  private def infer1(tm: Tm)(using ctx: Ctx): (Tm1, VTy) =
    debug(s"infer1 $tm")
    enter(tm.pos):
      tm match
        case Tm.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_) => err(s"cannot infer named lambda")
            case ArgInfo.Icit(i)  =>
              val ety = mty match
                case None     => err(s"cannot infer unannotated lambda")
                case Some(ty) => check1(ty, Val1.UMeta)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = infer1(b)(using ctx2)
              val ert = ctx2.quote1(vrt)
              (
                Tm1.Lam(x, i, ety, eb),
                Val1.Pi(x, i, vty, Clos1.Clos(ctx.env, ert))
              )

        case tm =>
          infer(tm) match
            case Infer0(tm, ty, cv) => (tm.quote, Val1.Lift(cv, ty))
            case Infer1(tm, ty)     => (tm, ty)

  private val intType: Val1 = VPrimitive(Name("Primitives"), Name("Int"))

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
      case Right((m, GlobalEntry.Def0(_, _, _, _, _, _, ty, cv))) =>
        Infer0(Tm0.Global(m, x), ty, cv)
      case Right((m, GlobalEntry.Def1(_, _, _, _, v, ty))) =>
        Infer1(Tm1.Global(m, x, v), ty)
      case Right((m, GlobalEntry.Primitive(_, _, _, ty))) =>
        Infer1(Tm1.Primitive(m, x), ty)
      case Right((_, GlobalEntry.Data(_, _, _, _, tm, ty, _))) =>
        Infer1(tm, ty)
      case Right(
            (_, GlobalEntry.DataCon(_, _, _, _, _, _, tm, _, ty))
          ) =>
        Infer1(tm, ty)

  private def infer(tm: Tm)(using ctx: Ctx): Infer =
    debug(s"infer $tm")
    enter(tm.pos):
      tm match
        case Tm.Hole(_, _)  => err("cannot infer hole")
        case Tm.Tuple(_, _) => err("cannot infer tuple")

        case Tm.IntLit(_, v) => Infer0(Tm0.IntLit(v), intType, Val1.Val)

        case Tm.Var(_, Name("meta")) => Infer1(Tm1.UMeta, Val1.UMeta)
        case Tm.App(
              _,
              Tm.Var(_, Name("type")),
              arg,
              ArgInfo.Icit(Expl)
            ) =>
          Infer1(Tm1.UTy(check1(arg, Val1.CV)), Val1.UMeta)
        case Tm.Var(_, Name("type")) =>
          Infer1(
            Tm1.Lam(
              Bind.DoBind(Name("ty")),
              Expl,
              Tm1.CV,
              Tm1.UTy(Tm1.Var(ix0))
            ),
            vfun1(Val1.CV, Val1.UMeta)
          )

        case Tm.Var(_, Name("cv"))   => Infer1(Tm1.CV, Val1.UMeta)
        case Tm.Var(_, Name("val"))  => Infer1(Tm1.Val, Val1.CV)
        case Tm.Var(_, Name("comp")) => Infer1(Tm1.Comp, Val1.CV)

        case Tm.Var(_, x) =>
          ctx.lookup(x) match
            case Some(NameInfo.Name0(x, ty, cv)) =>
              Infer0(Tm0.Var(x.toIx(using ctx.lvl)), ty, cv)
            case Some(NameInfo.Name1(x, ty)) =>
              Infer1(Tm1.Var(x.toIx(using ctx.lvl)), ty)
            case None => inferGlobal(None, x)

        case proj @ Tm.Proj(_, tm, p) =>
          val (hd, tl) = proj.splitProjs
          val global = hd match
            case Tm.Var(pos, x) =>
              if ctx.lookup(x).isEmpty && State.getGlobal(None, x).isLeft then
                def createMod(tl: List[(PosInfo, S.ProjType)]): List[Name] =
                  tl match
                    case Nil                               => Nil
                    case (pos, S.ProjType.Indexed(_)) :: _ =>
                      err("indexed projection for module is invalid")(using
                        ctx.enter(pos)
                      )
                    case (pos, S.ProjType.Named(x)) :: tl => x :: createMod(tl)
                val xs = x :: createMod(tl)
                val m = Name(xs.init.mkString("."))
                Some(inferGlobal(Some(m), xs.last)(using ctx.enter(tl.last._1)))
              else None
            case _ => None
          global match
            case Some(res) => res
            case None      =>
              infer(tm) match
                case Infer0(etm, vty, _) =>
                  forceAll1(vty) match
                    case Val1.RecordTy0(fs) =>
                      val (fty, ep) = p match
                        case S.ProjType.Named(x) =>
                          val fty = fs.find((y, _) => x == y)
                          val ix = fs.indexWhere(((y, _) => x == y))
                          (fty, ProjType(Some(x), ix))
                        case S.ProjType.Indexed(ix) =>
                          val fty = fs.zipWithIndex
                            .find { case (_, ix2) => ix == ix2 }
                            .map(_._1)
                          (fty, ProjType(None, ix))
                      fty match
                        case None =>
                          err(
                            s"no matching projection $p in type: ${ctx.pretty1(vty)}"
                          )
                        case Some((_, fty)) =>
                          Infer0(
                            Tm0.Proj(ctx.quote1(vty), etm, ep),
                            fty,
                            VTyVal
                          )
                    case _ =>
                      err(
                        s"expected record type in projection, but got: ${ctx.pretty1(vty)}"
                      )
                case Infer1(etm, vty) =>
                  forceAll1(vty) match
                    case Val1.RecordTy1(fs) =>
                      def go(
                          vtm: Val1,
                          env: Env,
                          fs: Assoc[Ty],
                          ix: Int
                      ): Option[(VTy, ProjType)] =
                        fs match
                          case Nil             => None
                          case (x, ty) :: rest =>
                            p match
                              case S.ProjType.Named(y) if x == y =>
                                Some(
                                  (eval1(ty)(using env), ProjType(Some(x), ix))
                                )
                              case S.ProjType.Indexed(ix2) if ix == ix2 =>
                                Some((eval1(ty)(using env), ProjType(None, ix)))
                              case _ =>
                                go(
                                  vtm,
                                  Env.E1(env, projIx(vtm, ix, Some(x))),
                                  rest,
                                  ix + 1
                                )
                      val vtm = ctx.eval1(etm)
                      go(vtm, fs.env, fs.fields, 0) match
                        case None =>
                          err(
                            s"no matching projection $p in type: ${ctx.pretty1(vty)}"
                          )
                        case Some((fty, ep)) => Infer1(Tm1.Proj(etm, ep), fty)
                    case _ =>
                      err(
                        s"expected record type in projection, but got: ${ctx.pretty1(vty)}"
                      )

        case Tm.LetRec(_, x, Some(ty), v, b) =>
          val ety = check1(ty, VTyComp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, Tm1.Comp, Val1.Comp)
          val ev = check0(v, vty, Val1.Comp)(using nctx)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(Tm0.LetRec(x, ety, ev, eb), rty, rcv)
        case Tm.LetRec(_, _, _, _, _) => err("let rec requires type annotation")

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
              unify(cv, Val1.Val)
              val (eb, k) = infer1(b)
              val vbcv = forceAll1(k) match
                case Val1.UTy(cv) => cv
                case _            => err("expected value type in pi")
              val bcv = ctx.quote1(vbcv)
              Infer1(Tm1.Fun(ea, bcv, eb), VTyComp)
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
                  unify(cv, Val1.Val)
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

        case Tm.Instr(_, _, _) => err(s"cannot infer JVM instruction")

        case Tm.Match(_, Some(scrut), Nil, None) =>
          err(s"cannot infer empty match")
        case Tm.Match(_, Some(scrut), cs, o) =>
          val (escrut, vdty, _) = infer0(scrut)
          val (etm, vrty, vrcv) = inferMatch(escrut, vdty, cs, o, None)
          Infer0(etm, vrty, vrcv)
        case Tm.Match(_, None, _, _) =>
          err(s"cannot infer match without scrutinee")

        case Tm.If(p, c, a, b) =>
          val (ec, dt) = checkIfCond(p, c)
          val (ea, vrt, vcv) = infer0(a)
          val rt = ctx.quote1(vrt)
          val eb = check0(b, vrt, vcv)
          val cs =
            List((Name("True"), Tm0.Wk0(ea)), (Name("False"), Tm0.Wk0(eb)))
          Infer0(Tm0.Match(rt, dt, ec, cs, None), vrt, vcv)

        case Tm.RecordCon1(_, _) => err("cannot infer meta record")

        case Tm.RecordTy(_, Nil)               => impossible()
        case Tm.RecordTy(_, (x, ty) :: fields) =>
          val xs = x :: fields.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record type")
          val (ety, vk) = infer1(ty)
          forceAll1(vk) match
            case Val1.UTy(vcv) =>
              unify(vcv, Val1.Val)
              def go(fs: Assoc[Tm]): Assoc[Ty] =
                fs match
                  case Nil             => Nil
                  case (x, ty) :: rest =>
                    val ety = check1(ty, VTyVal)
                    (x, ety) :: go(rest)
              val efields = go(fields)
              Infer1(Tm1.RecordTy0((x, ety) :: efields), VTyVal)
            case Val1.UMeta =>
              def go(ctx: Ctx, fs: Assoc[Tm]): Assoc[Ty] =
                fs match
                  case Nil             => Nil
                  case (x, ty) :: rest =>
                    val ety = check1(ty, Val1.UMeta)(using ctx)
                    val vty = ctx.eval1(ety)
                    (x, ety) :: go(ctx.bind1(DoBind(x), ety, vty), rest)
              val vty = ctx.eval1(ety)
              val efields = go(ctx.bind1(DoBind(x), ety, vty), fields)
              Infer1(Tm1.RecordTy1((x, ety) :: efields), Val1.UMeta)
            case _ =>
              err(
                s"expected universe for type in record type but got ${ctx.pretty1(vk)}"
              )

        case Tm.RecordCon0(_, fields) =>
          val xs = fields.map(_._1)
          if xs.toSet.size != xs.size then err(s"duplicate name in record")
          def go(fs: Assoc[Tm]): (List[Tm0], Assoc[VTy]) =
            fs match
              case Nil             => (Nil, Nil)
              case (x, tm) :: rest =>
                val (etm, vty, vcv) = infer0(tm)
                unify(vcv, Val1.Val)
                val (efields, tfields) = go(rest)
                (etm :: efields, (x, vty) :: tfields)
          val (efields, tfields) = go(fields)
          val vty = Val1.RecordTy0(tfields)
          val ty = ctx.quote1(vty)
          Infer0(Tm0.RecordCon(ty, efields), vty, VTyVal)

  private def inferMatch(
      escrut: Tm0,
      vdty: VTy,
      cs: List[(PosInfo, Name, List[Bind], Tm)],
      o: Option[(PosInfo, Tm)],
      erty: Option[(VTy, VTy)]
  )(using ctx: Ctx): (Tm0, VTy, VTy) =
    val (_, m, dx, dps) = forceAll1(vdty) match
      case VTypeCon(k, m, dx, ps) => (k, m, dx, ps.map(_._1))
      case _                      =>
        err(s"expected datatype in match but got ${ctx.pretty1(vdty)}")
    exhaustivenessCheck(
      cs.map((_, x, _, _) => x),
      dataCons(m, dx).toSet,
      o.isDefined
    )
    val dty = ctx.quote1(vdty)
    var rty: Option[(VTy, VTy)] = erty
    given Env = Env(dps)
    val ecs =
      cs.map((p, cx, ps, b) =>
        val (eb, rt) =
          inferMatchCase(
            p,
            m,
            dx,
            cx,
            ps,
            b,
            conParameters(m, cx),
            dty,
            vdty,
            rty
          )
        rty = Some(rt)
        (cx, eb)
      )
    val eo = o.map { (pos, tm) =>
      rty match
        case None =>
          val (eo, rt, rc) = infer0(tm)(using ctx.enter(pos))
          rty = Some((rt, rc))
          eo
        case Some((rt, rc)) => check0(tm, rt, rc)(using ctx.enter(pos))
    }
    val (vrty, vrcv) = rty.get
    val em = Tm0.Match(ctx.quote1(vrty), dty, escrut, ecs, eo)
    (em, vrty, vrcv)

  private def inferMatchCase(
      pos: PosInfo,
      m: Name,
      dx: Name,
      cx: Name,
      ps: List[Bind],
      body: Tm,
      ts: List[VTy],
      dty: Ty,
      vdty: VTy,
      rty: Option[(VTy, VTy)]
  )(using
      ctx: Ctx
  ): (Tm0, (VTy, VTy)) =
    if ps.size != ts.size then
      err(
        s"invalid amount of parameters in match case $cx, expected ${ts.size} but got ${ps.size}"
      )
    val nctx1 =
      ctx
        .enter(pos)
        .bind0(DontBind, dty, vdty, Tm1.Val, Val1.Val)
    val pst = ps.zip(ts)
    val (nctx2, qts) = pst.foldLeft((nctx1, List.empty[(Ty, Ty)])) {
      case ((ctx, qts), (x, vty)) =>
        x match
          case DoBind(_) =>
            val dty = ctx.quote1(vdty)
            val ty = ctx.quote1(vty)
            (ctx.bind0(x, ty, vty, Tm1.Val, Val1.Val), (dty, ty) :: qts)
          case DontBind => (ctx, qts)
    }
    val (eb, rty2) = rty match
      case Some(rt @ (ety, ecv)) => (check0(body, ety, ecv)(using nctx2), rt)
      case None                  =>
        val (eb, t, c) = infer0(body)(using nctx2)
        (eb, (t, c))
    val wrapped = pst.zipWithIndex.zip(qts.reverse).foldRight(eb) {
      case ((((x, vty), i), (dty, qty)), b) =>
        x match
          case DoBind(x) =>
            Tm0.Let(x, qty, Tm0.Select(dty, cx, Tm0.Var(mkIx(i)), i), b)
          case DontBind => b
    }
    (wrapped, rty2)

  private def dataCons(m: Name, dx: Name): List[Name] =
    State.getGlobal(m, dx) match
      case Some(GlobalEntry.Data(_, _, _, cs, _, _, _)) => cs
      case _                                            => impossible()

  private def conParameters(m: Name, cx: Name)(using
      env: Env
  ): List[VTy] =
    State.getGlobal(m, cx) match
      case Some(GlobalEntry.DataCon(_, _, _, ps, _, _, _, _, _)) =>
        ps.map { (_, t) => eval1(t) }
      case _ => impossible()

  private def exhaustivenessCheck(
      cs: List[Name],
      excs: Set[Name],
      hasOtherwise: Boolean
  )(using ctx: Ctx): Unit =
    if cs.toSet.size != cs.size then err(s"duplicate constructor in match")
    else if cs.exists(x => !excs.contains(x)) then
      err(s"invalid constructor in match, expected ${excs.mkString(", ")}")
    else if !hasOtherwise && excs.exists(x => !cs.contains(x)) then
      err(s"missing constructor in match, expected ${excs.mkString(", ")}")

  private def checkIfCond(p: PosInfo, c: Tm)(using
      ctx: Ctx
  ): (Tm0, Tm1) =
    val tbool = check1(Tm.Var(p, Name("Bool")), VTyVal)
    forceAll1(ctx.eval1(tbool)) match
      case Val1.Rigid(
            Head.TypeCon(DataKind.Finite, m, dx),
            Spine.Empty
          ) =>
        State.getGlobal(m, dx) match
          case Some(GlobalEntry.Data(DataKind.Finite, _, _, cs, _, _, _))
              if cs.toSet == Set(Name("True"), Name("False")) =>
            ()
          case _ =>
            err(
              s"expected a Bool type in if-expression but got ${ctx.pretty1(tbool)}"
            )
      case _ =>
        err(
          s"expected a Bool type in if-expression but got ${ctx.pretty1(tbool)}"
        )
    val ec = check0(c, ctx.eval1(tbool), Val1.Val)
    (ec, tbool)

  private def checkAccessibility(ty: VTy)(using ctx: Ctx): Unit =
    debug(s"checkAccessibility ${ctx.pretty1(ty)}")
    def checkGlobal(m: Name, x: Name): Unit =
      if !State.checkAccessibility(m, x) then
        err(s"escaping private definition $m.$x in type: ${ctx.pretty1(ty)}")
    def goSp(sp: Spine)(using lvl: Lvl): Unit =
      sp match
        case Spine.Empty         => ()
        case Spine.App(sp, a, _) => goSp(sp); go1(a)
        case Spine.Proj(sp, _)   => goSp(sp)
    def goHead(hd: Head): Unit =
      hd match
        case Head.Var(_)           => ()
        case Head.Primitive(m, x)  => checkGlobal(m, x)
        case Head.TypeCon(_, m, x) => checkGlobal(m, x)
        case Head.Con(m, x, cx)    => checkGlobal(m, x); checkGlobal(m, cx)
    def goUnfoldHead(hd: UnfoldHead)(using lvl: Lvl): Unit =
      hd match
        case UnfoldHead.Global(m, x, v) => checkGlobal(m, x); go1(v)
    def go1(ty: VTy)(using lvl: Lvl): Unit =
      inline def goClos(c: Clos1): Unit = go1(c(Var1(lvl)))(using lvl + 1)
      def goRec(c: ClosRec): Unit =
        def go(env: Env, lvl: Lvl, fs: Assoc[Ty]): Unit =
          fs match
            case Nil             => ()
            case (_, ty) :: rest =>
              val vty = eval1(ty)(using env)
              go1(vty)
              go(Env.E1(env, Var1(lvl)), lvl + 1, rest)
        go(c.env, lvl, c.fields)
      ty match
        case Val1.UMeta => ()
        case Val1.CV    => ()
        case Val1.Val   => ()
        case Val1.Comp  => ()

        case Val1.UTy(cv)           => go1(cv)
        case Val1.Fun(pty, cv, rty) => go1(pty); go1(cv); go1(rty)
        case Val1.Lift(cv, ty)      => go1(cv); go1(ty)

        case Val1.Quote(tm) => go0(tm)

        case Val1.Rigid(hd, sp)     => goHead(hd); goSp(sp)
        case Val1.Unfold(hd, sp, _) => goUnfoldHead(hd); goSp(sp)

        case Val1.Pi(_, _, ty, b)  => go1(ty); goClos(b)
        case Val1.Lam(_, _, ty, b) => go1(ty); goClos(b)

        case Val1.RecordTy1(fs) => goRec(fs)
        case Val1.RecordTy0(fs) => fs.foreach((_, t) => go1(t))
        case Val1.RecordCon(fs) => fs.foreach(go1)
    def go0(tm: Val0)(using lvl: Lvl): Unit =
      inline def goClos(c: Clos0): Unit = go0(c(Val0.Var(lvl)))(using lvl + 1)
      tm match
        case Val0.Global(m, x)        => checkGlobal(m, x)
        case Val0.Select(dt, _, s, _) =>
          go1(dt); go0(s) // TODO: need to check cx?

        case Val0.Var(_)    => ()
        case Val0.IntLit(_) => ()

        case Val0.Instr(_, ts, rt, args) =>
          ts.foreach(go1); go1(rt); args.foreach(go0)
        case Val0.App(f, a)  => go0(f); go0(a)
        case Val0.Splice(tm) => go1(tm)

        case Val0.Let(_, ty, v, b)        => go1(ty); go0(v); goClos(b)
        case Val0.LetRec(_, ty, v, b)     => go1(ty); goClos(v); goClos(b)
        case Val0.Lam(_, ty, b)           => go1(ty); goClos(b)
        case Val0.Match(rt, dt, s, cs, o) =>
          go1(rt)
          go1(dt)
          go0(s)
          cs.foreach((_, b) => goClos(b))
          o.foreach(go0)
        case Val0.RecordCon(ty, fs) => go1(ty); fs.foreach(go0)
        case Val0.Proj(ty, tm, _)   => go1(ty); go0(tm)
    go1(ty)(using lvl0)

  private def elaborate(defn: Surface.Def): Def = defn match
    case Surface.Def.D0(pos, pub, x, mty, v) =>
      given ctx: Ctx = Ctx.empty.enter(pos)
      if State.currentModuleHasName(x) then err(s"duplicate name $x")
      val (ev, ety, cv, vty, vcv) = mty match
        case None =>
          val (ev, vty, vcv) = infer0(v)
          (ev, ctx.quote1(vty), ctx.quote1(vcv), vty, vcv)
        case Some(ty) =>
          val (ety, k) = infer1(ty)
          val vcv = forceAll1(k) match
            case Val1.UTy(vcv) => vcv
            case _             =>
              err(
                s"value type definition should have value type but got ${ctx.pretty1(k)}"
              )
          val cv = ctx.quote1(vcv)
          val vty = ctx.eval1(ety)
          val ev = check0(v, vty, vcv)
          (ev, ety, cv, vty, vcv)
      if pub then checkAccessibility(vty)
      val vv = ctx.eval0(ev)
      State.addGlobal(GlobalEntry.Def0(pub, x, ev, ety, cv, vv, vty, vcv))
      Def.D0(pub, x, ety, ev)
    case Surface.Def.D1(pos, pub, x, mty, v) =>
      given ctx: Ctx = Ctx.empty.enter(pos)
      if State.currentModuleHasName(x) then err(s"duplicate name $x")
      val (ev, ety, vty) = mty match
        case None =>
          val (ev, vty) = infer1(v)
          (ev, ctx.quote1(vty), vty)
        case Some(ty) =>
          val ety = check1(ty, Val1.UMeta)
          val vty = ctx.eval1(ety)
          val ev = check1(v, vty)
          (ev, ety, vty)
      if pub then checkAccessibility(vty)
      val vv = ctx.eval1(ev)
      State.addGlobal(GlobalEntry.Def1(pub, x, ev, ety, vv, vty))
      Def.D1(pub, x, ety, ev)
    case Surface.Def.Primitive(pos, pub, x, ty) =>
      given ctx: Ctx = Ctx.empty.enter(pos)
      if State.currentModuleHasName(x) then err(s"duplicate name $x")
      val ety = check1(ty, Val1.UMeta)
      val vty = ctx.eval1(ety)
      if pub then checkAccessibility(vty)
      State.addGlobal(GlobalEntry.Primitive(pub, x, ety, vty))
      Def.Primitive(pub, x, ety)
    case Surface.Def.Data(pos, pub, x, k, ps, cs) =>
      given ctx: Ctx = Ctx.empty.enter(pos)
      if State.currentModuleHasName(x) then err(s"duplicate name $x")
      val m = State.currentModule
      val unitCons = cs.filter(c => c.params.isEmpty)
      val unitCon =
        if unitCons.size == 1 then Some(unitCons.head.name) else None
      if k == DataKind.Record && cs.size != 1 then
        err(s"records can only have one constructor")
      val ty = Tm1.TypeCon(k, m, x)
      val vty = ps.foldRight(VTyVal)((_, rt) => vfun1(VTyVal, rt))
      State.addGlobal(
        GlobalEntry.Data(k, pub, x, cs.map(_.name), ty, vty, unitCon)
      )
      val datactx =
        ps.foldLeft(ctx)((ctx, x) => ctx.bind1(DoBind(x), TyVal, VTyVal))
      val ecs = cs.zipWithIndex.map {
        case (Surface.Constructor(pos, pub, cx, cps), ix) =>
          given conctx: Ctx = datactx.enter(pos)
          if k == DataKind.Finite && cps.nonEmpty then
            err(s"a finite datatype cannot have constructor parameters")
          if State.currentModuleHasName(cx) then err(s"duplicate name $cx")
          val tyapp = ps.indices.foldRight(ty)((i, ty) =>
            Tm1.App(ty, Tm1.Var(mkIx(i)), Expl)
          )
          val eps = cps.map((x, t) => (x, check1(t, VTyVal)))
          val cty0 = eps.foldRight(Tm1.Lift(Tm1.Val, tyapp)) {
            case ((x, pty), rty) =>
              Tm1.Pi(x, Expl, Tm1.Lift(Tm1.Val, pty), Tm1.Wk1(rty))
          }
          val cty =
            ps.foldRight(cty0)((x, rty) => Tm1.Pi(DoBind(x), Impl, TyVal, rty))
          val vcty = conctx.eval1(cty)
          State.addGlobal(
            GlobalEntry.DataCon(
              k,
              pub,
              cx,
              eps,
              x,
              ix,
              Tm1.Con(m, x, cx),
              cty,
              vcty
            )
          )
          Constructor(cx, eps)
      }
      Def.Data(k, pub, x, ps, ecs)

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
