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
  Tm1 as T1,
  Tm0 as T0,
  Cases
}
import Evaluation.*
import Surface.Tm as S
import Surface.ArgInfo
import Ctx.NameInfo
import State.GlobalEntry
import Debug.debug

import scala.annotation.tailrec

object Elaboration:
  final class ElaborateError(val pos: PosInfo, val module: Name, msg: String)
      extends Exception(msg)

  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborateError(ctx.pos, State.currentModule, msg)

  private enum Infer:
    case Infer0(tm: T0, ty: VTy, cv: VTy)
    case Infer1(tm: T1, ty: VTy)
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
    def go(ls: Locals, xs: Seq[Bind], ty: Ty): Ty = (ls, xs) match
      case (Locals.Empty, Nil) => ty
      case (Locals.Def(ls, a, v), Bind.DoBind(x) :: xs) =>
        go(ls, xs, T1.Let(x, a, v, ty))
      case (Locals.Bind0(ls, a, cv), x :: xs) => go(ls, xs, T1.MetaPi0(a, ty))
      case (Locals.Bind1(ls, a), x :: xs)     => go(ls, xs, T1.MetaPi1(a, ty))
      case _                                  => impossible()
    go(ctx.locals, ctx.binds, ty)

  private def freshMetaId(ty: VTy)(using ctx: Ctx): MetaId =
    val qa = closeTy(ctx.readback1(ty, UnfoldOption.None))
    debug(s"freshMetaId : ${ctx.pretty1(qa)}")
    val vqa = eval1(qa)(using Env.Empty)
    val m = State.newMeta(vqa)
    debug(s"freshMetaId ?$m : ${ctx.pretty1(ty)}")
    m

  private inline def freshMeta(ty: VTy)(using ctx: Ctx): T1 =
    T1.AppPruning(freshMetaId(ty), ctx.pruning)

  private inline def freshCV()(using ctx: Ctx): T1 = freshMeta(V.CV)

  // meta insertion
  private enum InsertMode:
    case All
    case Until(name: Name)
  import InsertMode.*

  private def insertPi(inp: (T1, VTy), mode: InsertMode = All)(using
      ctx: Ctx
  ): (T1, VTy) =
    @tailrec
    def go(tm: T1, ty: VTy): (T1, VTy) =
      forceAll1(ty) match
        case V.Pi(y, Impl, a, b) =>
          mode match
            case Until(x) if DoBind(x) == y => (tm, ty)
            case _ =>
              val m = freshMeta(a)
              go(T1.App(tm, m, Impl), b(ctx.eval1(m)))
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

  private def insert(inp: (T1, VTy))(using ctx: Ctx): (T1, VTy) =
    inp._1 match
      case T1.Lam(_, Impl, _, _) => inp
      case _                     => insertPi(inp)

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
      Expl,
      V.Lift(V.Val, a),
      Clos1.Clos(ctx.env, T1.Lift(qbcv, qb))
    )

  private def quoteFun(x: Bind, a: VTy, t: T1)(using ctx: Ctx): T1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    T1.Lam(
      DoBind(y),
      Expl,
      T1.Lift(T1.Val, ctx.readback1(a)),
      T1.Quote(T0.App(T0.Wk1(t.splice), T0.Splice(T1.Var(ix0))))
    )

  private def spliceFun(x: Bind, a: VTy, t: T1)(using ctx: Ctx): T1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    T1.Quote(
      T0.Lam(
        DoBind(y),
        ctx.readback1(a),
        T0.Splice(T1.App(T1.Wk0(t), T1.Quote(T0.Var(ix0)), Expl))
      )
    )

  // coercion
  private def coe(t: T1, a1: VTy, a2: VTy)(using ctx: Ctx): T1 =
    def go(t: T1, a1: VTy, a2: VTy)(using ctx: Ctx): Option[T1] =
      debug(
        s"coe ${ctx.pretty1(t)} from ${ctx.pretty1(a1)} to ${ctx.pretty1(a2)}"
      )
      (forceAll1(a1), forceAll1(a2)) match
        case (V.Flex(x, sp), _) => unify(a1, a2); None
        case (_, V.Flex(x, sp)) => unify(a1, a2); None

        case (V.Type(cv), V.Meta) => Some(T1.Lift(ctx.readback1(cv), t))

        case (V.Pi(x, i, a1, b1), V.Pi(x2, i2, a2, b2)) =>
          if i != i2 then err(s"icit mismatch in coercion")(using ctx)
          given ctx2: Ctx = ctx.bind1(x, ctx.readback1(a2), a2)
          go(T1.Var(ix0), a2, a1) match
            case None =>
              go(
                T1.App(T1.Wk1(t), T1.Var(ix0), i),
                b1(ctx2.eval1(T1.Var(ix0))),
                b2(V.Var(ctx.lvl))
              ).map(b => T1.Lam(x, i, ctx.readback1(a2), b))
            case Some(coev0) =>
              Some(
                T1.Lam(
                  x,
                  i,
                  ctx.readback1(a2),
                  coe(
                    T1.App(T1.Wk1(t), coev0, i),
                    b1(ctx2.eval1(coev0)),
                    b2(V.Var(ctx.lvl))
                  )
                )
              )

        case (V.Lift(_, V.Fun(a, cv, b)), V.Pi(x, _, _, _)) =>
          Some(coe(quoteFun(x, a, t), liftFun(a, b, cv), a2))
        case (V.Lift(_, V.Fun(a, cv, b)), _) =>
          Some(coe(quoteFun(DontBind, a, t), liftFun(a, b, cv), a2))
        case (V.Pi(x, _, _, _), V.Lift(_, V.Fun(t1, cv, t2))) =>
          Some(spliceFun(x, t1, coe(t, a1, liftFun(t1, t2, cv))))
        case (_, V.Lift(_, V.Fun(t1, cv, t2))) =>
          Some(spliceFun(DontBind, t1, coe(t, a1, liftFun(t1, t2, cv))))

        case (pi @ V.Pi(x, Expl, a, b), V.Lift(cv, a2)) =>
          unify(cv, V.Comp)
          val a1 = ctx.eval1(freshMeta(V.TypeV))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2_ = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2_)
          unify(a2, fun)
          go(t, pi, V.Lift(V.Comp, fun))
        case (V.Lift(cv, a), pi @ V.Pi(x, Expl, t1, t2)) =>
          unify(cv, V.Comp)
          val a1 = ctx.eval1(freshMeta(V.TypeV))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2 = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2)
          unify(a, fun)
          go(t, V.Lift(V.Comp, fun), pi)

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
  ): (Seq[VTy], VTy, VTy) =
    if n == 0 then (Nil, acv, a)
    else
      val (t1, cv, t2) = ensureFun(a, acv)
      val (ps, rcv, rt) = ensureFunN(n - 1, t2, cv)
      (t1 +: ps, rcv, rt)

  private def ensureLift(t: VTy)(using ctx: Ctx): (VTy, VTy) =
    forceAll1(t) match
      case V.Lift(cv, ty) => (cv, ty)
      case _ =>
        val cv = ctx.eval1(freshCV())
        val ty = ctx.eval1(freshMeta(V.Type(cv)))
        unify(t, V.Lift(cv, ty))
        (cv, ty)

  private def apply1(a: VTy, i: Icit, t: T1, u: S)(using ctx: Ctx): Infer =
    debug(s"apply1 ${ctx.pretty1(a)} $i @ $u")
    forceAll1(a) match
      case V.Pi(x, i2, a, b) =>
        if i != i2 then err(s"icit mismatch in apply1")
        val u2 = check1(u, a)
        Infer1(T1.App(t, u2, i), b(ctx.eval1(u2)))
      case V.Lift(_, V.Fun(a, bcv, b)) =>
        if i != Expl then err(s"icit mismatch in apply1")
        val u2 = check0(u, a, V.Val)
        Infer0(T0.App(t.splice, u2), b, bcv)
      case _ =>
        val a2 = freshMeta(V.Meta)
        val va2 = ctx.eval1(a2)
        val x = DoBind(Name("x"))
        val b2 =
          Clos1.Clos(ctx.env, freshMeta(V.Meta)(using ctx.bind1(x, a2, va2)))
        val t2 = coe(t, a, V.Pi(x, i, va2, b2))
        val u2 = check1(u, ctx.eval1(a2))
        Infer1(T1.App(t2, u2, i), b2(ctx.eval1(u2)))

  private def coeQuote(t: T1, a1: VTy, a2: VTy, cv: VTy)(using ctx: Ctx): T0 =
    coe(t, a1, V.Lift(cv, a2)).splice

  private def icitMatch(i: ArgInfo, x: Bind, i2: Icit): Boolean = i match
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

  // checking
  private def check0(tm: S, ty: VTy, cv: VTy)(using ctx: Ctx): T0 =
    debug(s"check0 $tm : ${ctx.pretty1(ty)} : ${ctx.pretty1(cv)}")
    enter(tm.pos):
      tm match
        case S.Lam(_, x, i, ma, b) =>
          if i != ArgInfo.Icit(Expl) then err(s"implicit lambda in Ty")
          val (t1, fcv, t2) = ensureFun(ty, cv)
          ma.foreach { sty => unify(ctx.eval1(check1(sty, V.TypeV)), t1) }
          val qt1 = ctx.readback1(t1)
          T0.Lam(
            x,
            qt1,
            check0(b, t2, fcv)(using ctx.bind0(x, qt1, t1, T1.Val, V.Val))
          )

        case S.LetRec(_, x, ma, v, b) =>
          val (ety, cv2, vcv2) = (tyAnnot(ma, V.TypeC), T1.Comp, V.Comp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using nctx)
          val eb = check0(b, ty, cv)(using nctx)
          T0.LetRec(x, ety, ev, eb)

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
          T0.Let(x, ety, ev, eb)

        case S.If(_, c, t, f) =>
          val ec = check0(c, V.Bool, V.Val)
          val et = check0(t, ty, cv)
          val ef = check0(f, ty, cv)
          T0.If(ctx.readback1(ty), ec, et, ef)

        case S.Hole(_, _) => freshMeta(V.Lift(cv, ty)).splice

        case S.Splice(_, t) => check1(t, V.Lift(cv, ty)).splice

        case S.Match(_, Some(s), cs) => checkMatch(s, cs, ty, cv)

        case S.Match(_, None, cs) =>
          val (t1, fcv, t2) = ensureFun(ty, cv)
          val bx = DoBind(Name("x"))
          val rt1 = ctx.readback1(t1)
          val nctx =
            ctx.bind0(DontBind, rt1, t1, T1.Val, V.Val)
          val ecs = checkCases(t1, cs, t2, fcv)(using nctx)
          val nrt1 = nctx.readback1(t1)
          val rt2 = nctx.readback1(t2)
          T0.Lam(bx, rt1, T0.Case(rt2, nrt1, T0.Var(ix0), ecs))

        case tm =>
          infer(tm) match
            case Infer0(etm, vty, vcv) =>
              unify(vcv, cv)
              unify(vty, ty)
              etm
            case Infer1(etm, vty) =>
              val (etm2, vty2) = insert((etm, vty))
              coeQuote(etm2, vty2, ty, cv)

  private def check1(tm: S, ty: VTy)(using ctx: Ctx): T1 =
    debug(s"check1 $tm : ${ctx.pretty1(ty)}")
    enter(tm.pos):
      (tm, forceAll1(ty)) match
        case (S.Lam(_, x, i, ma, b), V.Pi(x2, i2, t1, t2))
            if icitMatch(i, x2, i2) =>
          ma.foreach { sty => unify(ctx.eval1(check1(sty, V.Meta)), t1) }
          val qt1 = ctx.readback1(t1)
          T1.Lam(
            x,
            i2,
            qt1,
            check1(b, t2(V.Var(ctx.lvl)))(using ctx.bind1(x, qt1, t1))
          )

        case (S.Var(_, x), V.Pi(_, Impl, _, _)) if varHasUnknownType1(x) =>
          val Some(NameInfo.Name1(lvl, ty2)) = ctx.lookup(x): @unchecked
          unify(ty2, ty)
          T1.Var(lvl.toIx(using ctx.lvl))

        case (tm, V.Pi(x, Impl, t1, t2)) =>
          val qt1 = ctx.readback1(t1)
          T1.Lam(
            x,
            Impl,
            qt1,
            check1(tm, t2(V.Var(ctx.lvl)))(using ctx.insert1(x, qt1))
          )

        case (S.Pi(_, DontBind, Expl, t1, t2), V.Type(cv)) =>
          unify(cv, V.Comp)
          val et1 = check1(t1, V.TypeV)
          val fcv = freshCV()
          val vfcv = ctx.eval1(fcv)
          val et2 = check1(t2, V.Type(vfcv))
          T1.Fun(et1, fcv, et2)
        case (S.Pi(_, x, i, t1, t2), V.Meta) =>
          val et1 = check1(t1, V.Meta)
          val et2 = check1(t2, V.Meta)(using ctx.bind1(x, et1, ctx.eval1(et1)))
          T1.Pi(x, i, et1, et2)

        case (S.Lift(_, tm), V.Meta) =>
          val cv = freshCV()
          T1.Lift(cv, check1(tm, V.Type(ctx.eval1(cv))))

        case (S.Let1(_, x, mlty, v, b), _) =>
          val lty = tyAnnot(mlty, V.Meta)
          val vlty = ctx.eval1(lty)
          val ev = check1(v, vlty)
          val eb =
            check1(b, ty)(using ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
          T1.Let(x, lty, ev, eb)

        case (S.Quote(_, tm), V.Lift(cv, ty)) => check0(tm, ty, cv).quote
        case (tm, V.Lift(cv, ty))             => check0(tm, ty, cv).quote

        case (S.Hole(_, _), _) => freshMeta(ty)

        case (S.Match(_, None, cs), V.Pi(x, Expl, a, b)) =>
          val vdty = ctx.eval1(freshMeta(V.TypeV))
          unify(a, V.Lift(V.Val, vdty))
          val ra = ctx.readback1(a)
          val nctx = ctx.bind1(DontBind, ra, a)
          val vrcv = nctx.eval1(freshCV()(using nctx))
          val vrty = nctx.eval1(freshMeta(V.Type(vrcv))(using nctx))
          unify(b(V.Var(ctx.lvl)), V.Lift(vrcv, vrty))(using nctx)
          val ndty = nctx.readback1(vdty)
          val nvrty = nctx.readback1(vrty)
          val ecs = checkCases(vdty, cs, vrty, vrcv)(using nctx)
          val casetm = T0.Case(nvrty, ndty, T1.Var(ix0).splice, ecs)
          val y = x.orElse(DoBind(Name("x")))
          T1.Lam(y, Expl, ra, casetm.quote)

        case (tm, _) =>
          val (etm, vty) = insert(infer1(tm))
          coe(etm, vty, ty)

  // inference
  private def infer0(tm: S)(using ctx: Ctx): (T0, VTy, VTy) =
    debug(s"infer0 $tm")
    enter(tm.pos):
      tm match
        case S.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_)   => err(s"implicit lambda in type")
            case ArgInfo.Icit(Impl) => err(s"implicit lambda in type")
            case ArgInfo.Icit(Expl) =>
              val acv = T1.Val
              val avcv = ctx.eval1(acv)
              val ety = tyAnnot(mty, V.Type(avcv))
              val cv = freshCV()
              val vcv = ctx.eval1(cv)
              val rt = freshMeta(V.Type(vcv))
              val vrt = ctx.eval1(rt)
              val vty = ctx.eval1(ety)
              val eb =
                check0(b, vrt, vcv)(using ctx.bind0(x, ety, vty, acv, avcv))
              (T0.Lam(x, ety, eb), V.Fun(vty, vcv, vrt), V.Comp)

        case S.Hole(_, _) => err("cannot infer hole")

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

  private def infer1(tm: S)(using ctx: Ctx): (T1, VTy) =
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
              (T1.Lam(x, i, ety, eb), V.Pi(x, i, vty, Clos1.Clos(ctx.env, ert)))

        case S.Hole(_, _) =>
          val ty = ctx.eval1(freshMeta(V.Meta))
          val tm = freshMeta(ty)
          (tm, ty)

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
      case Right((m, GlobalEntry.Def0(_, _, _, _, _, ty, cv))) =>
        Infer0(T0.Global(m, x), ty, cv)
      case Right((m, GlobalEntry.Def1(_, _, _, v, ty))) =>
        Infer1(T1.Global(m, x, v), ty)
      case Right((_, GlobalEntry.Data(_, _, _, tm, ty, _))) =>
        Infer1(tm, ty)
      case Right((_, GlobalEntry.Con(_, _, _, _, _, tm, _, ty))) =>
        Infer1(tm, ty)

  private def infer(tm: S)(using ctx: Ctx): Infer =
    debug(s"infer $tm")
    enter(tm.pos):
      tm match
        case S.Prim(_, p)   => Infer1(T1.Prim(p), inferPrimType(p))
        case S.IntLit(_, v) => Infer0(T0.IntLit(v), V.Int, V.Val)

        case S.Var(_, x) =>
          ctx.lookup(x) match
            case Some(NameInfo.Name0(x, ty, cv)) =>
              Infer0(T0.Var(x.toIx(using ctx.lvl)), ty, cv)
            case Some(NameInfo.Name1(x, ty)) =>
              Infer1(T1.Var(x.toIx(using ctx.lvl)), ty)
            case None => inferGlobal(None, x)

        case proj @ S.Proj(_, _, _) =>
          val (hd, tl) = proj.splitProjs
          hd match
            case S.Var(pos, x) =>
              if ctx.lookup(x).isEmpty && State.getGlobal(None, x).isLeft then
                def createMod(
                    tl: Seq[(PosInfo, Surface.ProjType)]
                ): Seq[Name] =
                  tl match
                    case Nil => Nil
                    case (pos, Surface.ProjType.Indexed(_)) :: _ =>
                      err("indexed projection for module is invalid")(using
                        ctx.enter(pos)
                      )
                    case (pos, Surface.ProjType.Named(x)) :: tl =>
                      x +: createMod(tl)
                val xs = x +: createMod(tl)
                val m = Name(xs.init.mkString("."))
                inferGlobal(Some(m), xs.last)(using ctx.enter(tl.last._1))
              else err(s"invalid projection")
            case _ => err(s"invalid projection")

        case S.LetRec(_, x, mty, v, b) =>
          val (ety, cv2, vcv2) = (tyAnnot(mty, V.TypeC), T1.Comp, V.Comp)
          val vty = ctx.eval1(ety)
          val nctx = ctx.bind0(DoBind(x), ety, vty, cv2, vcv2)
          val ev = check0(v, vty, vcv2)(using nctx)
          val (eb, rty, rcv) = infer0(b)(using nctx)
          Infer0(T0.LetRec(x, ety, ev, eb), rty, rcv)

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
          Infer0(T0.Let(x, ety, ev, eb), rty, rcv)

        case S.Let1(_, x, mty, v, b) =>
          val lty = tyAnnot(mty, V.Meta)
          val vlty = ctx.eval1(lty)
          val ev = check1(v, vlty)
          val (eb, rty) =
            infer1(b)(using ctx.define(x, lty, vlty, ev, ctx.eval1(ev)))
          Infer1(T1.Let(x, lty, ev, eb), rty)

        case S.Pi(_, DontBind, Expl, a, b) =>
          val (ea, vta) = insert(infer1(a))
          forceAll1(vta) match
            case V.Type(cv) =>
              unify(cv, V.Val)
              val bcv = freshCV()
              val vbcv = ctx.eval1(bcv)
              val eb = check1(b, V.Type(vbcv))
              Infer1(T1.Fun(ea, bcv, eb), V.TypeC)
            case V.Meta =>
              val eb =
                check1(b, V.Meta)(using ctx.bind1(DontBind, ea, ctx.eval1(ea)))
              Infer1(T1.Pi(DontBind, Expl, ea, eb), V.Meta)
            case _ => err("expected type for Pi parameter")
        case S.Pi(_, x, i, a, b) =>
          val ea = check1(a, V.Meta)
          val eb = check1(b, V.Meta)(using ctx.bind1(x, ea, ctx.eval1(ea)))
          Infer1(T1.Pi(x, i, ea, eb), V.Meta)

        case S.Lam(_, x, i, mty, b) =>
          i match
            case ArgInfo.Named(_)   => err("cannot infer")
            case ArgInfo.Icit(Expl) => err("cannot infer")
            case ArgInfo.Icit(Impl) =>
              val ety = tyAnnot(mty, V.Meta)
              val vty = ctx.eval1(ety)
              val ctx2 = ctx.bind1(x, ety, vty)
              val (eb, vrt) = insert(infer1(b)(using ctx2))(using ctx2)
              val qrt = ctx2.readback1(vrt)
              Infer1(
                T1.Lam(x, Impl, ety, eb),
                V.Pi(x, Impl, vty, Clos1.Clos(ctx.env, qrt))
              )

        case S.App(_, f, a, i) =>
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
                  Infer0(T0.App(ef, ea), t2, rcv)
                case Infer1(ef, fty) => apply1(fty, Expl, ef, a)

        case S.Lift(_, ty) =>
          val cv = freshCV()
          val vcv = ctx.eval1(cv)
          Infer1(T1.Lift(cv, check1(ty, V.Type(vcv))), V.Meta)
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
          Infer0(T0.If(ctx.readback1(ty), ec, et, ef), ty, cv)

        case S.Hole(_, _) => err("cannot infer hole")

        case S.Match(_, None, _) => err("cannot infer lambda match")
        case S.Match(_, Some(s), cs) =>
          val cv = freshCV()
          val excv = ctx.eval1(cv)
          val exty = ctx.eval1(freshMeta(V.Type(excv)))
          val etm = checkMatch(s, cs, exty, excv)
          Infer0(etm, exty, excv)

  private def checkMatch(
      scrut: S,
      cs: Seq[(PosInfo, Bind, Seq[Bind], S)],
      exty: VTy,
      excv: VTy
  )(using
      ctx: Ctx
  ): T0 =
    debug(
      s"checkMatch $scrut { ${cs.map((_, cx, ps, b) => s"$cx ${ps.mkString(" ")} => $b").mkString(" | ")} } : ${ctx.pretty1(exty)}"
    )
    val (escrut, vscrutty, vscrutcv) = infer0(scrut)
    unify(vscrutcv, V.Val)
    val ecs = checkCases(vscrutty, cs, exty, excv)
    T0.Case(ctx.readback1(exty), ctx.readback1(vscrutty), escrut, ecs)

  private def checkCases(
      vscrutty: VTy,
      cs: Seq[(PosInfo, Bind, Seq[Bind], S)],
      exty: VTy,
      excv: VTy
  )(using
      ctx: Ctx
  ): Cases =
    debug(
      s"checkCases ${ctx.pretty1(vscrutty)} { ${cs.map((_, cx, ps, b) => s"$cx ${ps.mkString(" ")} => $b").mkString(" | ")} } : ${ctx.pretty1(exty)}"
    )
    val (m, dx, ps) = forceAll1(vscrutty) match
      case V.TypeCon(m, dx, ps) => (m, dx, ps.map((t, _) => t))
      case _ =>
        err(s"expected datatype in match but got ${ctx.pretty1(vscrutty)}")
    val (dps, cons) = State.getGlobal(m, dx) match
      case Some(GlobalEntry.Data(_, dps, cs, _, _, _)) => (dps, cs.toSet)
      case _                                           => impossible()
    val psenv = Env(ps)
    inline def conTypes(m: Name, cx: Name): Seq[VTy] =
      State.getGlobal(m, cx) match
        case Some(GlobalEntry.Con(_, _, params, _, _, _, _, _)) =>
          params.map((_, ty) => eval1(ty)(using psenv))
        case _ => impossible()
    inline def goBranch(m: Name, cx: Name, ps: Seq[Bind], b: S)(using
        ctx: Ctx
    ): (Seq[(Bind, Ty)], T0) =
      val (innerctx, nps) =
        ps.zip(conTypes(m, cx)).foldLeft[(Ctx, Seq[(Bind, Ty)])]((ctx, Nil)) {
          case ((innerctx, nps), (x, ty)) =>
            val rty = ctx.readback1(ty)
            (
              innerctx.bind0(x, rty, ty, T1.Val, V.Val),
              nps :+ (x, rty)
            )
        }
      val nb = check0(b, exty, excv)(using innerctx)
      (nps, nb)
    def goCases(
        cs: Seq[(PosInfo, Bind, Seq[Bind], S)],
        cons: Set[Name],
        seen: Set[Name]
    ): Cases =
      cs match
        case Nil =>
          if cons.nonEmpty then
            err(
              s"match is not exhaustive, constructors left: ${cons.mkString(", ")}"
            )
          Cases.Empty
        case (pos, cx, ps, b) :: r =>
          enter(pos):
            cx match
              case DontBind =>
                if r.nonEmpty then err(s"otherwise branch must be the last one")
                if ps.nonEmpty then
                  err(s"otherwise branch cannot have parameters")
                Cases.Otherwise(check0(b, exty, excv))
              case DoBind(cx) =>
                if !cons.contains(cx) then
                  err(s"constructor not part of datatype in match: $cx")
                if seen.contains(cx) then
                  err(s"duplicate constructor in match: $cx")
                val (eps, eb) = goBranch(m, cx, ps, b)
                val er = goCases(r, cons - cx, seen + cx)
                Cases.Ext(cx, eps, eb, er)
    goCases(cs, cons, Set.empty)

  // elaboration
  // TODO: use frozen metas instead of this check
  private def checkUnsolvedMetas()(using ctx: Ctx): Unit =
    val ums = State.unsolvedMetas()
    if ums.nonEmpty then
      val str =
        ums.map((id, ty) => s"?$id : ${ctx.pretty1(ty)}").mkString("\n")
      err(s"there are unsolved metas:\n$str")

  private def elaborate(d: Surface.Def): Unit =
    debug(s"elaborate $d")
    d match
      case Surface.Def.Def0(pos, x, mty, v) =>
        given ctx: Ctx = Ctx.empty(pos)
        if State.currentModuleHasName(x) then err(s"duplicate definition $x")
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
        checkUnsolvedMetas()
        State.addGlobal(
          GlobalEntry.Def0(x, ev, ty, cv, ctx.eval0(ev), vty, vcv)
        )
      case Surface.Def.Def1(pos, x, mty, v) =>
        given ctx: Ctx = Ctx.empty(pos)
        if State.currentModuleHasName(x) then err(s"duplicate definition $x")
        val (ev, ty, vv, vty) = mty match
          case None =>
            val (ev, vty) = infer1(v)
            (ev, ctx.readback1(vty), ctx.eval1(ev), vty)
          case Some(sty) =>
            val ety = check1(sty, V.Meta)
            val vty = ctx.eval1(ety)
            val ev = check1(v, vty)
            (ev, ety, ctx.eval1(ev), vty)
        checkUnsolvedMetas()
        State.addGlobal(GlobalEntry.Def1(x, ev, ty, vv, vty))
      case Surface.Def.Data(pos, x, ps, cs) =>
        given ctx: Ctx = Ctx.empty(pos)
        if State.currentModuleHasName(x) then err(s"duplicate definition $x")
        val unitCons = cs.filter(c => c.params.isEmpty)
        val unitCon =
          if unitCons.size == 1 then Some(unitCons.head.name) else None
        val ty = T1.TypeCon(State.currentModule, x)
        val vty = ps.foldRight(V.TypeV)((_, rt) => V.fun1(V.TypeV, rt))
        State.addGlobal(
          GlobalEntry.Data(x, ps, cs.map(_.name), ty, vty, unitCon)
        )
        val datactx =
          ps.foldLeft(ctx)((ctx, x) => ctx.bind1(DoBind(x), T1.TypeV, V.TypeV))
        cs.zipWithIndex.foreach {
          case (Surface.Constructor(pos, cx, cps), ix) =>
            given conctx: Ctx = datactx.enter(pos)
            if State.currentModuleHasName(cx) then err(s"duplicate name $cx")
            val tyapp = ps.indices.foldRight(ty)((i, ty) =>
              T1.App(ty, T1.Var(mkIx(i)), Expl)
            )
            val eps = cps.map((x, t) => (x, check1(t, V.TypeV)))
            val cty0 = eps.foldRight(T1.Lift(T1.Val, tyapp)) {
              case ((x, pty), rty) =>
                T1.Pi(x, Expl, T1.Lift(T1.Val, pty), T1.Wk1(rty))
            }
            val cty = ps.foldRight(cty0)((x, rty) =>
              T1.Pi(DoBind(x), Impl, T1.TypeV, rty)
            )
            val vcty = conctx.eval1(cty)
            State.addGlobal(
              GlobalEntry.Con(
                cx,
                ps,
                eps,
                x,
                ix,
                T1.Con(State.currentModule, x, cx),
                cty,
                vcty
              )
            )
        }

  private def elaborate(mod: Surface.Module): Unit =
    State.enterModule(mod.name)
    mod.moduleAliases.foreach((m, r) => State.addModuleRenaming(m, r))
    mod.imports.foreach { case (x, (p1, p2, m, r)) =>
      val ctx = Ctx.empty(mod.pos)
      if (!State.moduleExists(m))
        err(s"undefined module $m in imports")(using ctx.enter(p1))
      else if (!State.moduleHasName(m, x))
        err(s"undefined name $m.$x in imports")(using ctx.enter(p2))
      else State.addImport(m, x, r.getOrElse(x))
    }
    mod.defs.toSeq.foreach(elaborate)

  def elaborate(mod: Seq[Surface.Module]): Unit =
    mod.map(elaborate)
