import Common.*
import Common.Icit.*
import Common.Bind.*
import Core.{VTy, Ty, Clos1, Locals, Env, Val1 as V, Tm1 as T1, Tm0 as T0}
import Evaluation.*
import Surface as S
import Debug.debug

import scala.annotation.tailrec

object Elaboration:
  final class ElaborateError(pos: PosInfo, msg: String) extends Exception(msg)

  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ElaborateError(ctx.pos, msg)

  private enum Infer:
    case Infer0(tm: T0, ty: VTy, cv: VTy)
    case Infer1(tm: T1, ty: VTy)
  import Infer.*

  // unification
  private def unify(a: VTy, b: VTy)(implicit ctx: Ctx): Unit =
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
        go(ls, xs, T1.Let(x, a, v, ty))
      case (Locals.Bind0(ls, a, cv), x :: xs) => go(ls, xs, T1.MetaPi0(a, ty))
      case (Locals.Bind1(ls, a), x :: xs)     => go(ls, xs, T1.MetaPi1(a, ty))
      case _                                  => impossible()
    go(ctx.locals, ctx.binds, ty)

  private def freshMetaId(ty: VTy)(using ctx: Ctx): MetaId =
    val qa = closeTy(ctx.readback1(ty, UnfoldOption.None))
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
      T1.Quote(T0.App(T0.Wk0(t.splice), T0.Splice(T1.Var(ix0))))
    )

  private def spliceFun(x: Bind, a: VTy, t: T1)(using ctx: Ctx): T1 =
    val y = x match
      case DontBind  => Name("x")
      case DoBind(x) => x
    T1.Quote(
      T0.Lam(
        DoBind(y),
        ctx.readback1(a),
        T0.Splice(T1.App(T1.Wk1(t), T1.Quote(T0.Var(ix0)), Expl))
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
          val a1 = ctx.eval1(freshMeta(V.Type(V.Val)))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2_ = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2_)
          unify(a2, fun)
          go(t, pi, V.Lift(V.Comp, fun))
        case (V.Lift(cv, a), pi @ V.Pi(x, Expl, t1, t2)) =>
          unify(cv, V.Comp)
          val a1 = ctx.eval1(freshMeta(V.Type(V.Val)))
          val a2cv = freshCV()
          val va2cv = ctx.eval1(a2cv)
          val a2 = ctx.eval1(freshMeta(V.Type(va2cv)))
          val fun = V.Fun(a1, va2cv, a2)
          unify(a, fun)
          go(t, V.Lift(V.Comp, fun), pi)

        case (_, _) => unify(a1, a2); None

    go(t, a1, a2).getOrElse(t)

  // helpers
  private def tyAnnot(ma: Option[S.Tm], ty: VTy)(using ctx: Ctx): Ty =
    ma.fold(freshMeta(ty))(a => check1(a, ty))

  private def ensureFun(a: VTy, acv: VTy)(using ctx: Ctx): (VTy, VTy, VTy) =
    forceAll1(a) match
      case V.Fun(a, bcv, b) => (a, bcv, b)
      case _ =>
        unify(acv, V.Comp)
        val a2 = ctx.eval1(freshMeta(V.Type(V.Val)))
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

  private def apply1(a: VTy, i: Icit, t: T1, u: S.Tm)(using ctx: Ctx): Infer =
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

  // checking
  private def check0(tm: S.Tm, ty: VTy, cv: VTy)(using ctx: Ctx): T0 = ???

  private def check1(tm: S.Tm, ty: VTy)(using ctx: Ctx): T1 = ???

  // inference
  private def infer0(tm: S.Tm)(using ctx: Ctx): (T0, VTy, VTy) = ???

  private def infer1(tm: S.Tm)(using ctx: Ctx): (T1, VTy) = ???

  private def infer(tm: S.Tm)(using ctx: Ctx): Infer = ???

  // elaboration
  private def elaborate(d: S.Def): Unit = ???

  def elaborate(d: S.Defs): Unit = d.toList.foreach(elaborate)
