package core

import common.Common.*
import Core.*
import Evaluation.*
import Evaluation.QuoteOption.UnfoldNone

object Unification:
  class UnificationError(val msg: String) extends RuntimeException(msg):
    override def toString: String = s"unification error: $msg"
  private inline def err(msg: String): Nothing =
    throw new UnificationError(msg)

  private def unify0(a: Val0, b: Val0)(using lvl: Lvl): Unit =
    inline def goClos(a: Clos0, b: Clos0): Unit =
      val v = Val0.Var(lvl)
      unify0(a(v), b(v))(using lvl + 1)
    (a, b) match
      case (Val0.Var(x), Val0.Var(y)) if x == y                           => ()
      case (Val0.IntLit(x), Val0.IntLit(y)) if x == y                     => ()
      case (Val0.Global(m1, x), Val0.Global(m2, y)) if m1 == m2 && x == y => ()
      case (
            Val0.Select(dt1, cx1, s1, i1),
            Val0.Select(dt2, cx2, s2, i2)
          ) if cx1 == cx2 && i1 == i2 =>
        unify1(dt1, dt2)
        unify0(s1, s2)
      case (Val0.Let(_, ty1, v1, b1), Val0.Let(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); unify0(v1, v2); goClos(b1, b2)
      case (Val0.LetRec(_, ty1, v1, b1), Val0.LetRec(_, ty2, v2, b2)) =>
        unify1(ty1, ty2); goClos(v1, v2); goClos(b1, b2)
      case (Val0.Splice(v1), Val0.Splice(v2)) => unify1(v1, v2)
      case (Val0.Instr(op1, ts1, rt1, args1), Val0.Instr(op2, ts2, rt2, args2))
          if op1 == op2 && args1.size == args2.size =>
        ts1.zip(ts2).foreach((a, b) => unify1(a, b))
        unify1(rt1, rt2)
        args1.zip(args2).foreach(unify0)
      case (Val0.Lam(_, _, b1), Val0.Lam(_, _, b2)) => goClos(b1, b2)
      case (Val0.App(f1, a1), Val0.App(f2, a2))     =>
        unify0(f1, f2); unify0(a1, a2)
      case (
            Val0.Match(rt1, dt1, s1, cs1, o1),
            Val0.Match(rt2, dt2, s2, cs2, o2)
          ) if cs1.size == cs2.size && o1.isDefined == o2.isDefined =>
        unify1(dt1, dt2)
        unify1(rt1, rt2)
        unify0(s1, s2)
        o1.zip(o2).foreach(unify0)
        cs1.zip(cs2).foreach { case ((x1, b1), (x2, b2)) =>
          if x1 != x2 then
            err(
              s"cannot unify ${quote0(a, UnfoldNone)} ~ ${quote0(b, UnfoldNone)}"
            )
          goClos(b1, b2)
        }
      case (Val0.RecordCon(_, f1), Val0.RecordCon(_, f2))
          if f1.size == f2.size =>
        f1.zip(f2).foreach(unify0)
      case _ =>
        err(s"cannot unify ${quote0(a, UnfoldNone)} ~ ${quote0(b, UnfoldNone)}")

  private def unify1(top1: Val1, sp1: Spine, top2: Val1, sp2: Spine)(using
      lvl: Lvl
  ): Unit =
    (sp1, sp2) match
      case (Spine.Empty, Spine.Empty)                     => ()
      case (Spine.App(sp1, a1, _), Spine.App(sp2, a2, _)) =>
        unify1(top1, sp1, top2, sp2); unify1(a1, a2)
      case _ =>
        err(
          s"spine mismatch ${quote1(top1, UnfoldNone)} ~ ${quote1(top2, UnfoldNone)}"
        )

  def unify1(a: Val1, b: Val1)(using lvl: Lvl): Unit =
    inline def unifyErr(): Nothing =
      err(s"cannot unify ${quote1(a, UnfoldNone)} ~ ${quote1(b, UnfoldNone)}")
    inline def goClos(a: Clos1, b: Clos1): Unit =
      val v = Var1(lvl)
      unify1(a(v), b(v))(using lvl + 1)
    def goRec(f1: ClosRec, f2: ClosRec): Unit =
      def go(
          lvl: Lvl,
          env1: Env,
          f1: List[(Name, Ty)],
          env2: Env,
          f2: List[(Name, Ty)]
      ): Unit =
        (f1, f2) match
          case (Nil, Nil)                                           => ()
          case ((x1, ty1) :: rest1, (x2, ty2) :: rest2) if x1 == x2 =>
            unify1(eval1(ty1)(using env1), eval1(ty2)(using env2))(using lvl)
            val v = Var1(lvl)
            go(lvl + 1, Env.E1(env1, v), rest1, Env.E1(env2, v), rest2)
          case _ => unifyErr()
      go(lvl, f1.env, f1.fields, f2.env, f2.fields)
    (a, b) match
      case (Val1.Rigid(x, sp1), Val1.Rigid(y, sp2)) if x == y =>
        unify1(a, sp1, b, sp2)

      case (Val1.Lift(cv1, ty1), Val1.Lift(cv2, ty2)) =>
        unify1(cv1, cv2); unify1(ty1, ty2)
      case (Val1.Quote(v1), Val1.Quote(v2)) => unify0(v1, v2)
      case (Val1.Pi(_, i1, ty1, b1), Val1.Pi(_, i2, ty2, b2)) if i1 == i2 =>
        unify1(ty1, ty2); goClos(b1, b2)
      case (Val1.Fun(t1, cv1, r1), Val1.Fun(t2, cv2, r2)) =>
        unify1(t1, t2); unify1(cv1, cv2); unify1(r1, r2)
      case (Val1.UMeta, Val1.UMeta)       => ()
      case (Val1.UTy(cv1), Val1.UTy(cv2)) => unify1(cv1, cv2)
      case (Val1.CV, Val1.CV)             => ()
      case (Val1.Val, Val1.Val)           => ()
      case (Val1.Comp, Val1.Comp)         => ()

      case (Val1.RecordTy1(f1), Val1.RecordTy1(f2)) => goRec(f1, f2)
      case (Val1.RecordTy0(f1), Val1.RecordTy0(f2))
          if f1.map(_._1) == f2.map(_._1) =>
        f1.zip(f2).foreach { case ((_, t1), (_, t2)) => unify1(t1, t2) }

      case (Val1.Lam(_, _, _, b1), Val1.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (Val1.Lam(_, i, _, b), f)                      =>
        val v = Var1(lvl)
        unify1(b(v), app1(f, v, i))(using lvl + 1)
      case (f, Val1.Lam(_, i, _, b)) =>
        val v = Var1(lvl)
        unify1(app1(f, v, i), b(v))(using lvl + 1)

      case (Val1.RecordCon(f1), Val1.RecordCon(f2)) if f1.size == f2.size =>
        f1.zip(f2).foreach((a, b) => unify1(a, b))
      // TODO: eta for records

      case (Val1.Unfold(h1, sp1, v1), Val1.Unfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnificationError => unify1(v1(), v2())
      case (Val1.Unfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, Val1.Unfold(_, _, v2)) => unify1(v1, v2())

      case _ => unifyErr()
