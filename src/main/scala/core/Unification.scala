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
      case (Val0.Con(k1, m1, x), Val0.Con(k2, m2, y))
          if k1 == k2 && m1 == m2 && x == y =>
        ()
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
    inline def goClos(a: Clos1, b: Clos1): Unit =
      val v = Var1(lvl)
      unify1(a(v), b(v))(using lvl + 1)
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

      case (Val1.Lam(_, _, _, b1), Val1.Lam(_, _, _, b2)) => goClos(b1, b2)
      case (Val1.Lam(_, i, _, b), f)                      =>
        val v = Var1(lvl)
        unify1(b(v), app1(f, v, i))(using lvl + 1)
      case (f, Val1.Lam(_, i, _, b)) =>
        val v = Var1(lvl)
        unify1(app1(f, v, i), b(v))(using lvl + 1)

      case (Val1.Unfold(h1, sp1, v1), Val1.Unfold(h2, sp2, v2)) =>
        try
          if h1 != h2 then err("head mismatch")
          unify1(a, sp1, b, sp2)
        catch case _: UnificationError => unify1(v1(), v2())
      case (Val1.Unfold(_, _, v1), v2) => unify1(v1(), v2)
      case (v1, Val1.Unfold(_, _, v2)) => unify1(v1, v2())

      case _ =>
        err(s"cannot unify ${quote1(a, UnfoldNone)} ~ ${quote1(b, UnfoldNone)}")
