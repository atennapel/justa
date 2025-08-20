package core

import common.Common.*
import Core.*

import scala.annotation.tailrec

object Evaluation:
  enum QuoteOption:
    case UnfoldAll
    case UnfoldNone
    case UnfoldStage

  // closures
  extension (c: Clos0)
    inline def apply(v: Val0): Val0 = c match
      case Clos0.Clos(env, tm) => eval0(tm)(using Env.E0(env, v))
      case Clos0.Fun(f)        => f(v)
  extension (c: Clos1)
    inline def apply(v: Val1): Val1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.E1(env, v))
      case Clos1.Fun(f)        => f(v)
    inline def apply(v: Val0): Val1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.E0(env, v))
      case Clos1.Fun(_)        => impossible()

  // evaluation
  @tailrec
  def var0(ix: Ix)(using e: Env): Val0 =
    e match
      case Env.E0(_, v) if ix.expose == 0 => v
      case Env.E0(env, _)                 => var0(ix - 1)(using env)
      case Env.E1(env, _)                 => var0(ix - 1)(using env)
      case Env.Empty                      => impossible()

  @tailrec
  def var1(ix: Ix)(using e: Env): Val1 =
    e match
      case Env.E1(_, v) if ix.expose == 0 => v
      case Env.E0(env, _)                 => var1(ix - 1)(using env)
      case Env.E1(env, _)                 => var1(ix - 1)(using env)
      case Env.Empty                      => impossible()

  def splice(v: Val1): Val0 = v match
    case Val1.Quote(v) => v
    case v             => Val0.Splice(v)

  def quote(v: Val0): Val1 = v match
    case Val0.Splice(v) => v
    case v              => Val1.Quote(v)

  def app1(f: Val1, a: Val1, i: Icit): Val1 = f match
    case Val1.Lam(x, _, _, b)  => b(a)
    case Val1.Rigid(h, sp)     => Val1.Rigid(h, Spine.App(sp, a, i))
    case Val1.Unfold(h, sp, v) =>
      Val1.Unfold(h, Spine.App(sp, a, i), () => app1(v(), a, i))
    case _ => impossible()
  inline def appE(f: Val1, a: Val1): Val1 =
    app1(f, a, Icit.Expl)
  inline def appI(f: Val1, a: Val1): Val1 = app1(f, a, Icit.Impl)

  def spine(v: Val1, sp: Spine): Val1 = sp match
    case Spine.Empty         => v
    case Spine.App(sp, a, i) => app1(spine(v, sp), a, i)

  def eval0(t: Tm0)(using env: Env): Val0 =
    t match
      case Tm0.Var(ix)              => var0(ix)
      case Tm0.IntLit(v)            => Val0.IntLit(v)
      case Tm0.Global(m, x)         => Val0.Global(m, x)
      case Tm0.Select(dt, cx, s, i) => Val0.Select(eval1(dt), cx, eval0(s), i)
      case Tm0.Let(x, ty, v, b)    => Val0.Let(x, eval1(ty), eval0(v), Clos0(b))
      case Tm0.LetRec(x, ty, v, b) =>
        Val0.LetRec(x, eval1(ty), Clos0(v), Clos0(b))
      case Tm0.Lam(x, ty, b)           => Val0.Lam(x, eval1(ty), Clos0(b))
      case Tm0.App(f, a)               => Val0.App(eval0(f), eval0(a))
      case Tm0.Splice(t)               => splice(eval1(t))
      case Tm0.Instr(op, ts, rt, args) =>
        Val0.Instr(op, ts.map(eval1), eval1(rt), args.map(eval0))
      case Tm0.Match(rt, dt, s, cs, o) =>
        Val0.Match(
          eval1(rt),
          eval1(dt),
          eval0(s),
          cs.map((x, b) => (x, Clos0(b))),
          o.map(eval0)
        )
      case Tm0.RecordCon(ty, fs) => Val0.RecordCon(eval1(ty), fs.map(eval0))
      case Tm0.Wk1(t)            => eval0(t)(using env.wk1)
      case Tm0.Wk0(t)            => eval0(t)(using env.wk0)

  def eval1(t: Tm1)(using env: Env): Val1 =
    t match
      case Tm1.Var(ix)          => var1(ix)
      case Tm1.Primitive(m, x)  => VPrimitive(m, x)
      case Tm1.Con(m, dx, cx)   => VCon(m, dx, cx, Nil)
      case Tm1.TypeCon(k, m, x) => VTypeCon(k, m, x, Nil)
      case Tm1.Global(m, x, v)  =>
        Val1.Unfold(UnfoldHead.Global(m, x, v), Spine.Empty, () => v)
      case Tm1.Let(_, _, v, b)  => eval1(b)(using Env.E1(env, eval1(v)))
      case Tm1.UTy(cv)          => Val1.UTy(eval1(cv))
      case Tm1.UMeta            => Val1.UMeta
      case Tm1.CV               => Val1.CV
      case Tm1.Val              => Val1.Val
      case Tm1.Comp             => Val1.Comp
      case Tm1.Pi(x, i, ty, b)  => Val1.Pi(x, i, eval1(ty), Clos1(b))
      case Tm1.Lam(x, i, ty, b) => Val1.Lam(x, i, eval1(ty), Clos1(b))
      case Tm1.App(f, a, i)     => app1(eval1(f), eval1(a), i)
      case Tm1.Fun(p, cv, r)    => Val1.Fun(eval1(p), eval1(cv), eval1(r))
      case Tm1.Lift(cv, ty)     => Val1.Lift(eval1(cv), eval1(ty))
      case Tm1.Quote(tm)        => quote(eval0(tm))
      case Tm1.RecordTy1(fs)    => Val1.RecordTy1(ClosRec(fs))
      case Tm1.RecordTy0(fs) => Val1.RecordTy0(fs.map((x, t) => (x, eval1(t))))
      case Tm1.RecordCon(fs) => Val1.RecordCon(fs.map(eval1))
      case Tm1.Wk0(tm)       => eval1(tm)(using env.wk0)
      case Tm1.Wk1(tm)       => eval1(tm)(using env.wk1)

  // forcing
  @tailrec
  def forceAll1(v: Val1): Val1 = v match
    case Val1.Unfold(_, _, v) => forceAll1(v())
    case v                    => v

  @tailrec
  def forceAll0(v: Val0): Val0 = v match
    case top @ Val0.Splice(v) =>
      forceAll1(v) match
        case Val1.Quote(v) => forceAll0(v)
        case _             => top
    case v => v

  @tailrec
  def forceStage0(v: Val0): Val0 = v match
    case top @ Val0.Splice(v) =>
      forceAll1(v) match
        case Val1.Quote(v) => forceStage0(v)
        case _             => top
    case v => v

  @tailrec
  def forceStage1(v: Val1): Val1 = v match
    case Val1.Unfold(_, _, v) => forceStage1(v())
    case v                    => v

  // quoting
  private def quote1(h: Tm1, sp: Spine, q: QuoteOption)(using lvl: Lvl): Tm1 =
    sp match
      case Spine.Empty         => h
      case Spine.App(sp, v, i) => Tm1.App(quote1(h, sp, q), quote1(v, q), i)

  def quote1(v: Val1, q: QuoteOption)(using lvl: Lvl): Tm1 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = quote1(h, sp, q)
    inline def goClos(c: Clos1): Tm1 = quote1(c(Var1(lvl)), q)(using lvl + 1)
    inline def force(v: Val1): Val1 = q match
      case QuoteOption.UnfoldAll   => forceAll1(v)
      case QuoteOption.UnfoldNone  => v
      case QuoteOption.UnfoldStage => forceStage1(v)
    def goRec(c: ClosRec): List[(Name, Ty)] =
      def go(env: Env, lvl: Lvl, fs: List[(Name, Ty)]): List[(Name, Ty)] =
        fs match
          case Nil             => Nil
          case (x, ty) :: rest =>
            val qty = quote1(eval1(ty)(using env), q)(using lvl)
            (x, qty) :: go(Env.E1(env, Var1(lvl)), lvl + 1, rest)
      go(c.env, lvl, c.fields)
    force(v) match
      case Val1.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl)         => goSp(Tm1.Var(lvl.toIx), sp)
          case Head.Primitive(m, x)  => goSp(Tm1.Primitive(m, x), sp)
          case Head.Con(m, x, cx)    => goSp(Tm1.Con(m, x, cx), sp)
          case Head.TypeCon(k, m, x) => goSp(Tm1.TypeCon(k, m, x), sp)
      case Val1.Unfold(UnfoldHead.Global(m, x, v), sp, _) =>
        goSp(Tm1.Global(m, x, v), sp)
      case Val1.Pi(x, i, ty, b)   => Tm1.Pi(x, i, go1(ty), goClos(b))
      case Val1.Lam(x, i, ty, b)  => Tm1.Lam(x, i, go1(ty), goClos(b))
      case Val1.UTy(cv)           => Tm1.UTy(go1(cv))
      case Val1.UMeta             => Tm1.UMeta
      case Val1.CV                => Tm1.CV
      case Val1.Val               => Tm1.Val
      case Val1.Comp              => Tm1.Comp
      case Val1.Fun(pty, cv, rty) => Tm1.Fun(go1(pty), go1(cv), go1(rty))
      case Val1.Lift(cv, ty)      => Tm1.Lift(go1(cv), go1(ty))
      case Val1.Quote(tm)         => go0(tm).quote
      case Val1.RecordTy1(fs)     => Tm1.RecordTy1(goRec(fs))
      case Val1.RecordTy0(fs) => Tm1.RecordTy0(fs.map((x, t) => (x, go1(t))))
      case Val1.RecordCon(fs) => Tm1.RecordCon(fs.map(t => go1(t)))

  def quote0(v: Val0, q: QuoteOption)(using lvl: Lvl): Tm0 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goClos(c: Clos0): Tm0 =
      quote0(c(Val0.Var(lvl)), q)(using lvl + 1)
    inline def force(v: Val0): Val0 = q match
      case QuoteOption.UnfoldAll   => forceAll0(v)
      case QuoteOption.UnfoldNone  => v
      case QuoteOption.UnfoldStage => forceStage0(v)
    force(v) match
      case Val0.Var(x)               => Tm0.Var(x.toIx)
      case Val0.IntLit(v)            => Tm0.IntLit(v)
      case Val0.Global(m, x)         => Tm0.Global(m, x)
      case Val0.Select(dt, cx, s, i) => Tm0.Select(go1(dt), cx, go0(s), i)
      case Val0.Let(x, ty, v, b)     =>
        Tm0.Let(x, go1(ty), go0(v), goClos(b))
      case Val0.LetRec(x, ty, v, b) =>
        Tm0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case Val0.Lam(x, ty, b)           => Tm0.Lam(x, go1(ty), goClos(b))
      case Val0.App(f, a)               => Tm0.App(go0(f), go0(a))
      case Val0.Splice(tm)              => go1(tm).splice
      case Val0.Instr(op, ts, rt, args) =>
        Tm0.Instr(op, ts.map(go1), go1(rt), args.map(go0))
      case Val0.Match(rt, dt, s, cs, o) =>
        Tm0.Match(
          go1(rt),
          go1(dt),
          go0(s),
          cs.map((x, b) => (x, goClos(b))),
          o.map(go0)
        )
      case Val0.RecordCon(ty, fs) => Tm0.RecordCon(go1(ty), fs.map(t => go0(t)))

  def nf(tm: Tm1, q: QuoteOption = QuoteOption.UnfoldAll): Tm1 =
    quote1(eval1(tm)(using Env.Empty), q)(using lvl0)
  def nfWithEnv(
      tm: Tm1,
      env: Env,
      q: QuoteOption = QuoteOption.UnfoldAll
  ): Tm1 =
    quote1(eval1(tm)(using env), q)(using env.lvl)
  def unstage0(tm: Tm0): Tm0 =
    quote0(eval0(tm)(using Env.Empty), QuoteOption.UnfoldStage)(using lvl0)
  def unstage0Under(tm: Tm0, env: Env): Tm0 =
    quote0(eval0(tm)(using env), QuoteOption.UnfoldStage)(using env.lvl)
