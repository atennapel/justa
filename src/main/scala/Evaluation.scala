import Common.*
import Common.Icit.*
import Core.*
import State.MetaEntry

import scala.annotation.tailrec

object Evaluation:
  // closure application
  extension (c: Clos0)
    inline def apply(v: Val0): Val0 = c match
      case Clos0.Clos(env, tm) => eval0(tm)(using Env.Ext0(env, v))
      case Clos0.Fun(f)        => f(v)
  extension (c: Clos1)
    inline def apply(v: Val1): Val1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.Ext1(env, v))
      case Clos1.Fun(f)        => f(v)
    inline def apply(v: Val0): Val1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.Ext0(env, v))
      case Clos1.Fun(_)        => impossible()

  // evaluation
  @tailrec
  private def var0(ix: Ix)(using env: Env): Val0 =
    env match
      case Env.Ext0(_, v) if ix.expose == 0 => v
      case Env.Ext0(env, _)                 => var0(ix - 1)(using env)
      case Env.Ext1(env, _)                 => var0(ix - 1)(using env)
      case Env.Empty                        => impossible()

  @tailrec
  private def var1(ix: Ix)(using env: Env): Val1 =
    env match
      case Env.Ext1(_, v) if ix.expose == 0 => v
      case Env.Ext0(env, _)                 => var1(ix - 1)(using env)
      case Env.Ext1(env, _)                 => var1(ix - 1)(using env)
      case Env.Empty                        => impossible()

  private def vmeta(id: MetaId): Val1 = State.getMeta(id) match
    case MetaEntry.Unsolved(_)      => Val1.Flex(id, Spine.Empty)
    case MetaEntry.Solved(value, _) => value

  private def vsplice(v: Val1): Val0 = v match
    case Val1.Quote(v) => v
    case v             => Val0.Splice(v)

  private def vquote(v: Val0): Val1 = v match
    case Val0.Splice(v) => v
    case v              => Val1.Quote(v)

  def vapp1(f: Val1, a: Val1, i: Icit): Val1 = f match
    case Val1.Lam(x, _, _, b) => b(a)
    case Val1.Flex(id, sp)    => Val1.Flex(id, Spine.App(sp, a, i))
    case Val1.Rigid(h, sp)    => Val1.Rigid(h, Spine.App(sp, a, i))
    case Val1.Unfold(h, sp, v) =>
      Val1.Unfold(h, Spine.App(sp, a, i), () => vapp1(v(), a, i))
    case _ => impossible()
  inline def vapp1E(f: Val1, a: Val1): Val1 = vapp1(f, a, Expl)
  inline def vapp1I(f: Val1, a: Val1): Val1 = vapp1(f, a, Impl)

  private def vmetaapp1(f: Val1, a: Val1): Val1 = f match
    case Val1.MetaLam1(b)  => b(a)
    case Val1.Flex(id, sp) => Val1.Flex(id, Spine.MetaApp1(sp, a))
    case Val1.Unfold(h, sp, v) =>
      Val1.Unfold(h, Spine.MetaApp1(sp, a), () => vmetaapp1(v(), a))
    case _ => impossible()

  private def vmetaapp0(f: Val1, a: Val0): Val1 = f match
    case Val1.MetaLam0(b)  => b(a)
    case Val1.Flex(id, sp) => Val1.Flex(id, Spine.MetaApp0(sp, a))
    case Val1.Unfold(h, sp, v) =>
      Val1.Unfold(h, Spine.MetaApp0(sp, a), () => vmetaapp0(v(), a))
    case _ => impossible()

  private def vspine(v: Val1, sp: Spine): Val1 = sp match
    case Spine.Empty           => v
    case Spine.App(sp, a, i)   => vapp1(vspine(v, sp), a, i)
    case Spine.MetaApp1(sp, a) => vmetaapp1(vspine(v, sp), a)
    case Spine.MetaApp0(sp, a) => vmetaapp0(vspine(v, sp), a)

  private def vappPruning(v: Val1, p: Pruning)(implicit env: Env): Val1 =
    (env, p) match
      case (Env.Empty, Nil) => v
      case (Env.Ext1(env, _), PruneEntry.Skip :: p) =>
        vappPruning(v, p)(using env)
      case (Env.Ext0(env, _), PruneEntry.Skip :: p) =>
        vappPruning(v, p)(using env)
      case (Env.Ext1(env, u), PruneEntry.Bind1(i) :: p) =>
        vmetaapp1(vappPruning(v, p)(using env), u)
      case (Env.Ext0(env, u), PruneEntry.Bind0 :: p) =>
        vmetaapp0(vappPruning(v, p)(using env), u)
      case _ => impossible()

  def eval0(t: Tm0)(using env: Env): Val0 = t match
    case Tm0.Var(ix)          => var0(ix)
    case Tm0.Let(x, ty, v, b) => Val0.Let(x, eval1(ty), eval0(v), Clos0(b))
    case Tm0.LetRec(x, ty, v, b) =>
      Val0.LetRec(x, eval1(ty), Clos0(v), Clos0(b))
    case Tm0.Lam(x, ty, b) => Val0.Lam(x, eval1(ty), Clos0(b))
    case Tm0.App(f, a)     => Val0.App(eval0(f), eval0(a))
    case Tm0.Splice(tm)    => vsplice(eval1(tm))
    case Tm0.Wk1(tm)       => eval0(t)(using env.wk1)
    case Tm0.Wk0(tm)       => eval0(t)(using env.wk0)

  def eval1(t: Tm1)(using env: Env): Val1 = t match
    case Tm1.Var(ix)          => var1(ix)
    case Tm1.Prim(p)          => Val1.Prim(p)
    case Tm1.Let(x, ty, v, b) => eval1(b)(using Env.Ext1(env, eval1(v)))
    case Tm1.Pi(x, i, ty, b)  => Val1.Pi(x, i, eval1(ty), Clos1(b))
    case Tm1.Lam(x, i, ty, b) => Val1.Lam(x, i, eval1(ty), Clos1(b))
    case Tm1.App(f, a, i)     => vapp1(eval1(f), eval1(a), i)
    case Tm1.Fun(p, cv, r)    => Val1.Fun(eval1(p), eval1(cv), eval1(r))
    case Tm1.Lift(cv, ty)     => Val1.Lift(eval1(cv), eval1(ty))
    case Tm1.Quote(tm)        => vquote(eval0(tm))
    case Tm1.Wk0(tm)          => eval1(tm)(using env.wk0)
    case Tm1.Wk1(tm)          => eval1(tm)(using env.wk1)
    case Tm1.Meta(id)         => vmeta(id)
    case Tm1.MetaPi1(ty, b)   => Val1.MetaPi1(eval1(t), Clos1(b))
    case Tm1.MetaPi0(ty, b)   => Val1.MetaPi0(eval1(t), Clos1(b))
    case Tm1.MetaLam1(b)      => Val1.MetaLam1(Clos1(b))
    case Tm1.MetaLam0(b)      => Val1.MetaLam0(Clos1(b))
    case Tm1.MetaApp1(f, a)   => vmetaapp1(eval1(f), eval1(a))
    case Tm1.MetaApp0(f, a)   => vmetaapp0(eval1(f), eval0(a))
    case Tm1.AppPruning(m, p) => vappPruning(vmeta(m), p)

  // forcing
  def force1(v: Val1): Val1 = v match
    case top @ Val1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => vspine(v, sp)
    case v => v

  def forceAll1(v: Val1): Val1 = v match
    case top @ Val1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceAll1(vspine(v, sp))
    case Val1.Unfold(_, _, v) => forceAll1(v())
    case v                    => v

  @tailrec
  def forceAll0(v: Val0): Val0 = v match
    case top @ Val0.Splice(v) =>
      forceAll1(v) match
        case Val1.Quote(v) => forceAll0(v)
        case _             => top
    case v => v

  def forceMetas1(v: Val1): Val1 = v match
    case top @ Val1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceMetas1(vspine(v, sp))
    case v => v

  @tailrec
  def forceMetas0(v: Val0): Val0 = v match
    case top @ Val0.Splice(v) =>
      forceMetas1(v) match
        case Val1.Quote(v) => forceMetas0(v)
        case _             => top
    case v => v

  @tailrec
  def forceUnstage0(v: Val0): Val0 = v match
    case top @ Val0.Splice(v) =>
      forceAll1(v) match
        case Val1.Quote(v) => forceUnstage0(v)
        case _             => top
    case v => v

  def forceUnstage1(v: Val1): Val1 = v match
    case top @ Val1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceUnstage1(vspine(v, sp))
    case Val1.Unfold(_, _, v) => forceUnstage1(v())
    case v                    => v

  // readback
  enum UnfoldOption:
    case All
    case Metas
    case None
    case Unstage

  private def readbackSpine(h: Tm1, sp: Spine)(using
      lvl: Lvl,
      q: UnfoldOption
  ): Tm1 = sp match
    case Spine.Empty         => h
    case Spine.App(sp, v, i) => Tm1.App(readbackSpine(h, sp), readback1(v), i)
    case Spine.MetaApp1(sp, v) =>
      Tm1.MetaApp1(readbackSpine(h, sp), readback1(v))
    case Spine.MetaApp0(sp, v) =>
      Tm1.MetaApp0(readbackSpine(h, sp), readback0(v))

  def readback1(v: Val1)(using lvl: Lvl, q: UnfoldOption): Tm1 =
    inline def go0(v: Val0): Tm0 = readback0(v)
    inline def go1(v: Val1): Tm1 = readback1(v)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = readbackSpine(h, sp)
    inline def goClos(c: Clos1): Tm1 =
      readback1(c(Val1.Var(lvl)))(using lvl + 1)
    inline def goClos0(c: Clos1): Tm1 =
      readback1(c(Val0.Var(lvl)))(using lvl + 1)
    inline def force(v: Val1): Val1 = q match
      case UnfoldOption.All     => forceAll1(v)
      case UnfoldOption.Metas   => forceMetas1(v)
      case UnfoldOption.None    => force1(v)
      case UnfoldOption.Unstage => forceUnstage1(v)
    force(v) match
      case Val1.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl) => goSp(Tm1.Var(lvl.toIx), sp)
          case Head.Prim(p)  => goSp(Tm1.Prim(p), sp)
      case Val1.Flex(id, sp)      => goSp(Tm1.Meta(id), sp)
      case Val1.Unfold(h, sp, _)  => goSp(h, sp)
      case Val1.Pi(x, i, ty, b)   => Tm1.Pi(x, i, go1(ty), goClos(b))
      case Val1.Lam(x, i, ty, b)  => Tm1.Lam(x, i, go1(ty), goClos(b))
      case Val1.Fun(pty, cv, rty) => Tm1.Fun(go1(pty), go1(cv), go1(rty))
      case Val1.Lift(cv, ty)      => Tm1.Lift(go1(cv), go1(ty))
      case Val1.Quote(tm)         => go0(tm).quote
      case Val1.MetaPi1(t, b)     => Tm1.MetaPi1(go1(t), goClos(b))
      case Val1.MetaPi0(t, b)     => Tm1.MetaPi0(go1(t), goClos0(b))
      case Val1.MetaLam1(b)       => Tm1.MetaLam1(goClos(b))
      case Val1.MetaLam0(b)       => Tm1.MetaLam0(goClos0(b))

  def readback0(v: Val0)(using lvl: Lvl, q: UnfoldOption): Tm0 =
    inline def go0(v: Val0): Tm0 = readback0(v)
    inline def go1(v: Val1): Tm1 = readback1(v)
    inline def goClos(c: Clos0): Tm0 =
      readback0(c(Val0.Var(lvl)))(using lvl + 1)
    inline def force(v: Val0): Val0 = q match
      case UnfoldOption.All     => forceAll0(v)
      case UnfoldOption.Metas   => forceMetas0(v)
      case UnfoldOption.None    => v
      case UnfoldOption.Unstage => forceUnstage0(v)
    force(v) match
      case Val0.Var(x)           => Tm0.Var(x.toIx)
      case Val0.Let(x, ty, v, b) => Tm0.Let(x, go1(ty), go0(v), goClos(b))
      case Val0.LetRec(x, ty, v, b) =>
        Tm0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case Val0.Lam(x, ty, b) => Tm0.Lam(x, go1(ty), goClos(b))
      case Val0.App(f, a)     => Tm0.App(go0(f), go0(a))
      case Val0.Splice(tm)    => go1(tm).splice

  // helpers
  def unstage(tm: Tm0): Tm0 =
    readback0(eval0(tm)(using Env.Empty))(using lvl0, UnfoldOption.Unstage)
  def unstageUnder(tm: Tm0, env: Env): Tm0 =
    readback0(eval0(tm)(using env))(using mkLvl(env.size), UnfoldOption.Unstage)
