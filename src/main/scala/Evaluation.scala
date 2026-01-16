import Common.*
import Common.Icit.*
import Core.*
import Core.{Val1 as V1, Val0 as V0, Tm1 as T1, Tm0 as T0}
import State.MetaEntry

import scala.annotation.tailrec
import scala.collection.mutable

object Evaluation:
  // closure application
  extension (c: Clos0)
    inline def apply(v: V0): V0 = c match
      case Clos0.Clos(env, tm) => eval0(tm)(using Env.Ext0(env, v))
      case Clos0.Fun(f)        => f(v)
  extension (c: Clos1)
    inline def apply(v: V1): V1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.Ext1(env, v))
      case Clos1.Fun(f)        => f(v)
    inline def apply(v: V0): V1 = c match
      case Clos1.Clos(env, tm) => eval1(tm)(using Env.Ext0(env, v))
      case Clos1.Fun(_)        => impossible()

  // evaluation
  @tailrec
  private def var0(ix: Ix)(using env: Env): V0 =
    env match
      case Env.Ext0(_, v) if ix.expose == 0 => v
      case Env.Ext0(env, _)                 => var0(ix - 1)(using env)
      case Env.Ext1(env, _)                 => var0(ix - 1)(using env)
      case Env.Empty                        => impossible()

  @tailrec
  private def var1(ix: Ix)(using env: Env): V1 =
    env match
      case Env.Ext1(_, v) if ix.expose == 0 => v
      case Env.Ext0(env, _)                 => var1(ix - 1)(using env)
      case Env.Ext1(env, _)                 => var1(ix - 1)(using env)
      case Env.Empty                        => impossible()

  private def vmeta(id: MetaId): V1 = State.getMeta(id) match
    case MetaEntry.Unsolved(_)      => V1.Flex(id, Spine.Empty)
    case MetaEntry.Solved(value, _) => value

  def vsplice(v: V1): V0 = v match
    case V1.Quote(v) => v
    case v           => V0.Splice(v)

  def vquote(v: V0): V1 = v match
    case V0.Splice(v) => v
    case v            => V1.Quote(v)

  def vapp1(f: V1, a: V1, i: Icit): V1 = f match
    case V1.Lam(x, _, _, b) => b(a)
    case V1.Flex(id, sp)    => V1.Flex(id, Spine.App(sp, a, i))
    case V1.Rigid(h, sp)    => V1.Rigid(h, Spine.App(sp, a, i))
    case V1.Unfold(h, sp, v) =>
      V1.Unfold(h, Spine.App(sp, a, i), () => vapp1(v(), a, i))
    case _ => impossible()
  inline def vappE(f: V1, a: V1): V1 = vapp1(f, a, Expl)
  inline def vappI(f: V1, a: V1): V1 = vapp1(f, a, Impl)

  def vmetaapp1(f: V1, a: V1): V1 = f match
    case V1.MetaLam1(b)  => b(a)
    case V1.Flex(id, sp) => V1.Flex(id, Spine.MetaApp1(sp, a))
    case V1.Unfold(h, sp, v) =>
      V1.Unfold(h, Spine.MetaApp1(sp, a), () => vmetaapp1(v(), a))
    case _ => impossible()

  def vmetaapp0(f: V1, a: V0): V1 = f match
    case V1.MetaLam0(b)  => b(a)
    case V1.Flex(id, sp) => V1.Flex(id, Spine.MetaApp0(sp, a))
    case V1.Unfold(h, sp, v) =>
      V1.Unfold(h, Spine.MetaApp0(sp, a), () => vmetaapp0(v(), a))
    case _ => impossible()

  private def vspine(v: V1, sp: Spine): V1 = sp match
    case Spine.Empty           => v
    case Spine.App(sp, a, i)   => vapp1(vspine(v, sp), a, i)
    case Spine.MetaApp1(sp, a) => vmetaapp1(vspine(v, sp), a)
    case Spine.MetaApp0(sp, a) => vmetaapp0(vspine(v, sp), a)

  private def vappPruning(v: V1, p: Pruning)(using env: Env): V1 =
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

  def eval0(t: T0)(using env: Env): V0 =
    t match
      case T0.Var(ix)          => var0(ix)
      case T0.Global(m, x)     => V0.Global(m, x)
      case T0.IntLit(v)        => V0.IntLit(v)
      case T0.Let(x, ty, v, b) => V0.Let(x, eval1(ty), eval0(v), Clos0(b))
      case T0.LetRec(x, ty, v, b) =>
        V0.LetRec(x, eval1(ty), Clos0(v), Clos0(b))
      case T0.Lam(x, ty, b)   => V0.Lam(x, eval1(ty), Clos0(b))
      case T0.App(f, a)       => V0.App(eval0(f), eval0(a))
      case T0.Splice(tm)      => vsplice(eval1(tm))
      case T0.If(ty, c, t, f) => V0.If(eval1(ty), eval0(c), eval0(t), eval0(f))
      case T0.Case(rty, dty, s, cs) =>
        V0.Case(eval1(rty), eval1(dty), eval0(s), ClosCases(cs))
      case T0.Select(rty, s, x, i) => V0.Select(eval1(rty), eval0(s), x, i)
      case T0.Wk1(t)               => eval0(t)(using env.wk1)
      case T0.Wk0(t)               => eval0(t)(using env.wk0)

  def eval1(t: T1)(using env: Env): V1 =
    t match
      case T1.Var(ix) => var1(ix)
      case T1.Global(m, x, v) =>
        V1.Unfold(UnfoldHead.Global(m, x, v), Spine.Empty, () => v)
      case T1.Prim(p)          => V1.Prim(p)
      case T1.TypeCon(m, x)    => V1.TypeCon(m, x)
      case T1.Con(m, dx, cx)   => V1.Con(m, dx, cx)
      case T1.Let(x, ty, v, b) => eval1(b)(using Env.Ext1(env, eval1(v)))
      case T1.Pi(x, i, ty, b)  => V1.Pi(x, i, eval1(ty), Clos1(b))
      case T1.Lam(x, i, ty, b) => V1.Lam(x, i, eval1(ty), Clos1(b))
      case T1.App(f, a, i)     => vapp1(eval1(f), eval1(a), i)
      case T1.Fun(p, cv, r)    => V1.Fun(eval1(p), eval1(cv), eval1(r))
      case T1.Lift(cv, ty)     => V1.Lift(eval1(cv), eval1(ty))
      case T1.Quote(tm)        => vquote(eval0(tm))
      case T1.Wk0(tm)          => eval1(tm)(using env.wk0)
      case T1.Wk1(tm)          => eval1(tm)(using env.wk1)
      case T1.Meta(id)         => vmeta(id)
      case T1.MetaPi1(t, b)    => V1.MetaPi1(eval1(t), Clos1(b))
      case T1.MetaPi0(t, b)    => V1.MetaPi0(eval1(t), Clos1(b))
      case T1.MetaLam1(b)      => V1.MetaLam1(Clos1(b))
      case T1.MetaLam0(b)      => V1.MetaLam0(Clos1(b))
      case T1.MetaApp1(f, a)   => vmetaapp1(eval1(f), eval1(a))
      case T1.MetaApp0(f, a)   => vmetaapp0(eval1(f), eval0(a))
      case T1.AppPruning(m, p) => vappPruning(vmeta(m), p)

  // forcing
  def force1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => vspine(v, sp)
    case v => v

  def forceAll1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceAll1(vspine(v, sp))
    case V1.Unfold(_, _, v) => forceAll1(v())
    case v                  => v

  @tailrec
  def forceAll0(v: V0): V0 = v match
    case top @ V0.Splice(v) =>
      forceAll1(v) match
        case V1.Quote(v) => forceAll0(v)
        case _           => top
    case v => v

  def forceMetas1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceMetas1(vspine(v, sp))
    case v => v

  @tailrec
  def forceMetas0(v: V0): V0 = v match
    case top @ V0.Splice(v) =>
      forceMetas1(v) match
        case V1.Quote(v) => forceMetas0(v)
        case _           => top
    case v => v

  @tailrec
  def forceUnstage0(v: V0): V0 = v match
    case top @ V0.Splice(v) =>
      forceAll1(v) match
        case V1.Quote(v) => forceUnstage0(v)
        case _           => top
    case v => v

  def forceUnstage1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_)  => top
        case MetaEntry.Solved(v, _) => forceUnstage1(vspine(v, sp))
    case V1.Unfold(_, _, v) => forceUnstage1(v())
    case v                  => v

  // readback
  enum UnfoldOption:
    case All
    case Metas
    case None
    case Unstage

  private def readbackSpine(h: T1, sp: Spine)(using
      lvl: Lvl,
      q: UnfoldOption
  ): T1 = sp match
    case Spine.Empty         => h
    case Spine.App(sp, v, i) => T1.App(readbackSpine(h, sp), readback1(v), i)
    case Spine.MetaApp1(sp, v) =>
      T1.MetaApp1(readbackSpine(h, sp), readback1(v))
    case Spine.MetaApp0(sp, v) =>
      T1.MetaApp0(readbackSpine(h, sp), readback0(v))

  def readback1(v: V1)(using lvl: Lvl, unfoldOption: UnfoldOption): T1 =
    inline def go0(v: V0): T0 = readback0(v)
    inline def go1(v: V1): T1 = readback1(v)
    inline def goSp(h: T1, sp: Spine): T1 = readbackSpine(h, sp)
    inline def goClos(c: Clos1): T1 =
      readback1(c(V1.Var(lvl)))(using lvl + 1)
    inline def goClos0(c: Clos1): T1 =
      readback1(c(V0.Var(lvl)))(using lvl + 1)
    inline def force(v: V1): V1 = unfoldOption match
      case UnfoldOption.All     => forceAll1(v)
      case UnfoldOption.Metas   => forceMetas1(v)
      case UnfoldOption.None    => force1(v)
      case UnfoldOption.Unstage => forceUnstage1(v)
    force(v) match
      case V1.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl)       => goSp(T1.Var(lvl.toIx), sp)
          case Head.Prim(p)        => goSp(T1.Prim(p), sp)
          case Head.TypeCon(m, x)  => goSp(T1.TypeCon(m, x), sp)
          case Head.Con(m, dx, cx) => goSp(T1.Con(m, dx, cx), sp)
      case V1.Flex(id, sp) => goSp(T1.Meta(id), sp)
      case V1.Unfold(UnfoldHead.Global(m, x, v), sp, _) =>
        goSp(T1.Global(m, x, v), sp)
      case V1.Pi(x, i, ty, b)   => T1.Pi(x, i, go1(ty), goClos(b))
      case V1.Lam(x, i, ty, b)  => T1.Lam(x, i, go1(ty), goClos(b))
      case V1.Fun(pty, cv, rty) => T1.Fun(go1(pty), go1(cv), go1(rty))
      case V1.Lift(cv, ty)      => T1.Lift(go1(cv), go1(ty))
      case V1.Quote(tm)         => go0(tm).quote
      case V1.MetaPi1(t, b)     => T1.MetaPi1(go1(t), goClos(b))
      case V1.MetaPi0(t, b)     => T1.MetaPi0(go1(t), goClos0(b))
      case V1.MetaLam1(b)       => T1.MetaLam1(goClos(b))
      case V1.MetaLam0(b)       => T1.MetaLam0(goClos0(b))

  def readback0(v: V0)(using lvl: Lvl, unfoldOption: UnfoldOption): T0 =
    inline def go0(v: V0): T0 = readback0(v)
    inline def go1(v: V1): T1 = readback1(v)
    inline def goClos(c: Clos0): T0 =
      readback0(c(V0.Var(lvl)))(using lvl + 1)
    inline def force(v: V0): V0 = unfoldOption match
      case UnfoldOption.All     => forceAll0(v)
      case UnfoldOption.Metas   => forceMetas0(v)
      case UnfoldOption.None    => v
      case UnfoldOption.Unstage => forceUnstage0(v)
    force(v) match
      case V0.Var(x)           => T0.Var(x.toIx)
      case V0.Global(m, x)     => T0.Global(m, x)
      case V0.IntLit(v)        => T0.IntLit(v)
      case V0.Let(x, ty, v, b) => T0.Let(x, go1(ty), go0(v), goClos(b))
      case V0.LetRec(x, ty, v, b) =>
        T0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case V0.Lam(x, ty, b)        => T0.Lam(x, go1(ty), goClos(b))
      case V0.App(f, a)            => T0.App(go0(f), go0(a))
      case V0.If(ty, c, t, f)      => T0.If(go1(ty), go0(c), go0(t), go0(f))
      case V0.Splice(tm)           => go1(tm).splice
      case V0.Select(rty, s, x, i) => T0.Select(go1(rty), go0(s), x, i)
      case V0.Case(rty, dty, s, cs) =>
        def goCases(cs: Cases)(using env: Env): Cases =
          cs match
            case Cases.Empty        => Cases.Empty
            case Cases.Otherwise(b) => Cases.Otherwise(go0(eval0(b)))
            case Cases.Ext(x, ps, b, r) =>
              val (innerlvl, innerenv) = addParams(ps)
              val nps = ps.map((x, ty) => (x, go1(eval1(ty))))
              val rb = readback0(eval0(b)(using innerenv))(using innerlvl)
              Cases.Ext(x, nps, rb, goCases(r))
        T0.Case(
          go1(rty),
          go1(dty),
          go0(s),
          goCases(cs.cases)(using cs.env)
        )

  def addParams(ps: Seq[(Bind, Ty)])(using lvl: Lvl, env: Env): (Lvl, Env) =
    def go(n: Int, lvl: Lvl, env: Env): (Lvl, Env) =
      n match
        case 0 => (lvl, env)
        case n => go(n - 1, lvl + 1, Env.Ext0(env, V0.Var(lvl)))
    go(ps.size, lvl, env)

  // helpers
  inline def readback1m(v: V1)(using lvl: Lvl): T1 =
    readback1(v)(using unfoldOption = UnfoldOption.Metas)
  inline def readback0m(v: V0)(using lvl: Lvl): T0 =
    readback0(v)(using unfoldOption = UnfoldOption.Metas)
  inline def readback1n(v: V1)(using lvl: Lvl): T1 =
    readback1(v)(using unfoldOption = UnfoldOption.None)
  inline def readback0n(v: V0)(using lvl: Lvl): T0 =
    readback0(v)(using unfoldOption = UnfoldOption.None)

  inline def unstage(tm: T0): T0 =
    readback0(eval0(tm)(using Env.Empty))(using lvl0, UnfoldOption.Unstage)
  inline def unstageUnder(tm: T0, env: Env): T0 =
    readback0(eval0(tm)(using env))(using mkLvl(env.size), UnfoldOption.Unstage)

  def allGlobals(v: V1): Set[(Name, Name)] =
    val set = mutable.Set.empty[(Name, Name)]
    inline def goClos1(c: Clos1)(using lvl: Lvl): Unit =
      go1(c(V1.Var(lvl)))(using lvl + 1)
    inline def goClos0(c: Clos0)(using lvl: Lvl): Unit =
      go0(c(V0.Var(lvl)))(using lvl + 1)
    @tailrec
    def goSp(sp: Spine)(using lvl: Lvl): Unit =
      sp match
        case Spine.Empty           => ()
        case Spine.App(sp, a, _)   => go1(a); goSp(sp)
        case Spine.MetaApp1(sp, a) => go1(a); goSp(sp)
        case Spine.MetaApp0(sp, a) => go0(a); goSp(sp)
    def goHead(h: Head): Unit =
      h match
        case Head.Var(_)         => ()
        case Head.Prim(_)        => ()
        case Head.TypeCon(m, x)  => set += ((m, x))
        case Head.Con(m, dx, cx) => set += ((m, dx)); set += ((m, cx))
    def goUnfoldHead(h: UnfoldHead)(using lvl: Lvl): Unit =
      h match
        case UnfoldHead.Global(m, x, v) => set += ((m, x)); go1(v)
    def go1(v: V1)(using lvl: Lvl): Unit =
      v match
        case V1.Rigid(h, sp)      => goHead(h); goSp(sp)
        case V1.Unfold(h, sp, _)  => goUnfoldHead(h); goSp(sp)
        case V1.Pi(_, _, ty, b)   => go1(ty); goClos1(b)
        case V1.Lam(_, _, ty, b)  => go1(ty); goClos1(b)
        case V1.Fun(pty, cv, rty) => go1(pty); go1(cv); go1(rty)
        case V1.Lift(cv, ty)      => go1(cv); go1(ty)
        case V1.Quote(tm)         => go0(tm)
        case V1.MetaPi1(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaPi0(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaLam1(b)       => goClos1(b)
        case V1.MetaLam0(b)       => goClos1(b)
        case V1.Flex(m, sp) =>
          State.getMeta(m) match
            case MetaEntry.Unsolved(_)  => goSp(sp)
            case MetaEntry.Solved(v, _) => go1(vspine(v, sp))
    def go0(v: V0)(using lvl: Lvl): Unit =
      v match
        case V0.Global(m, x)         => set += ((m, x))
        case V0.Var(_)               => ()
        case V0.IntLit(_)            => ()
        case V0.Let(_, ty, v, b)     => go1(ty); go0(v); goClos0(b)
        case V0.LetRec(_, ty, v, b)  => go1(ty); goClos0(v); goClos0(b)
        case V0.Lam(_, ty, b)        => go1(ty); goClos0(b)
        case V0.App(f, a)            => go0(f); go0(a)
        case V0.If(rty, c, t, f)     => go1(rty); go0(c); go0(t); go0(f)
        case V0.Select(rty, s, x, i) => go1(rty); go0(s)
        case V0.Splice(tm)           => go1(tm)
        case V0.Case(rty, dty, s, cs) =>
          go1(rty); go1(dty); go0(s)
          def goCases(cs: Cases)(using env: Env): Unit =
            cs match
              case Cases.Empty        => ()
              case Cases.Otherwise(b) => go0(eval0(b))
              case Cases.Ext(x, ps, b, r) =>
                val (innerlvl, innerenv) = addParams(ps)
                val nps = ps.foreach((_, ty) => go1(eval1(ty)))
                val rb = go0(eval0(b)(using innerenv))(using innerlvl)
                goCases(r)
          goCases(cs.cases)(using cs.env)
    go1(v)(using lvl0)
    set.toSet
