import Common.*
import Common.Icit.*
import Core.*
import Core.{Val1 as V1, Val0 as V0}
import State.{CheckEntry, MetaEntry}

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
    case MetaEntry.Unsolved(_, _)   => V1.Flex(id, Spine.Empty)
    case MetaEntry.Solved(value, _) => value

  private def vcheck(id: CheckId)(using env: Env): V1 =
    State.getCheck(id) match
      case CheckEntry.Checked(tm) => eval1(tm)
      case CheckEntry.Unchecked(ctx, _, _, m) =>
        vappPruning(vmeta(m), ctx.pruning)

  def vsplice(v: V1): V0 = v match
    case V1.Quote(v) => v
    case v           => V0.Splice(v)

  def vquote(v: V0): V1 = v match
    case V0.Splice(v) => v
    case v            => V1.Quote(v)

  def vapp(f: V1, a: V1, i: Icit): V1 = f match
    case V1.Lam(x, _, _, b) => b(a)
    case V1.Flex(id, sp)    => V1.Flex(id, Spine.App(sp, a, i))
    case V1.Rigid(h, sp)    => V1.Rigid(h, Spine.App(sp, a, i))
    case V1.Unfold(h, sp, v) =>
      V1.Unfold(h, Spine.App(sp, a, i), () => vapp(v(), a, i))
    case _ => impossible()
  inline def vappE(f: V1, a: V1): V1 = vapp(f, a, Expl)
  inline def vappI(f: V1, a: V1): V1 = vapp(f, a, Impl)

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

  def vproj(tm: Val1, p: ProjType): Val1 = tm match
    case V1.RecordCon(fs)       => fs(p.ix)
    case V1.Con1(_, _, _, args) => args(p.ix)._1
    case V1.Rigid(h, sp)        => V1.Rigid(h, Spine.Proj(sp, p))
    case V1.Flex(h, sp)         => V1.Flex(h, Spine.Proj(sp, p))
    case V1.Unfold(h, sp, v) =>
      V1.Unfold(h, Spine.Proj(sp, p), () => vproj(v(), p))
    case _ => impossible()
  inline def vprojIx(tm: Val1, ix: Int, name: Option[Name] = None): Val1 =
    vproj(tm, ProjType(name, ix))

  private def velimid(a: V1, x: V1, pp: V1, h: V1, y: V1, p: V1): V1 =
    p match
      case V1.Refl(_, _)    => h
      case V1.Rigid(hh, sp) => V1.Rigid(hh, Spine.ElimId(sp, a, x, pp, h, y))
      case V1.Flex(hh, sp)  => V1.Flex(hh, Spine.ElimId(sp, a, x, pp, h, y))
      case V1.Unfold(hh, sp, v) =>
        V1.Unfold(
          hh,
          Spine.ElimId(sp, a, x, pp, h, y),
          () => velimid(a, x, pp, h, y, v())
        )
      case _ => impossible()

  private def vfixix(ii: V1, a: V1, b: V1, f: V1, i: V1, x: V1): V1 =
    x match
      case V1.Rigid(h, sp) => V1.Rigid(h, Spine.FixIx(sp, ii, a, b, f, i))
      case V1.Flex(h, sp)  => V1.Flex(h, Spine.FixIx(sp, ii, a, b, f, i))
      case V1.Unfold(h, sp, v) =>
        V1.Unfold(
          h,
          Spine.FixIx(sp, ii, a, b, f, i),
          () => vfixix(ii, a, b, f, i, v())
        )
      // fixIx {I} {A} {B} f {i} v ~> f (\{j} y => fixIx {I} {A} {B} f {j} y) {i} v
      case v =>
        vappE(
          vappI(
            vappE(
              f,
              V1.lamI(
                "i",
                ii,
                j => V1.lam1("x", vappE(a, j), y => vfixix(ii, a, b, f, j, y))
              )
            ),
            i
          ),
          x
        )

  private def vcase(scrut: V1, cs: ClosCases1): V1 =
    scrut match
      case V1.Con1(_, _, cx, args) =>
        @tailrec
        def go(env: Env, cs: Cases1): V1 =
          cs match
            case Cases1.Ext(cx2, ps, b, r) if cx == cx2 =>
              // TODO: can we just drop the first few args?
              val nenv = env.exts1(args.drop(args.size - ps.size).map(_._1))
              eval1(b)(using nenv)
            case Cases1.Ext(_, _, _, r) => go(env, r)
            case Cases1.Otherwise(b)    => eval1(b)(using env)
            case Cases1.Empty           => impossible()
        go(cs.env, cs.cases)
      case V1.Rigid(h, sp) => V1.Rigid(h, Spine.Case(sp, cs))
      case V1.Flex(h, sp)  => V1.Flex(h, Spine.Case(sp, cs))
      case V1.Unfold(h, sp, v) =>
        V1.Unfold(h, Spine.Case(sp, cs), () => vcase(v(), cs))
      case _ => impossible()

  private def vspine(v: V1, sp: Spine): V1 = sp match
    case Spine.Empty         => v
    case Spine.App(sp, a, i) => vapp(vspine(v, sp), a, i)
    case Spine.Proj(sp, p)   => vproj(vspine(v, sp), p)
    case Spine.ElimId(sp, a, x, pp, h, y) =>
      velimid(a, x, pp, h, y, vspine(v, sp))
    case Spine.FixIx(sp, ii, a, b, f, i) =>
      vfixix(ii, a, b, f, i, vspine(v, sp))
    case Spine.Case(sp, cs)    => vcase(vspine(v, sp), cs)
    case Spine.MetaApp1(sp, a) => vmetaapp1(vspine(v, sp), a)
    case Spine.MetaApp0(sp, a) => vmetaapp0(vspine(v, sp), a)

  def vappPruning(v: V1, p: Pruning)(using env: Env): V1 =
    (env, p) match
      case (Env.Empty, Nil) => v
      case (Env.Ext1(env, _), PruneEntry.Skip :: p) =>
        vappPruning(v, p)(using env)
      case (Env.Ext0(env, _), PruneEntry.Skip :: p) =>
        vappPruning(v, p)(using env)
      case (Env.Ext1(env, u), PruneEntry.Keep1 :: p) =>
        vmetaapp1(vappPruning(v, p)(using env), u)
      case (Env.Ext0(env, u), PruneEntry.Keep0 :: p) =>
        vmetaapp0(vappPruning(v, p)(using env), u)
      case _ => impossible()

  def eval0(t: Tm0)(using env: Env): V0 =
    t match
      case Tm0.Var(ix)          => var0(ix)
      case Tm0.Global(m, x)     => V0.Global(m, x)
      case Tm0.IntLit(v)        => V0.IntLit(v)
      case Tm0.StringLit(v)     => V0.StringLit(v)
      case Tm0.Let(x, ty, v, b) => V0.Let(x, eval1(ty), eval0(v), Clos0(b))
      case Tm0.LetRec(x, ty, v, b) =>
        V0.LetRec(x, eval1(ty), Clos0(v), Clos0(b))
      case Tm0.Lam(x, ty, b)   => V0.Lam(x, eval1(ty), Clos0(b))
      case Tm0.App(f, a)       => V0.App(eval0(f), eval0(a))
      case Tm0.Splice(tm)      => vsplice(eval1(tm))
      case Tm0.If(ty, c, t, f) => V0.If(eval1(ty), eval0(c), eval0(t), eval0(f))
      case Tm0.Case(rty, dty, s, cs) =>
        V0.Case(eval1(rty), eval1(dty), eval0(s), ClosCases0(cs))
      case Tm0.RecordCon(ty, fs) => Val0.RecordCon(eval1(ty), fs.map(eval0))
      case Tm0.Proj(rty, s, p)   => V0.Proj(eval1(rty), eval0(s), p)
      case Tm0.Unsafe(rt, io, l, args) =>
        V0.Unsafe(eval1(rt), io, eval1(l), args.map(eval0))
      case Tm0.Wk1(t) => eval0(t)(using env.wk1)
      case Tm0.Wk0(t) => eval0(t)(using env.wk0)

  def eval1(t: Tm1)(using env: Env): V1 =
    t match
      case Tm1.Var(ix) => var1(ix)
      case Tm1.Global(m, x, v) =>
        V1.Unfold(UnfoldHead.Global(m, x, v), Spine.Empty, () => v)
      case Tm1.LabelLit(v)      => V1.LabelLit(v)
      case Tm1.TypeCon1(m, x)   => V1.TypeCon1(m, x)
      case Tm1.Con1(m, dx, cx)  => V1.Con1(m, dx, cx)
      case Tm1.TypeCon0(m, x)   => V1.TypeCon0(m, x)
      case Tm1.Con0(m, dx, cx)  => V1.Con0(m, dx, cx)
      case Tm1.Let(x, ty, v, b) => eval1(b)(using Env.Ext1(env, eval1(v)))
      case Tm1.Pi(x, i, ty, b)  => V1.Pi(x, i, eval1(ty), Clos1(b))
      case Tm1.Lam(x, i, ty, b) => V1.Lam(x, i, eval1(ty), Clos1(b))
      case Tm1.App(f, a, i)     => vapp(eval1(f), eval1(a), i)
      case Tm1.Fun(p, cv, r)    => V1.Fun(eval1(p), eval1(cv), eval1(r))
      case Tm1.Lift(cv, ty)     => V1.Lift(eval1(cv), eval1(ty))
      case Tm1.Quote(tm)        => vquote(eval0(tm))
      case Tm1.RecordTy1(fs)    => Val1.RecordTy1(ClosRec(fs))
      case Tm1.RecordTy0(cv, fs) =>
        Val1.RecordTy0(eval1(cv), fs.map((x, t) => (x, eval1(t))))
      case Tm1.RecordCon(fs)      => Val1.RecordCon(fs.map(eval1))
      case Tm1.Proj(tm, p)        => vproj(eval1(tm), p)
      case Tm1.Case(s, cs)        => vcase(eval1(s), ClosCases1(cs))
      case Tm1.Wk0(tm)            => eval1(tm)(using env.wk0)
      case Tm1.Wk1(tm)            => eval1(tm)(using env.wk1)
      case Tm1.Meta(id)           => vmeta(id)
      case Tm1.MetaPi1(t, b)      => V1.MetaPi1(eval1(t), Clos1(b))
      case Tm1.MetaPi0(t, b)      => V1.MetaPi0(eval1(t), Clos1(b))
      case Tm1.MetaLam1(b)        => V1.MetaLam1(Clos1(b))
      case Tm1.MetaLam0(b)        => V1.MetaLam0(Clos1(b))
      case Tm1.MetaApp1(f, a)     => vmetaapp1(eval1(f), eval1(a))
      case Tm1.MetaApp0(f, a)     => vmetaapp0(eval1(f), eval0(a))
      case Tm1.AppPruning(m, p)   => vappPruning(vmeta(m), p)
      case Tm1.PostponedCheck(id) => vcheck(id)

      case Tm1.Prim(Primitive.ElimId) =>
        V1.lamI(
          "A",
          V1.Meta,
          a =>
            V1.lamI(
              "x",
              a,
              x =>
                V1.lam1(
                  "P",
                  V1.piI("y", a, y => V1.fun1(V1.Id(a, a, x, y), V1.Meta)),
                  pp =>
                    V1.lam1(
                      "h",
                      vappE(vappI(pp, x), V1.Refl(a, x)),
                      h =>
                        V1.lamI(
                          "y",
                          a,
                          y =>
                            V1.lam1(
                              "p",
                              V1.Id(a, a, x, y),
                              p => velimid(a, x, pp, h, y, p)
                            )
                        )
                    )
                )
            )
        )
      case Tm1.Prim(Primitive.FixIx) =>
        V1.lamI(
          "I",
          V1.Meta,
          ii =>
            V1.lamI(
              "A",
              V1.fun1(ii, V1.Meta),
              a =>
                V1.lamI(
                  "B",
                  V1.pi("i", ii, i => V1.fun1(vappE(a, i), V1.Meta)),
                  b =>
                    V1.lam1(
                      "f",
                      V1.fun1(
                        V1.piI(
                          "i",
                          ii,
                          i =>
                            V1.pi("x", vappE(a, i), x => vappE(vappE(b, i), x))
                        ),
                        V1.piI(
                          "i",
                          ii,
                          i =>
                            V1.pi("x", vappE(a, i), x => vappE(vappE(b, i), x))
                        )
                      ),
                      f =>
                        V1.lamI(
                          "i",
                          ii,
                          i =>
                            V1.lam1(
                              "x",
                              vappE(a, i),
                              x => vfixix(ii, a, b, f, i, x)
                            )
                        )
                    )
                )
            )
        )
      case Tm1.Prim(p) => V1.Prim(p)

  // forcing
  def force1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_, _) => top
        case MetaEntry.Solved(v, _)   => vspine(v, sp)
    case v => v

  def forceAll1(v: V1): V1 = v match
    case top @ V1.Flex(id, sp) =>
      State.getMeta(id) match
        case MetaEntry.Unsolved(_, _) => top
        case MetaEntry.Solved(v, _)   => forceAll1(vspine(v, sp))
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
        case MetaEntry.Unsolved(_, _) => top
        case MetaEntry.Solved(v, _)   => forceMetas1(vspine(v, sp))
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
        case MetaEntry.Unsolved(_, _) => top
        case MetaEntry.Solved(v, _)   => forceUnstage1(vspine(v, sp))
    case V1.Unfold(_, _, v) => forceUnstage1(v())
    case v                  => v

  // readback
  enum UnfoldOption derives CanEqual:
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
    case Spine.Proj(sp, p)   => Tm1.Proj(readbackSpine(h, sp), p)
    case Spine.MetaApp1(sp, v) =>
      Tm1.MetaApp1(readbackSpine(h, sp), readback1(v))
    case Spine.MetaApp0(sp, v) =>
      Tm1.MetaApp0(readbackSpine(h, sp), readback0(v))
    case Spine.Case(sp, cs) =>
      def go(env: Env, cs: Cases1): Cases1 =
        cs match
          case Cases1.Ext(x, ps, b, r) =>
            val (innerlvl, innerenv, nps) = addParams(ps)(using lvl, env)
            val rb = readback1(eval1(b)(using innerenv))(using innerlvl)
            Cases1.Ext(x, nps, rb, go(env, r))
          case Cases1.Otherwise(b) =>
            Cases1.Otherwise(readback1(eval1(b)(using env)))
          case Cases1.Empty => Cases1.Empty
      Tm1.Case(readbackSpine(h, sp), go(cs.env, cs.cases))
    case Spine.ElimId(sp, a, x, pp, hh, y) =>
      Tm1.ElimId(
        readback1(a),
        readback1(x),
        readback1(pp),
        readback1(hh),
        readback1(y),
        readbackSpine(h, sp)
      )
    case Spine.FixIx(sp, ii, a, b, f, i) =>
      Tm1.FixIx(
        readback1(ii),
        readback1(a),
        readback1(b),
        readback1(f),
        readback1(i),
        readbackSpine(h, sp)
      )

  def readback1(v: V1)(using lvl: Lvl, unfoldOption: UnfoldOption): Tm1 =
    inline def go0(v: V0): Tm0 = readback0(v)
    inline def go1(v: V1): Tm1 = readback1(v)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = readbackSpine(h, sp)
    inline def goClos(c: Clos1): Tm1 =
      readback1(c(V1.Var(lvl)))(using lvl + 1)
    inline def goClos0(c: Clos1): Tm1 =
      readback1(c(V0.Var(lvl)))(using lvl + 1)
    inline def force(v: V1): V1 = unfoldOption match
      case UnfoldOption.All     => forceAll1(v)
      case UnfoldOption.Metas   => forceMetas1(v)
      case UnfoldOption.None    => force1(v)
      case UnfoldOption.Unstage => forceUnstage1(v)
    def goRec(c: ClosRec): AssocBind[Ty] =
      def go(env: Env, lvl: Lvl, fs: AssocBind[Ty]): AssocBind[Ty] =
        fs match
          case Nil => Nil
          case (x, ty) :: rest =>
            val qty = readback1(eval1(ty)(using env))(using lvl)
            (x, qty) :: go(Env.Ext1(env, V1.Var(lvl)), lvl + 1, rest)
      go(c.env, lvl, c.fields)
    force(v) match
      case V1.Rigid(hd, sp) =>
        hd match
          case Head.Var(lvl)        => goSp(Tm1.Var(lvl.toIx), sp)
          case Head.Prim(p)         => goSp(Tm1.Prim(p), sp)
          case Head.TypeCon1(m, x)  => goSp(Tm1.TypeCon1(m, x), sp)
          case Head.Con1(m, dx, cx) => goSp(Tm1.Con1(m, dx, cx), sp)
          case Head.TypeCon0(m, x)  => goSp(Tm1.TypeCon0(m, x), sp)
          case Head.Con0(m, dx, cx) => goSp(Tm1.Con0(m, dx, cx), sp)
      case V1.LabelLit(v)  => Tm1.LabelLit(v)
      case V1.Flex(id, sp) => goSp(Tm1.Meta(id), sp)
      case V1.Unfold(UnfoldHead.Global(m, x, v), sp, _) =>
        goSp(Tm1.Global(m, x, v), sp)
      case V1.Pi(x, i, ty, b)   => Tm1.Pi(x, i, go1(ty), goClos(b))
      case V1.Lam(x, i, ty, b)  => Tm1.Lam(x, i, go1(ty), goClos(b))
      case V1.Fun(pty, cv, rty) => Tm1.Fun(go1(pty), go1(cv), go1(rty))
      case V1.Lift(cv, ty)      => Tm1.Lift(go1(cv), go1(ty))
      case V1.Quote(tm)         => go0(tm).quote
      case V1.RecordTy1(fs)     => Tm1.RecordTy1(goRec(fs))
      case V1.RecordTy0(cv, fs) =>
        Tm1.RecordTy0(go1(cv), fs.map((x, t) => (x, go1(t))))
      case V1.RecordCon(fs) => Tm1.RecordCon(fs.map(t => go1(t)))
      case V1.MetaPi1(t, b) => Tm1.MetaPi1(go1(t), goClos(b))
      case V1.MetaPi0(t, b) => Tm1.MetaPi0(go1(t), goClos0(b))
      case V1.MetaLam1(b)   => Tm1.MetaLam1(goClos(b))
      case V1.MetaLam0(b)   => Tm1.MetaLam0(goClos0(b))

  def readback0(v: V0)(using lvl: Lvl, unfoldOption: UnfoldOption): Tm0 =
    inline def go0(v: V0): Tm0 = readback0(v)
    inline def go1(v: V1): Tm1 = readback1(v)
    inline def goClos(c: Clos0): Tm0 =
      readback0(c(V0.Var(lvl)))(using lvl + 1)
    inline def force(v: V0): V0 = unfoldOption match
      case UnfoldOption.All     => forceAll0(v)
      case UnfoldOption.Metas   => forceMetas0(v)
      case UnfoldOption.None    => v
      case UnfoldOption.Unstage => forceUnstage0(v)
    force(v) match
      case V0.Var(x)           => Tm0.Var(x.toIx)
      case V0.Global(m, x)     => Tm0.Global(m, x)
      case V0.IntLit(v)        => Tm0.IntLit(v)
      case V0.StringLit(v)     => Tm0.StringLit(v)
      case V0.Let(x, ty, v, b) => Tm0.Let(x, go1(ty), go0(v), goClos(b))
      case V0.LetRec(x, ty, v, b) =>
        Tm0.LetRec(x, go1(ty), goClos(v), goClos(b))
      case V0.Lam(x, ty, b)     => Tm0.Lam(x, go1(ty), goClos(b))
      case V0.App(f, a)         => Tm0.App(go0(f), go0(a))
      case V0.If(ty, c, t, f)   => Tm0.If(go1(ty), go0(c), go0(t), go0(f))
      case V0.Splice(tm)        => go1(tm).splice
      case V0.Proj(rty, s, p)   => Tm0.Proj(go1(rty), go0(s), p)
      case V0.RecordCon(ty, fs) => Tm0.RecordCon(go1(ty), fs.map(t => go0(t)))
      case V0.Unsafe(rt, io, l, args) =>
        Tm0.Unsafe(go1(rt), io, go1(l), args.map(go0))
      case V0.Case(rty, dty, s, cs) =>
        def goCases(cs: Cases0)(using env: Env): Cases0 =
          cs match
            case Cases0.Empty        => Cases0.Empty
            case Cases0.Otherwise(b) => Cases0.Otherwise(go0(eval0(b)))
            case Cases0.Ext(x, ps, b, r) =>
              val (innerlvl, innerenv) = addParams(ps.size)
              val nps = ps.map((x, ty) => (x, go1(eval1(ty))))
              val rb = readback0(eval0(b)(using innerenv))(using innerlvl)
              Cases0.Ext(x, nps, rb, goCases(r))
        Tm0.Case(
          go1(rty),
          go1(dty),
          go0(s),
          goCases(cs.cases)(using cs.env)
        )

  def addParams(n: Int)(using lvl: Lvl, env: Env): (Lvl, Env) =
    @tailrec
    def go(n: Int, lvl: Lvl, env: Env): (Lvl, Env) =
      n match
        case 0 => (lvl, env)
        case n => go(n - 1, lvl + 1, Env.Ext0(env, V0.Var(lvl)))
    go(n, lvl, env)

  def addParams(ps: List[(Bind, Icit, Ty)])(using
      lvl: Lvl,
      env: Env,
      unfoldOption: UnfoldOption
  ): (Lvl, Env, List[(Bind, Icit, Ty)]) =
    ps match
      case Nil => (lvl, env, Nil)
      case (x, i, ty) :: rest =>
        val ety = readback1(eval1(ty))
        val (nlvl, nenv, nps) =
          addParams(rest)(using lvl + 1, Env.Ext1(env, V1.Var(lvl)))
        (nlvl, nenv, (x, i, ety) :: nps)

  // helpers
  inline def readback1m(v: V1)(using lvl: Lvl): Tm1 =
    readback1(v)(using unfoldOption = UnfoldOption.Metas)
  inline def readback0m(v: V0)(using lvl: Lvl): Tm0 =
    readback0(v)(using unfoldOption = UnfoldOption.Metas)
  inline def readback1n(v: V1)(using lvl: Lvl): Tm1 =
    readback1(v)(using unfoldOption = UnfoldOption.None)
  inline def readback0n(v: V0)(using lvl: Lvl): Tm0 =
    readback0(v)(using unfoldOption = UnfoldOption.None)

  inline def unstage(tm: Tm0): Tm0 =
    readback0(eval0(tm)(using Env.Empty))(using lvl0, UnfoldOption.Unstage)
  inline def unstageUnder(tm: Tm0, env: Env): Tm0 =
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
        case Spine.Empty         => ()
        case Spine.App(sp, a, _) => go1(a); goSp(sp)
        case Spine.Proj(sp, _)   => goSp(sp)
        case Spine.ElimId(sp, a, x, pp, h, y) =>
          go1(a); go1(x); go1(pp); go1(h); go1(y); goSp(sp)
        case Spine.FixIx(sp, ii, a, b, f, i) =>
          go1(ii); go1(a); go1(b); go1(f); go1(i); goSp(sp)
        case Spine.MetaApp1(sp, a) => go1(a); goSp(sp)
        case Spine.MetaApp0(sp, a) => go0(a); goSp(sp)
        case Spine.Case(sp, cs) =>
          @tailrec
          def goCases(cs: Cases1)(using env: Env): Unit =
            cs match
              case Cases1.Empty        => ()
              case Cases1.Otherwise(b) => go1(eval1(b))
              case Cases1.Ext(x, ps, b, r) =>
                @tailrec
                def goParams(
                    ps: List[(Bind, Icit, Ty)]
                )(using lvl: Lvl, env: Env): (Lvl, Env) =
                  ps match
                    case Nil => (lvl, env)
                    case (x, i, ty) :: rest =>
                      go1(eval1(ty))
                      goParams(rest)(using lvl + 1, Env.Ext1(env, V1.Var(lvl)))
                val (innerlvl, innerenv) = goParams(ps)
                go1(eval1(b)(using innerenv))(using innerlvl)
                goCases(r)
          goCases(cs.cases)(using cs.env)
          goSp(sp)
    def goHead(h: Head): Unit =
      h match
        case Head.Var(_)          => ()
        case Head.Prim(_)         => ()
        case Head.TypeCon1(m, x)  => set += ((m, x))
        case Head.Con1(m, dx, cx) => set += ((m, dx)); set += ((m, cx))
        case Head.TypeCon0(m, x)  => set += ((m, x))
        case Head.Con0(m, dx, cx) => set += ((m, dx)); set += ((m, cx))
    def goUnfoldHead(h: UnfoldHead)(using lvl: Lvl): Unit =
      h match
        case UnfoldHead.Global(m, x, v) => set += ((m, x)); go1(v)
    def goRec(c: ClosRec)(using lvl: Lvl): Unit =
      @tailrec
      def go(env: Env, lvl: Lvl, fs: AssocBind[Ty]): Unit =
        fs match
          case Nil => ()
          case (x, ty) :: rest =>
            val qty = go1(eval1(ty)(using env))(using lvl)
            go(Env.Ext1(env, V1.Var(lvl)), lvl + 1, rest)
      go(c.env, lvl, c.fields)
    def go1(v: V1)(using lvl: Lvl): Unit =
      v match
        case V1.Rigid(h, sp)      => goHead(h); goSp(sp)
        case V1.LabelLit(_)       => ()
        case V1.Unfold(h, sp, _)  => goUnfoldHead(h); goSp(sp)
        case V1.Pi(_, _, ty, b)   => go1(ty); goClos1(b)
        case V1.Lam(_, _, ty, b)  => go1(ty); goClos1(b)
        case V1.Fun(pty, cv, rty) => go1(pty); go1(cv); go1(rty)
        case V1.Lift(cv, ty)      => go1(cv); go1(ty)
        case V1.Quote(tm)         => go0(tm)
        case V1.RecordTy1(fs)     => goRec(fs)
        case V1.RecordTy0(cv, fs) => go1(cv); fs.foreach((_, t) => go1(t))
        case V1.RecordCon(fs)     => fs.foreach(t => go1(t))
        case V1.MetaPi1(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaPi0(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaLam1(b)       => goClos1(b)
        case V1.MetaLam0(b)       => goClos1(b)
        case V1.Flex(m, sp) =>
          State.getMeta(m) match
            case MetaEntry.Unsolved(_, _) => goSp(sp)
            case MetaEntry.Solved(v, _)   => go1(vspine(v, sp))
    def go0(v: V0)(using lvl: Lvl): Unit =
      v match
        case V0.Global(m, x)        => set += ((m, x))
        case V0.Var(_)              => ()
        case V0.IntLit(_)           => ()
        case V0.StringLit(_)        => ()
        case V0.Let(_, ty, v, b)    => go1(ty); go0(v); goClos0(b)
        case V0.LetRec(_, ty, v, b) => go1(ty); goClos0(v); goClos0(b)
        case V0.Lam(_, ty, b)       => go1(ty); goClos0(b)
        case V0.App(f, a)           => go0(f); go0(a)
        case V0.If(rty, c, t, f)    => go1(rty); go0(c); go0(t); go0(f)
        case V0.Splice(tm)          => go1(tm)
        case V0.Proj(rty, s, _)     => go1(rty); go0(s)
        case V0.RecordCon(ty, fs)   => go1(ty); fs.foreach(t => go0(t))
        case V0.Unsafe(rt, io, l, args) =>
          go1(rt); go1(l); args.foreach(t => go0(t))
        case V0.Case(rty, dty, s, cs) =>
          @tailrec
          def goCases(cs: Cases0)(using env: Env): Unit =
            cs match
              case Cases0.Empty        => ()
              case Cases0.Otherwise(b) => go0(eval0(b))
              case Cases0.Ext(x, ps, b, r) =>
                val (innerlvl, innerenv) = addParams(ps.size)
                val nps = ps.foreach((_, ty) => go1(eval1(ty)))
                val rb = go0(eval0(b)(using innerenv))(using innerlvl)
                goCases(r)
          go1(rty); go1(dty); go0(s)
          goCases(cs.cases)(using cs.env)
    go1(v)(using lvl0)
    set.toSet

  def allLocals(v: V1): Set[Lvl] =
    val set = mutable.Set.empty[Lvl]
    inline def goClos1(c: Clos1)(using lvl: Lvl): Unit =
      go1(c(V1.Var(lvl)))(using lvl + 1)
    inline def goClos0(c: Clos0)(using lvl: Lvl): Unit =
      go0(c(V0.Var(lvl)))(using lvl + 1)
    @tailrec
    def goSp(sp: Spine)(using lvl: Lvl): Unit =
      sp match
        case Spine.Empty         => ()
        case Spine.App(sp, a, _) => go1(a); goSp(sp)
        case Spine.Proj(sp, _)   => goSp(sp)
        case Spine.ElimId(sp, a, x, pp, h, y) =>
          go1(a); go1(x); go1(pp); go1(h); go1(y); goSp(sp)
        case Spine.FixIx(sp, ii, a, b, f, i) =>
          go1(ii); go1(a); go1(b); go1(f); go1(i); goSp(sp)
        case Spine.MetaApp1(sp, a) => go1(a); goSp(sp)
        case Spine.MetaApp0(sp, a) => go0(a); goSp(sp)
        case Spine.Case(sp, cs) =>
          @tailrec
          def goCases(cs: Cases1)(using env: Env): Unit =
            cs match
              case Cases1.Empty        => ()
              case Cases1.Otherwise(b) => go1(eval1(b))
              case Cases1.Ext(x, ps, b, r) =>
                @tailrec
                def goParams(
                    ps: List[(Bind, Icit, Ty)]
                )(using lvl: Lvl, env: Env): (Lvl, Env) =
                  ps match
                    case Nil => (lvl, env)
                    case (x, i, ty) :: rest =>
                      go1(eval1(ty))
                      goParams(rest)(using lvl + 1, Env.Ext1(env, V1.Var(lvl)))
                val (innerlvl, innerenv) = goParams(ps)
                go1(eval1(b)(using innerenv))(using innerlvl)
                goCases(r)
          goCases(cs.cases)(using cs.env)
          goSp(sp)
    def goHead(h: Head): Unit =
      h match
        case Head.Var(x)          => set += x
        case Head.Prim(_)         => ()
        case Head.TypeCon1(m, x)  => ()
        case Head.Con1(m, dx, cx) => ()
        case Head.TypeCon0(m, x)  => ()
        case Head.Con0(m, dx, cx) => ()
    def goUnfoldHead(h: UnfoldHead)(using lvl: Lvl): Unit =
      h match
        case UnfoldHead.Global(m, x, v) => go1(v)
    def goRec(c: ClosRec)(using lvl: Lvl): Unit =
      @tailrec
      def go(env: Env, lvl: Lvl, fs: AssocBind[Ty]): Unit =
        fs match
          case Nil => ()
          case (x, ty) :: rest =>
            val qty = go1(eval1(ty)(using env))(using lvl)
            go(Env.Ext1(env, V1.Var(lvl)), lvl + 1, rest)
      go(c.env, lvl, c.fields)
    def go1(v: V1)(using lvl: Lvl): Unit =
      v match
        case V1.Rigid(h, sp)      => goHead(h); goSp(sp)
        case V1.LabelLit(_)       => ()
        case V1.Unfold(h, sp, _)  => goUnfoldHead(h); goSp(sp)
        case V1.Pi(_, _, ty, b)   => go1(ty); goClos1(b)
        case V1.Lam(_, _, ty, b)  => go1(ty); goClos1(b)
        case V1.Fun(pty, cv, rty) => go1(pty); go1(cv); go1(rty)
        case V1.Lift(cv, ty)      => go1(cv); go1(ty)
        case V1.Quote(tm)         => go0(tm)
        case V1.RecordTy1(fs)     => goRec(fs)
        case V1.RecordTy0(cv, fs) => go1(cv); fs.foreach((_, t) => go1(t))
        case V1.RecordCon(fs)     => fs.foreach(t => go1(t))
        case V1.MetaPi1(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaPi0(ty, b)    => go1(ty); goClos1(b)
        case V1.MetaLam1(b)       => goClos1(b)
        case V1.MetaLam0(b)       => goClos1(b)
        case V1.Flex(m, sp) =>
          State.getMeta(m) match
            case MetaEntry.Unsolved(_, _) => goSp(sp)
            case MetaEntry.Solved(v, _)   => go1(vspine(v, sp))
    def go0(v: V0)(using lvl: Lvl): Unit =
      v match
        case V0.Var(x)              => set += x
        case V0.Global(m, x)        => ()
        case V0.IntLit(_)           => ()
        case V0.StringLit(_)        => ()
        case V0.Let(_, ty, v, b)    => go1(ty); go0(v); goClos0(b)
        case V0.LetRec(_, ty, v, b) => go1(ty); goClos0(v); goClos0(b)
        case V0.Lam(_, ty, b)       => go1(ty); goClos0(b)
        case V0.App(f, a)           => go0(f); go0(a)
        case V0.If(rty, c, t, f)    => go1(rty); go0(c); go0(t); go0(f)
        case V0.Splice(tm)          => go1(tm)
        case V0.Proj(rty, s, _)     => go1(rty); go0(s)
        case V0.RecordCon(ty, fs)   => go1(ty); fs.foreach(t => go0(t))
        case V0.Unsafe(rt, io, l, args) =>
          go1(rt); go1(l); args.foreach(t => go0(t))
        case V0.Case(rty, dty, s, cs) =>
          @tailrec
          def goCases(cs: Cases0)(using env: Env): Unit =
            cs match
              case Cases0.Empty        => ()
              case Cases0.Otherwise(b) => go0(eval0(b))
              case Cases0.Ext(x, ps, b, r) =>
                val (innerlvl, innerenv) = addParams(ps.size)
                val nps = ps.foreach((_, ty) => go1(eval1(ty)))
                val rb = go0(eval0(b)(using innerenv))(using innerlvl)
                goCases(r)
          go1(rty); go1(dty); go0(s)
          goCases(cs.cases)(using cs.env)
    go1(v)(using lvl0)
    set.toSet
