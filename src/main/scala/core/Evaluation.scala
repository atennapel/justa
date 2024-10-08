package core

import common.Common.*
import Syntax.*
import Value.*
import State.*
import State.MetaEntry.*
import State.GlobalEntry.*

import scala.annotation.tailrec

object Evaluation:
  enum QuoteOption:
    case UnfoldAll
    case UnfoldMetas
    case UnfoldNone
    case UnfoldStage

final class Evaluation(val state: State):
  import Evaluation.QuoteOption
  import Evaluation.QuoteOption.*
  import state.*

  // closures
  extension (c: Clos0)
    inline def apply(v: Val0): Val0 = c match
      case CClos0(env, tm) => eval0(tm)(E0(env, v))
      case CFun0(f)        => f(v)
  extension (c: Clos1)
    inline def apply(v: Val1): Val1 = c match
      case CClos1(env, tm) => eval1(tm)(E1(env, v))
      case CFun1(f)        => f(v)
    inline def apply(v: Val0): Val1 = c match
      case CClos1(env, tm) => eval1(tm)(E0(env, v))
      case CFun1(_)        => impossible()

  // evaluation
  @tailrec
  def vvar0(ix: Ix)(implicit e: Env): Val0 =
    e match
      case E0(_, v) if ix.expose == 0 => v
      case E0(env, _)                 => vvar0(ix - 1)(env)
      case E1(env, _)                 => vvar0(ix - 1)(env)
      case EEmpty                     => impossible()

  @tailrec
  def vvar1(ix: Ix)(implicit e: Env): Val1 =
    e match
      case E1(_, v) if ix.expose == 0 => v
      case E0(env, _)                 => vvar1(ix - 1)(env)
      case E1(env, _)                 => vvar1(ix - 1)(env)
      case EEmpty                     => impossible()

  def vglobal1(x: Name): Val1 =
    state.getGlobal(x) match
      case Some(GlobalEntry1(_, _, _, v, _)) =>
        VUnfold(UGlobal(x), SId, () => v)
      case Some(GlobalEntryNative(_, _, _)) => VNative(x)
      case _                                => impossible()

  inline def vmeta(id: MetaId): Val1 = getMeta(id) match
    case Unsolved(_)      => VFlex(id, SId)
    case Solved(value, _) => VUnfold(UMeta(id), SId, () => value)

  inline def vsplice(v: Val1): Val0 = v match
    case VQuote(v) => v
    case v         => VSplice(v)

  inline def vquote(v: Val0): Val1 = v match
    case VSplice(v) => v
    case v          => VQuote(v)

  def vapp1(f: Val1, a: Val1, i: Icit): Val1 = f match
    case VLam1(x, _, _, b) => b(a)
    case VFlex(id, sp)     => VFlex(id, SApp(sp, a, i))
    case VRigid(h, sp)     => VRigid(h, SApp(sp, a, i))
    case VUnfold(h, sp, v) => VUnfold(h, SApp(sp, a, i), () => vapp1(v(), a, i))
    case _                 => impossible()
  inline def vappE(f: Val1, a: Val1): Val1 = vapp1(f, a, Expl)
  inline def vappI(f: Val1, a: Val1): Val1 = vapp1(f, a, Impl)

  def vmetaapp1(f: Val1, a: Val1): Val1 = f match
    case VMetaLam1(b)  => b(a)
    case VFlex(id, sp) => VFlex(id, SMetaApp1(sp, a))
    case VUnfold(h, sp, v) =>
      VUnfold(h, SMetaApp1(sp, a), () => vmetaapp1(v(), a))
    case _ => impossible()

  def vmetaapp0(f: Val1, a: Val0): Val1 = f match
    case VMetaLam0(b)  => b(a)
    case VFlex(id, sp) => VFlex(id, SMetaApp0(sp, a))
    case VUnfold(h, sp, v) =>
      VUnfold(h, SMetaApp0(sp, a), () => vmetaapp0(v(), a))
    case _ => impossible()

  def vspine(v: Val1, sp: Spine): Val1 = sp match
    case SId              => v
    case SApp(sp, a, i)   => vapp1(vspine(v, sp), a, i)
    case SMetaApp1(sp, a) => vmetaapp1(vspine(v, sp), a)
    case SMetaApp0(sp, a) => vmetaapp0(vspine(v, sp), a)

  def vappPruning(v: Val1, p: Pruning)(implicit env: Env): Val1 =
    (env, p) match
      case (EEmpty, Nil)                 => v
      case (E1(env, _), PESkip :: p)     => vappPruning(v, p)(env)
      case (E0(env, _), PESkip :: p)     => vappPruning(v, p)(env)
      case (E1(env, u), PEBind1(i) :: p) => vmetaapp1(vappPruning(v, p)(env), u)
      case (E0(env, u), PEBind0 :: p)    => vmetaapp0(vappPruning(v, p)(env), u)
      case _                             => impossible()

  def eval0(t: Tm0)(implicit env: Env): Val0 =
    t match
      case Var0(ix)   => vvar0(ix)
      case Global0(x) => VGlobal0(x)
      case Let0(x, ty, v, b) =>
        VLet0(x, eval1(ty), eval0(v), Clos0(b))
      case LetRec(x, ty, v, b) =>
        VLetRec(x, eval1(ty), Clos0(v), Clos0(b))
      case Lam0(x, ty, b) => VLam0(x, eval1(ty), Clos0(b))
      case App0(f, a)     => VApp0(eval0(f), eval0(a))
      case Splice(t)      => vsplice(eval1(t))
      case Wk10(t)        => eval0(t)(env.wk1)
      case Wk00(t)        => eval0(t)(env.wk0)

  def eval1(t: Tm1)(implicit env: Env): Val1 =
    t match
      case Var1(ix)          => vvar1(ix)
      case Global1(x)        => vglobal1(x)
      case Native(x)         => VNative(x)
      case Let1(_, _, v, b)  => eval1(b)(E1(env, eval1(v)))
      case U0(cv)            => VU0(eval1(cv))
      case U1                => VU1
      case CV                => VCV
      case CVV               => VCVV
      case CVC               => VCVC
      case Pi(x, i, ty, b)   => VPi(x, i, eval1(ty), Clos1(b))
      case Lam1(x, i, ty, b) => VLam1(x, i, eval1(ty), Clos1(b))
      case App1(f, a, i)     => vapp1(eval1(f), eval1(a), i)
      case Fun(p, cv, r)     => VFun(eval1(p), eval1(cv), eval1(r))
      case Lift(cv, ty)      => VLift(eval1(cv), eval1(ty))
      case Quote(tm)         => vquote(eval0(tm))
      case AppPruning(m, p)  => vappPruning(vmeta(m), p)
      case Wk01(tm)          => eval1(tm)(env.wk0)
      case Wk11(tm)          => eval1(tm)(env.wk1)
      case Meta(id)          => vmeta(id)
      case MetaPi1(t, b)     => VMetaPi1(eval1(t), Clos1(b))
      case MetaPi0(t, b)     => VMetaPi0(eval1(t), Clos1(b))
      case MetaLam1(b)       => VMetaLam1(Clos1(b))
      case MetaLam0(b)       => VMetaLam0(Clos1(b))
      case MetaApp1(f, a)    => vmetaapp1(eval1(f), eval1(a))
      case MetaApp0(f, a)    => vmetaapp0(eval1(f), eval0(a))

  // forcing
  def force1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => VUnfold(UMeta(id), sp, () => vspine(v, sp))
    case v => v

  def forceAll1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => forceAll1(vspine(v, sp))
    case VUnfold(_, _, v) => forceAll1(v())
    case v                => v

  @tailrec
  def forceAll0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceAll1(v) match
        case VQuote(v) => forceAll0(v)
        case _         => top
    case v => v

  def forceMetas1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => forceMetas1(vspine(v, sp))
    case VUnfold(UMeta(_), _, v) => forceMetas1(v())
    case v                       => v

  @tailrec
  def forceMetas0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceMetas1(v) match
        case VQuote(v) => forceMetas0(v)
        case _         => top
    case v => v

  @tailrec
  def forceStage0(v: Val0): Val0 = v match
    case top @ VSplice(v) =>
      forceAll1(v) match
        case VQuote(v) => forceStage0(v)
        case _         => top
    case v => v

  def forceStage1(v: Val1): Val1 = v match
    case top @ VFlex(id, sp) =>
      getMeta(id) match
        case Unsolved(_)  => top
        case Solved(v, _) => forceStage1(vspine(v, sp))
    case VUnfold(_, _, v) => forceStage1(v())
    case v                => v

  // quoting
  private def quote1(h: Tm1, sp: Spine, q: QuoteOption)(implicit
      lvl: Lvl
  ): Tm1 = sp match
    case SId            => h
    case SApp(sp, v, i) => App1(quote1(h, sp, q), quote1(v, q), i)
    case SMetaApp1(sp, v) =>
      MetaApp1(quote1(h, sp, q), quote1(v, q))
    case SMetaApp0(sp, v) =>
      MetaApp0(quote1(h, sp, q), quote0(v, q))

  def quote1(v: Val1, q: QuoteOption)(implicit lvl: Lvl): Tm1 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goSp(h: Tm1, sp: Spine): Tm1 = quote1(h, sp, q)
    inline def goClos(c: Clos1): Tm1 = quote1(c(VVar1(lvl)), q)(lvl + 1)
    inline def goClos0(c: Clos1): Tm1 = quote1(c(VVar0(lvl)), q)(lvl + 1)
    inline def force(v: Val1): Val1 = q match
      case UnfoldAll   => forceAll1(v)
      case UnfoldMetas => forceMetas1(v)
      case UnfoldNone  => force1(v)
      case UnfoldStage => forceStage1(v)
    force(v) match
      case VRigid(hd, sp) =>
        hd match
          case HVar(lvl)  => goSp(Var1(lvl.toIx), sp)
          case HNative(x) => goSp(Native(x), sp)
      case VFlex(id, sp)              => goSp(Meta(id), sp)
      case VUnfold(UMeta(id), sp, _)  => goSp(Meta(id), sp)
      case VUnfold(UGlobal(x), sp, _) => goSp(Global1(x), sp)
      case VPi(x, i, ty, b)           => Pi(x, i, go1(ty), goClos(b))
      case VLam1(x, i, ty, b)         => Lam1(x, i, go1(ty), goClos(b))
      case VU0(cv)                    => U0(go1(cv))
      case VU1                        => U1
      case VCV                        => CV
      case VCVV                       => CVV
      case VCVC                       => CVC
      case VFun(pty, cv, rty)         => Fun(go1(pty), go1(cv), go1(rty))
      case VLift(cv, ty)              => Lift(go1(cv), go1(ty))
      case VQuote(tm)                 => quote(go0(tm))
      case VMetaPi1(t, b)             => MetaPi1(go1(t), goClos(b))
      case VMetaPi0(t, b)             => MetaPi0(go1(t), goClos0(b))
      case VMetaLam1(b)               => MetaLam1(goClos(b))
      case VMetaLam0(b)               => MetaLam0(goClos0(b))

  def quote0(v: Val0, q: QuoteOption)(implicit lvl: Lvl): Tm0 =
    inline def go0(v: Val0): Tm0 = quote0(v, q)
    inline def go1(v: Val1): Tm1 = quote1(v, q)
    inline def goClos(c: Clos0): Tm0 = quote0(c(VVar0(lvl)), q)(lvl + 1)
    inline def force(v: Val0): Val0 = q match
      case UnfoldAll   => forceAll0(v)
      case UnfoldMetas => forceMetas0(v)
      case UnfoldNone  => v
      case UnfoldStage => forceStage0(v)
    force(v) match
      case VVar0(x)    => Var0(x.toIx)
      case VGlobal0(x) => Global0(x)
      case VLet0(x, ty, v, b) =>
        Let0(x, go1(ty), go0(v), goClos(b))
      case VLetRec(x, ty, v, b) =>
        LetRec(x, go1(ty), goClos(v), goClos(b))
      case VLam0(x, ty, b) => Lam0(x, go1(ty), goClos(b))
      case VApp0(f, a)     => App0(go0(f), go0(a))
      case VSplice(tm)     => splice(go1(tm))

  def nf(tm: Tm1, q: QuoteOption = UnfoldAll): Tm1 =
    quote1(eval1(tm)(EEmpty), q)(lvl0)
  def stage(tm: Tm0): Tm0 = quote0(eval0(tm)(EEmpty), UnfoldStage)(lvl0)
  def stageUnder(tm: Tm0, env: Env): Tm0 =
    quote0(eval0(tm)(env), UnfoldStage)(mkLvl(env.size))
