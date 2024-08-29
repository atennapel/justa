package core

package core

import common.Common.*
import Syntax as S

import scala.annotation.tailrec

object Value:
  enum Clos0:
    case CClos0(env: Env, tm: S.Tm0)
    case CFun0(fn: Val0 => Val0)
  export Clos0.*
  object Clos0:
    def apply(tm: S.Tm0)(implicit env: Env): Clos0 = CClos0(env, tm)

  enum Clos1:
    case CClos1(env: Env, tm: S.Tm1)
    case CFun1(fn: Val1 => Val1)
  export Clos1.*
  object Clos1:
    def apply(tm: S.Tm1)(implicit env: Env): Clos1 = CClos1(env, tm)

  enum Env:
    case EEmpty
    case E1(env: Env, value: Val1)
    case E0(env: Env, value: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, e: Env): Int = e match
        case EEmpty   => acc
        case E1(e, _) => go(acc + 1, e)
        case E0(e, _) => go(acc + 1, e)
      go(0, this)

    inline def wk1: Env = this match
      case E1(env, _) => env
      case _          => impossible()

    inline def wk0: Env = this match
      case E0(env, _) => env
      case _          => impossible()

    inline def tail: Env = this match
      case E0(env, _) => env
      case E1(env, _) => env
      case _          => impossible()
  export Env.*
  object Env:
    def apply(vs: List[Val1]): Env = vs.foldLeft(EEmpty)(E1.apply)

  type VTy = Val1
  type VCV = VTy

  enum Spine:
    case SId
    case SApp(sp: Spine, arg: Val1, icit: Icit)
    case SMetaApp1(sp: Spine, arg: Val1)
    case SMetaApp0(sp: Spine, arg: Val0)

    def size: Int =
      @tailrec
      def go(acc: Int, sp: Spine): Int = sp match
        case SId              => acc
        case SApp(sp, _, _)   => go(acc + 1, sp)
        case SMetaApp1(sp, _) => go(acc + 1, sp)
        case SMetaApp0(sp, _) => go(acc + 1, sp)
      go(0, this)

    def reverse: Spine =
      @tailrec
      def go(acc: Spine, sp: Spine): Spine = sp match
        case SId              => acc
        case SApp(sp, v, i)   => go(SApp(acc, v, i), sp)
        case SMetaApp1(sp, v) => go(SMetaApp1(acc, v), sp)
        case SMetaApp0(sp, v) => go(SMetaApp0(acc, v), sp)
      go(SId, this)

    def isEmpty: Boolean = this match
      case SId => true
      case _   => false
  export Spine.*

  enum Val0:
    case VVar0(lvl: Lvl)
    case VGlobal0(name: Name)
    case VLet0(
        name: Name,
        ty: VTy,
        value: Val0,
        body: Clos0
    )
    case VLetRec(
        name: Name,
        ty: VTy,
        value: Clos0,
        body: Clos0
    )
    case VLam0(name: Bind, ty: VTy, body: Clos0)
    case VApp0(fn: Val0, arg: Val0)
    case VSplice(tm: Val1)
  export Val0.*

  enum Head:
    case HVar(lvl: Lvl)
  export Head.*

  enum UHead:
    case UMeta(id: MetaId)
    case UGlobal(name: Name)
  export UHead.*

  enum Val1:
    case VRigid(head: Head, spine: Spine)
    case VFlex(id: MetaId, spine: Spine)
    case VUnfold(head: UHead, spine: Spine, value: () => Val1)

    case VPi(name: Bind, icit: Icit, ty: VTy, body: Clos1)
    case VLam1(name: Bind, icit: Icit, ty: VTy, body: Clos1)

    case VMetaPi1(ty: VTy, body: Clos1)
    case VMetaLam1(body: Clos1)
    case VMetaPi0(ty: VTy, body: Clos1)
    case VMetaLam0(body: Clos1)

    case VU0(cv: VTy)
    case VU1

    case VCV
    case VCVV
    case VCVC

    case VFun(pty: VTy, cv: VTy, rty: VTy)
    case VLift(cv: VTy, ty: VTy)

    case VQuote(tm: Val0)
  export Val1.*

  private inline def bind(x: String): Bind =
    if x == "_" then DontBind else DoBind(Name(x))
  def vlam1(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VLam1(bind(x), Expl, ty, CFun1(b))
  def vlamI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VLam1(bind(x), Impl, ty, CFun1(b))
  def vfun1(ty: VTy, rt: VTy): Val1 = VPi(DontBind, Expl, ty, CFun1(_ => rt))
  def vpi(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VPi(bind(x), Expl, ty, CFun1(b))
  def vpiI(x: String, ty: VTy, b: Val1 => Val1): Val1 =
    VPi(bind(x), Impl, ty, CFun1(b))

  object VVar1:
    def apply(lvl: Lvl): Val1 = VRigid(HVar(lvl), SId)
    def unapply(value: Val1): Option[Lvl] = value match
      case VRigid(HVar(hd), SId) => Some(hd)
      case _                     => None
