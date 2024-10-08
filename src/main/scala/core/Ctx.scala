package core

import common.Common.*
import Syntax.*
import Value.*
import Evaluation.QuoteOption
import Evaluation.QuoteOption.*
import Pretty.{
  pretty0 as pretty0_,
  pretty1 as pretty1_,
  prettyParen1 as prettyParen1_
}

import Ctx.NameMap

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    pruning: Pruning,
    binds: List[Bind],
    names: NameMap,
    pos: PosInfo
):
  import Ctx.NameInfo
  import Ctx.NameInfo.*

  private def addName(x: Bind, info: NameInfo): NameMap =
    x match
      case DontBind  => names
      case DoBind(x) => names + (x -> info)

  def typeOfLvl(x: Lvl): Ty =
    def go(ls: Locals, i: Int): Ty = ls match
      case LEmpty                        => impossible()
      case LDef(locs, ty, _) if i == 0   => ty
      case LBind0(locs, ty, _) if i == 0 => ty
      case LBind1(locs, ty) if i == 0    => ty
      case LDef(ls, _, _)                => go(ls, i - 1)
      case LBind0(ls, _, _)              => go(ls, i - 1)
      case LBind1(ls, _)                 => go(ls, i - 1)
    go(locals, x.toIx(lvl).expose)

  def bindOfLvl(x: Lvl): Bind = binds.reverse(x.expose)

  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def lookup(x: Name): Option[NameInfo] = names.get(x)

  def bind1(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(
      lvl + 1,
      E1(env, VVar1(lvl)),
      LBind1(locals, ty),
      PEBind1(Expl) :: pruning,
      x :: binds,
      addName(x, Name1(lvl, vty)),
      pos
    )

  def insert1(x: Bind, ty: Ty): Ctx =
    Ctx(
      lvl + 1,
      E1(env, VVar1(lvl)),
      LBind1(locals, ty),
      PEBind1(Expl) :: pruning,
      x :: binds,
      names,
      pos
    )

  def define(x: Name, ty: Ty, vty: VTy, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      E1(env, vv),
      LDef(locals, ty, v),
      PESkip :: pruning,
      DoBind(x) :: binds,
      names + (x -> Name1(lvl, vty)),
      pos
    )

  def defineInsert(x: Name, ty: Ty, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      E1(env, vv),
      LDef(locals, ty, v),
      PESkip :: pruning,
      DoBind(x) :: binds,
      names,
      pos
    )

  def bind0(x: Bind, ty: Ty, vty: VTy, cv: CV, vcv: VTy): Ctx =
    Ctx(
      lvl + 1,
      E0(env, VVar0(lvl)),
      LBind0(locals, ty, cv),
      PEBind0 :: pruning,
      x :: binds,
      addName(x, Name0(lvl, vty, vcv)),
      pos
    )

  def insert0(x: Bind, ty: Ty, cv: CV): Ctx =
    Ctx(
      lvl + 1,
      E0(env, VVar0(lvl)),
      LBind0(locals, ty, cv),
      PEBind0 :: pruning,
      x :: binds,
      names,
      pos
    )

  def quote1(v: Val1, q: QuoteOption = UnfoldNone)(implicit
      e: Evaluation
  ): Tm1 =
    e.quote1(v, q)(lvl)
  def quote0(v: Val0, q: QuoteOption = UnfoldNone)(implicit
      e: Evaluation
  ): Tm0 =
    e.quote0(v, q)(lvl)
  def eval1(t: Tm1)(implicit e: Evaluation): Val1 =
    e.eval1(t)(env)
  def eval0(t: Tm0)(implicit e: Evaluation): Val0 =
    e.eval0(t)(env)

  def pretty1(v: Val1, q: QuoteOption = UnfoldMetas)(implicit
      e: Evaluation
  ): String =
    pretty1_(e.quote1(v, q)(lvl))(binds)
  def pretty0(v: Val0, q: QuoteOption = UnfoldMetas)(implicit
      e: Evaluation
  ): String =
    pretty0_(e.quote0(v, q)(lvl))(binds)
  def pretty1(v: Tm1): String = pretty1_(v)(binds)
  def pretty0(v: Tm0): String = pretty0_(v)(binds)

  def prettyParen1(v: Tm1): String = prettyParen1_(v)(binds)

object Ctx:
  def empty(pos: PosInfo) = Ctx(lvl0, EEmpty, LEmpty, Nil, Nil, Map.empty, pos)

  enum NameInfo:
    case Name0(_lvl: Lvl, ty: VTy, cv: VTy)
    case Name1(_lvl: Lvl, ty: VTy)
    def lvl: Lvl = this match
      case Name0(_lvl, ty, cv) => _lvl
      case Name1(_lvl, ty)     => _lvl

  type NameMap = Map[Name, NameInfo]
