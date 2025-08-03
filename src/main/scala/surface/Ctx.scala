package surface

import common.Common.*
import common.Common.Icit.*
import core.Core.*
import core.Evaluation.QuoteOption
import core.Evaluation
import core.Pretty
import Ctx.*

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    pruning: Pruning,
    binds: List[Bind],
    names: NameMap,
    pos: PosInfo
):
  private def addName(x: Bind, info: NameInfo): NameMap =
    x match
      case Bind.DontBind  => names
      case Bind.DoBind(x) => names + (x -> info)

  def typeOfLvl(x: Lvl): Ty =
    def go(ls: Locals, i: Int): Ty = ls match
      case Locals.Empty                        => impossible()
      case Locals.Def(locs, ty, _) if i == 0   => ty
      case Locals.Bind0(locs, ty, _) if i == 0 => ty
      case Locals.Bind1(locs, ty) if i == 0    => ty
      case Locals.Def(ls, _, _)                => go(ls, i - 1)
      case Locals.Bind0(ls, _, _)              => go(ls, i - 1)
      case Locals.Bind1(ls, _)                 => go(ls, i - 1)
    go(locals, x.toIx(using lvl).expose)

  def bindOfLvl(x: Lvl): Bind = binds.reverse(x.expose)

  def enter(pos: PosInfo): Ctx = copy(pos = pos)

  def lookup(x: Name): Option[NameInfo] = names.get(x)

  def bind1(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(
      lvl + 1,
      Env.E1(env, Var1(lvl)),
      Locals.Bind1(locals, ty),
      PruneEntry.Bind1(Expl) :: pruning,
      x :: binds,
      addName(x, NameInfo.Name1(lvl, vty)),
      pos
    )

  def insert1(x: Bind, ty: Ty): Ctx =
    Ctx(
      lvl + 1,
      Env.E1(env, Var1(lvl)),
      Locals.Bind1(locals, ty),
      PruneEntry.Bind1(Expl) :: pruning,
      x :: binds,
      names,
      pos
    )

  def define(x: Name, ty: Ty, vty: VTy, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      Env.E1(env, vv),
      Locals.Def(locals, ty, v),
      PruneEntry.Skip :: pruning,
      Bind.DoBind(x) :: binds,
      names + (x -> NameInfo.Name1(lvl, vty)),
      pos
    )

  def defineInsert(x: Name, ty: Ty, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      Env.E1(env, vv),
      Locals.Def(locals, ty, v),
      PruneEntry.Skip :: pruning,
      Bind.DoBind(x) :: binds,
      names,
      pos
    )

  def bind0(x: Bind, ty: Ty, vty: VTy, cv: Ty, vcv: VTy): Ctx =
    Ctx(
      lvl + 1,
      Env.E0(env, Val0.Var(lvl)),
      Locals.Bind0(locals, ty, cv),
      PruneEntry.Bind0 :: pruning,
      x :: binds,
      addName(x, NameInfo.Name0(lvl, vty, vcv)),
      pos
    )

  def insert0(x: Bind, ty: Ty, cv: Ty): Ctx =
    Ctx(
      lvl + 1,
      Env.E0(env, Val0.Var(lvl)),
      Locals.Bind0(locals, ty, cv),
      PruneEntry.Bind0 :: pruning,
      x :: binds,
      names,
      pos
    )

  def quote1(v: Val1, q: QuoteOption = QuoteOption.UnfoldNone): Tm1 =
    Evaluation.quote1(v, q)(using lvl)
  def quote0(v: Val0, q: QuoteOption = QuoteOption.UnfoldNone): Tm0 =
    Evaluation.quote0(v, q)(using lvl)
  def eval1(t: Tm1): Val1 = Evaluation.eval1(t)(using env)
  def eval0(t: Tm0): Val0 = Evaluation.eval0(t)(using env)

  // TODO: use UnfoldMetas for pretty
  def pretty1(v: Val1, q: QuoteOption = QuoteOption.UnfoldNone): String =
    Pretty.pretty1(Evaluation.quote1(v, q)(using lvl))(using binds)
  def pretty0(v: Val0, q: QuoteOption = QuoteOption.UnfoldNone): String =
    Pretty.pretty0(Evaluation.quote0(v, q)(using lvl))(using binds)
  def pretty1(v: Tm1): String = Pretty.pretty1(v)(using binds)
  def pretty0(v: Tm0): String = Pretty.pretty0(v)(using binds)
  def prettyParen1(v: Tm1): String = Pretty.prettyParen1(v)(using binds)

object Ctx:
  def empty: Ctx =
    Ctx(lvl0, Env.Empty, Locals.Empty, Nil, Nil, Map.empty, PosInfo.start)

  enum NameInfo:
    case Name0(_lvl: Lvl, ty: VTy, cv: VTy)
    case Name1(_lvl: Lvl, ty: VTy)
    def lvl: Lvl = this match
      case Name0(_lvl, _, _) => _lvl
      case Name1(_lvl, _)    => _lvl

  private type NameMap = Map[Name, NameInfo]
