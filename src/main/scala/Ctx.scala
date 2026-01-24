import Common.*
import Common.Icit.*
import Core.*
import Evaluation.UnfoldOption
import Ctx.NameMap
import Evaluation.apply

final case class Ctx(
    lvl: Lvl,
    env: Env,
    locals: Locals,
    pruning: Pruning,
    binds: List[Bind],
    names: NameMap,
    allTypes1: List[Option[(VTy, Option[Val1])]],
    pos: PosInfo
):
  import Ctx.NameInfo
  import Ctx.NameInfo.*

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

  inline def bindOfLvl(x: Lvl): Bind = binds.reverse(x.expose)

  inline def enter(pos: PosInfo): Ctx = copy(pos = pos)

  inline def lookup(x: Name): Option[NameInfo] = names.get(x)

  def bind1(x: Bind, ty: Ty, vty: VTy): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext1(env, Val1.Var(lvl)),
      Locals.Bind1(locals, ty),
      PruneEntry.Bind1(Expl) :: pruning,
      x :: binds,
      addName(x, Name1(lvl, vty)),
      Some((vty, None)) :: allTypes1,
      pos
    )

  def insert1(x: Bind, ty: Ty): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext1(env, Val1.Var(lvl)),
      Locals.Bind1(locals, ty),
      PruneEntry.Bind1(Expl) :: pruning,
      x :: binds,
      names,
      Some((eval1(ty), None)) :: allTypes1,
      pos
    )

  def define(x: Name, ty: Ty, vty: VTy, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext1(env, vv),
      Locals.Def(locals, ty, v),
      PruneEntry.Skip :: pruning,
      Bind.DoBind(x) :: binds,
      names + (x -> Name1(lvl, vty)),
      Some((vty, Some(vv))) :: allTypes1,
      pos
    )

  def defineInsert(x: Name, ty: Ty, v: Tm1, vv: Val1): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext1(env, vv),
      Locals.Def(locals, ty, v),
      PruneEntry.Skip :: pruning,
      Bind.DoBind(x) :: binds,
      names,
      Some((eval1(ty), Some(vv))) :: allTypes1,
      pos
    )

  def bind0(x: Bind, ty: Ty, vty: VTy, cv: Ty, vcv: VTy): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext0(env, Val0.Var(lvl)),
      Locals.Bind0(locals, ty, cv),
      PruneEntry.Bind0 :: pruning,
      x :: binds,
      addName(x, Name0(lvl, vty, vcv)),
      None :: allTypes1,
      pos
    )

  def insert0(x: Bind, ty: Ty, cv: Ty): Ctx =
    Ctx(
      lvl + 1,
      Env.Ext0(env, Val0.Var(lvl)),
      Locals.Bind0(locals, ty, cv),
      PruneEntry.Bind0 :: pruning,
      x :: binds,
      names,
      None :: allTypes1,
      pos
    )

  inline def readback1(
      v: Val1,
      unfoldOption: UnfoldOption = UnfoldOption.None
  ): Tm1 =
    Evaluation.readback1(v)(using lvl, unfoldOption)
  inline def readback0(
      v: Val0,
      unfoldOption: UnfoldOption = UnfoldOption.None
  ): Tm0 =
    Evaluation.readback0(v)(using lvl, unfoldOption)
  inline def eval1(t: Tm1): Val1 = Evaluation.eval1(t)(using env)
  inline def eval0(t: Tm0): Val0 = Evaluation.eval0(t)(using env)

  inline def pretty1(
      v: Val1,
      unfoldOption: UnfoldOption = UnfoldOption.Metas
  ): String =
    Pretty.pretty1(Evaluation.readback1(v)(using lvl, unfoldOption))(using
      binds
    )
  inline def pretty0(
      v: Val0,
      unfoldOption: UnfoldOption = UnfoldOption.Metas
  ): String =
    Pretty.pretty0(Evaluation.readback0(v)(using lvl, unfoldOption))(using
      binds
    )
  inline def pretty1(v: Tm1): String = Pretty.pretty1(v)(using binds)
  inline def pretty0(v: Tm0): String = Pretty.pretty0(v)(using binds)

  inline def prettyParen1(v: Tm1): String = Pretty.prettyParen1(v)(using binds)

  inline def prettyClos1(
      x: Bind,
      v: Clos1,
      unfoldOption: UnfoldOption = UnfoldOption.Metas
  ): String =
    Pretty.pretty1(
      Evaluation.readback1(v(Val1.Var(lvl)))(using lvl + 1, unfoldOption)
    )(using x :: binds)

  def show: String =
    def go(bs: List[Bind], ls: Locals): List[String] =
      (bs, ls) match
        case (Nil, Locals.Empty) => Nil
        case (x :: bs, Locals.Def(ls, ty, v)) =>
          val tl = go(bs, ls)
          s"$x : ${Pretty.pretty1(ty)(using bs)} = ${Pretty.pretty1(v)(using bs)}" :: tl
        case (x :: bs, Locals.Bind0(ls, ty, cv)) =>
          s"$x : ${Pretty.pretty1(ty)(using bs)}" :: go(bs, ls)
        case (x :: bs, Locals.Bind1(ls, ty)) =>
          s"$x : ${Pretty.pretty1(ty)(using bs)}" :: go(bs, ls)
        case _ => impossible()
    go(binds, locals).mkString("\n")

object Ctx:
  def empty(pos: PosInfo) =
    Ctx(lvl0, Env.Empty, Locals.Empty, Nil, Nil, Map.empty, Nil, pos)

  enum NameInfo:
    case Name0(_lvl: Lvl, ty: VTy, cv: VTy)
    case Name1(_lvl: Lvl, ty: VTy)
    def lvl: Lvl = this match
      case Name0(_lvl, ty, cv) => _lvl
      case Name1(_lvl, ty)     => _lvl

  type NameMap = Map[Name, NameInfo]
