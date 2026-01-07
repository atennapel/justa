import Common.*
import Core.*

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
  def eval0(t: Tm0)(using env: Env): Val0 = ???

  def eval1(t: Tm1)(using env: Env): Val1 = ???

  // forcing
  def force1(v: Val1): Val1 = ???

  def forceAll1(v: Val1): Val1 = ???

  def forceAll0(v: Val0): Val0 = ???

  def forceMetas1(v: Val1): Val1 = ???

  def forceMetas0(v: Val0): Val0 = ???

  def forceUnstage1(v: Val1): Val1 = ???

  def forceUnstage0(v: Val0): Val0 = ???

  // readback
  enum UnfoldOption:
    case All
    case Metas
    case None
    case Unstage

  def readback1(v: Val1)(implicit lvl: Lvl, q: UnfoldOption): Tm1 = ???

  def readback0(v: Val0)(implicit lvl: Lvl, q: UnfoldOption): Tm0 = ???

  // helpers
  def unstage(tm: Tm0): Tm0 =
    readback0(eval0(tm)(using Env.Empty))(using lvl0, UnfoldOption.Unstage)
  def unstageUnder(tm: Tm0, env: Env): Tm0 =
    readback0(eval0(tm)(using env))(using mkLvl(env.size), UnfoldOption.Unstage)
