import Common.*
import Core.{Env, Val1 as V, Val0 as V0, Tm0, Tm1}
import IR.*
import State.GlobalEntry
import Evaluation.{eval1, forceAll1}

object Unstaging:
  def unstageState(): Defs =
    Defs(State.allGlobals.flatMap {
      case GlobalEntry.Def0(x, tm, _, _, _, vty, _) =>
        val nty = goCTy(vty)
        val ntm = unstage(tm)
        Some(Def(x, nty, ntm))
      case _ => None
    })

  private type TEnv = List[CTy]
  private type Ren = List[LocalName]

  private final case class Supply(var id: LocalName):
    def next: LocalName =
      val cur = id
      id += 1
      cur

  private def unstage(tm: Tm0): Tm =
    go(Evaluation.unstage(tm))(using Nil, Env.Empty, Nil, Supply(0))

  // unstaging
  private def go(
      tm: Tm0
  )(using tenv: TEnv, venv: Env, ren: Ren, supply: Supply): Tm =
    inline def extVEnv: Env = Env.Ext0(venv, V0.Var(mkLvl(venv.size)))
    tm match
      case Tm0.IntLit(v) => Tm.IntLit(v)
      case Tm0.Global(x) => Tm.Global(x)

      case Tm0.Var(ix) => Tm.Local(ren(ix.expose), tenv(ix.expose))

      case Tm0.Let(x, ty, v, b) =>
        val y = supply.next
        val ct = goCTy(ty)
        Tm.Let(y, -1, ct, go(v), go(b)(using ct :: tenv, extVEnv, y :: ren))
      case Tm0.LetRec(x, ty, v, b) =>
        val y = supply.next
        val ct = goCTy(ty)
        val nextTEnv = ct :: tenv
        val nextVEnv = extVEnv
        val nextRen = y :: ren
        Tm.LetRec(
          y,
          -1,
          ct,
          go(v)(using nextTEnv, nextVEnv, nextRen),
          go(b)(using nextTEnv, nextVEnv, nextRen)
        )

      case Tm0.Lam(x, ty, b) =>
        val y = supply.next
        val vt = goVTy(ty)
        Tm.Lam(
          y,
          -1,
          goVTy(ty),
          go(b)(using CTy(vt) :: tenv, extVEnv, y :: ren)
        )

      case Tm0.App(fn, arg) => Tm.App(go(fn), go(arg))

      case Tm0.If(rty, c, t, f) => Tm.If(goCTy(rty), go(c), go(t), go(f))

      case Tm0.Wk1(tm) => go(tm)(using tenv, venv.wk1)
      case Tm0.Wk0(tm) => go(tm)(using tenv.tail, venv.wk0, ren.tail)

      case Tm0.Splice(tm) =>
        tm match
          case Tm1.Prim(Primitive.True)    => Tm.True
          case Tm1.Prim(Primitive.False)   => Tm.False
          case Tm1.Prim(p @ Primitive.Lt)  => Tm.Prim(p)
          case Tm1.Prim(p @ Primitive.Add) => Tm.Prim(p)
          case Tm1.Prim(p @ Primitive.Sub) => Tm.Prim(p)
          case Tm1.Prim(p @ Primitive.Mul) => Tm.Prim(p)
          case _                           => impossible()

  // types
  private def goCTy(ty: Tm1, env: Env = Env.Empty): CTy =
    goCTy(eval1(ty)(using env))
  private def goVTy(ty: Tm1, env: Env = Env.Empty): VTy =
    goVTy(eval1(ty)(using env))

  private def goCTy(ty: V): CTy =
    forceAll1(ty) match
      case V.Fun(pty, _, rty) => CTy(goVTy(pty), goCTy(rty))
      case _                  => CTy(goVTy(ty))

  private def goVTy(ty: V): VTy =
    forceAll1(ty) match
      case V.Bool => VTy.Bool
      case V.Int  => VTy.Int
      case _      => impossible()
