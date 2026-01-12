import Common.*
import Core.{Env, Val1 as V, Val0 as V0, Tm0, Tm1}
import IR.*
import State.GlobalEntry
import Evaluation.{eval1, forceAll1, unstageUnder}

import scala.annotation.tailrec
import scala.collection.mutable

object Unstaging:
  def unstageState(): Defs =
    monoStore.clear()
    newDefs.clear()
    val ds = State.allGlobals.flatMap {
      case GlobalEntry.Def0(x, tm, _, _, _, vty, _) =>
        val nty = goCTy(vty)
        val ntm = unstage(tm)
        Some(Def.Value(x, nty, ntm))
      case _ => None
    }
    val extraDefs = newDefs.toList
    Defs(extraDefs ++ ds)

  private type TEnv = List[CTy]
  private type Ren = List[LocalName]

  private final class Supply(var id: LocalName):
    def next(): LocalName =
      val cur = id
      id += 1
      cur

  private def unstage(tm: Tm0): Tm =
    go(Evaluation.unstage(tm))(using Nil, Env.Empty, Nil, new Supply(0))

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
        val y = supply.next()
        val ct = goCTy(ty)
        Tm.Let(y, -1, ct, go(v), go(b)(using ct :: tenv, extVEnv, y :: ren))
      case Tm0.LetRec(x, ty, v, b) =>
        val y = supply.next()
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
        val y = supply.next()
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
          case Tm1.Prim(p @ Primitive.Lt)  => Tm.Prim(RuntimePrimitive.Lt)
          case Tm1.Prim(p @ Primitive.Add) => Tm.Prim(RuntimePrimitive.Add)
          case Tm1.Prim(p @ Primitive.Sub) => Tm.Prim(RuntimePrimitive.Sub)
          case Tm1.Prim(p @ Primitive.Mul) => Tm.Prim(RuntimePrimitive.Mul)
          case _ =>
            @tailrec
            def apps(
                tm: Tm1,
                args: List[(Tm1, Icit)] = Nil
            ): (Tm1, List[(Tm1, Icit)]) =
              tm match
                case Tm1.App(f, a, i) => apps(f, (a, i) :: args)
                case Tm1.Prim(_)      => (tm, args)
                case Tm1.Con(_, _)    => (tm, args)
                case _                => impossible()
            def takeImpl(args: List[(Tm1, Icit)]): List[Tm1] =
              args match
                case (a, Icit.Impl) :: tl => a :: takeImpl(tl)
                case _                    => Nil
            def stWithEnv(t: Tm1, e: Env) = unstageUnder(t.splice, e)
            inline def st(t: Tm1) = stWithEnv(t, venv)
            inline def stgo(t: Tm1) = go(st(t))
            apps(tm) match
              case (Tm1.Con(dx, cx), args) =>
                val ps = takeImpl(args).map(eval1)
                val as = args.drop(ps.size).map((t, _) => stgo(t))
                monomorphize(dx, ps) match
                  case IR.VTy.Data(mx) =>
                    IR.Tm.Con(mx, cx, conIndex(dx, cx), as)
                  case _ => impossible()
              case _ => impossible()
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
      case V.Bool             => VTy.Bool
      case V.Int              => VTy.Int
      case V.TypeCon(x, args) => monomorphize(x, args.map((a, _) => a))
      case _                  => impossible()

  // monomorphization
  private type MonoKey = (Name, List[IR.VTy])
  private var currentModule: Option[Name] = None
  private val monoStore = mutable.Map.empty[MonoKey, Name]
  private val monoRecStore = mutable.Map.empty[Assoc[IR.VTy], Name]
  private val newDefs = mutable.ArrayBuffer.empty[IR.Def]

  private def conIndex(dx: Name, cx: Name): Int =
    State.getGlobal(dx) match
      case Some(GlobalEntry.Data(_, _, xs, _, _, _)) => xs.indexOf(cx)
      case _                                         => impossible()

  private def monomorphize(mx: Name, ps: List[V]): IR.VTy =
    val xs = State.getGlobal(mx) match
      case Some(GlobalEntry.Data(_, _, xs, _, _, _)) => xs
      case _                                         => impossible()
    val eps = ps.map(goVTy)
    val (nx, alreadyDone) = monomorphize(mx, eps)
    if !alreadyDone then
      val cons = xs.map { cx =>
        State.getGlobal(cx) match
          case Some(GlobalEntry.Con(_, _, ps, _, _, _, _, _)) => cx -> ps
          case _                                              => impossible()
      }
      val env = Env(ps)
      val ecs = cons.map { (cx, ts) =>
        val ets = ts.map((x, t) => (x.toOption, goVTy(t, env)))
        IR.Constructor(cx, ets)
      }
      newDefs += IR.Def.Data(nx, ecs)
    IR.VTy.Data(nx)

  private def monomorphize(name: Name, ps: List[IR.VTy]): (Name, Boolean) =
    val k = (name, ps)
    monoStore.get(k) match
      case Some(x) => (x, true)
      case None =>
        val x = createName(name, ps)
        monoStore += k -> x
        (x, false)

  private def createName(name: Name, ps: List[IR.VTy]): Name =
    def paramStr(p: IR.VTy): String = p match
      case VTy.Bool    => "bool"
      case VTy.Int     => "int"
      case VTy.Data(x) => s"$x"
    if ps.isEmpty then name
    else Name(s"${name}_${ps.map(paramStr).mkString("_")}")
