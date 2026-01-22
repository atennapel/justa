import Common.*
import Core.{Env, Val1 as V, Val0 as V0, Tm0, Tm1}
import IR.*
import State.GlobalEntry
import Evaluation.{eval1, forceAll1, unstageUnder}

import scala.annotation.tailrec

object Unstaging:
  def unstageState(): List[Module] =
    State
      .allGlobals()
      .map { (m, sds) =>
        val ds = sds.flatMap {
          case GlobalEntry.Def0(pub, x, tm, _, _, _, vty, _) =>
            val nty = goCTy(vty)
            val ntm = unstage(tm)
            Some(Def(pub, x, nty, ntm))
          case GlobalEntry.Con0(_, cx, typarams, params, dx, _, _, _, _) =>
            State.setMono(m, dx, cx) { menv =>
              val env =
                Env(
                  (0 until typarams.size).reverse
                    .map(i => V.Var(mkLvl(i)))
                    .toList
                )
              params.map { case (x, ty) =>
                val vty = eval1(ty)(using env)
                val ty2 = goVTy(vty, menv)
                (x, ty2)
              }
            }
            None
          case _ =>
            None
        }
        Module(m, Defs(ds))
      }
      .toList

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
      case Tm0.Global(m, x) =>
        State.getGlobalDirect(m, x) match
          case Some(GlobalEntry.Def0(_, _, _, _, _, _, vty, _)) =>
            Tm.Global(m, x, goCTy(vty))
          case _ => impossible()

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
        val vt = goTy(ty)
        Tm.Lam(
          y,
          -1,
          goTy(ty),
          go(b)(using CTy(vt) :: tenv, extVEnv, y :: ren)
        )

      case Tm0.App(fn, arg) => Tm.App(go(fn), go(arg))

      case Tm0.If(rty, c, t, f) => Tm.If(goCTy(rty), go(c), go(t), go(f))

      case Tm0.Proj(rty, s, p) => Tm.Select(goTy(rty), go(s), p.ix)

      case Tm0.RecordCon(ty, fs) => Tm.Record(goTy(ty), fs.map(go))

      case Tm0.Case(rty, dty, s, cs) =>
        def goCases(cs: Core.Cases0): Cases =
          cs match
            case Core.Cases0.Empty        => Cases.Empty
            case Core.Cases0.Otherwise(b) => Cases.Otherwise(go(b))
            case Core.Cases0.Ext(x, ps, b, r) =>
              @tailrec
              def addParamsRec(
                  ps: List[(Bind, Tm1)],
                  newps: List[(LocalName, VTy, Int)],
                  tenv: TEnv,
                  env: Env,
                  ren: Ren
              ): (List[(LocalName, VTy, Int)], TEnv, Env, Ren) =
                ps match
                  case Nil => (newps, tenv, env, ren)
                  case (_, ty) :: rest =>
                    val x = supply.next()
                    val vt = goTy(ty)
                    addParamsRec(
                      rest,
                      newps :+ (x, vt, -1),
                      CTy(vt) :: tenv,
                      Env.Ext0(env, V0.Var(mkLvl(env.size))),
                      x :: ren
                    )
              inline def addParams(
                  ps: List[(Bind, Tm1)]
              )(using
                  tenv: TEnv,
                  env: Env,
                  ren: Ren
              ): (List[(LocalName, VTy, Int)], TEnv, Env, Ren) =
                addParamsRec(ps, Nil, tenv, env, ren)
              val (newps, innertenv, innerenv, innerren) = addParams(ps)
              val body = go(b)(using innertenv, innerenv, innerren)
              Cases.Ext(x, newps, body, goCases(r))
        Tm.Case(goCTy(rty), goTy(dty), go(s), goCases(cs))

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
                case Tm1.App(f, a, i)  => apps(f, (a, i) :: args)
                case Tm1.Prim(_)       => (tm, args)
                case Tm1.Con0(_, _, _) => (tm, args)
                case _                 => impossible()
            def takeImpl(args: List[(Tm1, Icit)]): List[Tm1] =
              args match
                case (a, Icit.Impl) :: tl => a :: takeImpl(tl)
                case _                    => Nil
            def stWithEnv(t: Tm1, e: Env) = unstageUnder(t.splice, e)
            inline def st(t: Tm1) = stWithEnv(t, venv)
            inline def stgo(t: Tm1) = go(st(t))
            apps(tm) match
              case (Tm1.Con0(m, dx, cx), args) =>
                val ps = takeImpl(args).map(eval1)
                val dty = VTy.Data(m, dx, ps.map(t => goVTy(t)))
                val as = args.drop(ps.size).map((t, _) => stgo(t))
                IR.Tm.Con(m, dx, cx, State.conIndex(m, dx, cx), dty, as)
              case (Tm1.Prim(Primitive.ReturnIO), List(ty, v)) =>
                val ety = goTy(ty._1)
                val ev = stgo(v._1)
                IR.Tm.ReturnIO(ety, ev)
              case (Tm1.Prim(Primitive.BindIO), List(ty, _, v, k)) =>
                val ety = goTy(ty._1)
                val ev = stgo(v._1)
                val ek = stgo(k._1)
                val x = supply.next()
                val b = IR.Tm.App(ek, IR.Tm.Local(x, CTy(ety)))
                IR.Tm.BindIO(x, -1, ety, ev, b)
              case _ => impossible()
  // types
  private def goCTy(ty: Tm1, env: Env = Env.Empty): CTy =
    goCTy(eval1(ty)(using env))
  private def goTy(ty: Tm1, env: Env = Env.Empty): VTy =
    goVTy(eval1(ty)(using env))

  private def goCTy(ty: V): CTy =
    forceAll1(ty) match
      case V.Fun(pty, _, rty) => CTy(goVTy(pty), goCTy(rty))
      case V.IO(ty)           => CTy(Nil, true, goVTy(ty))
      case _                  => CTy(goVTy(ty))

  private def goVTy(ty: V, menv: State.MonoEnv = Map.empty): VTy =
    forceAll1(ty) match
      case V.Bool => VTy.Bool
      case V.Int  => VTy.Int
      case V.TypeCon0(m, x, args) =>
        VTy.Data(m, x, args.map((a, _) => goVTy(a, menv)))
      case V.Var(lvl)      => menv(lvl)
      case V.RecordTy0(fs) => VTy.Record(fs.map((x, t) => (x, goVTy(t))))
      case _               => impossible()
