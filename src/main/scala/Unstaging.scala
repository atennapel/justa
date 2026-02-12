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
      .flatMap { (m, sds) =>
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
        if ds.isEmpty then None
        else Some(Module(m, Defs(ds)))
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
    go(Evaluation.unstage(tm))(using Nil, Env.Empty, Nil, new Supply(0))._1

  // unstaging
  private def go(
      tm: Tm0
  )(using tenv: TEnv, venv: Env, ren: Ren, supply: Supply): (Tm, CTy) =
    inline def extVEnv: Env = Env.Ext0(venv, V0.Var(mkLvl(venv.size)))
    tm match
      case Tm0.IntLit(v)    => (Tm.IntLit(v), CTy(VTy.Int))
      case Tm0.StringLit(v) => (Tm.StringLit(v), CTy(VTy.String))
      case Tm0.Global(m, x) =>
        State.getGlobalDirect(m, x) match
          case Some(GlobalEntry.Def0(_, _, _, _, _, _, vty, _)) =>
            val cty = goCTy(vty)
            (Tm.Global(m, x, cty), cty)
          case _ => impossible()

      case Tm0.Var(ix) =>
        val ty = tenv(ix.expose)
        (Tm.Local(ren(ix.expose), ty), ty)

      case Tm0.Let(x, ty, v, b) =>
        val y = supply.next()
        val ct = goCTy(ty)
        val (eb, et) = go(b)(using ct :: tenv, extVEnv, y :: ren)
        (Tm.Let(y, -1, ct, go(v)._1, eb), et)
      case Tm0.LetRec(x, ty, v, b) =>
        val y = supply.next()
        val ct = goCTy(ty)
        val nextTEnv = ct :: tenv
        val nextVEnv = extVEnv
        val nextRen = y :: ren
        val (eb, et) = go(b)(using nextTEnv, nextVEnv, nextRen)
        (
          Tm.LetRec(y, -1, ct, go(v)(using nextTEnv, nextVEnv, nextRen)._1, eb),
          et
        )

      case Tm0.Lam(x, ty, b) =>
        val y = supply.next()
        val vt = goTy(ty)
        val (eb, et) = go(b)(using CTy(vt) :: tenv, extVEnv, y :: ren)
        (Tm.Lam(y, -1, vt, eb), CTy.Fun(vt, et))

      case Tm0.App(fn, arg) =>
        val (f, tf) = go(fn)
        val (a, ta) = go(arg)
        (Tm.App(f, a, ta.vty), tf.retty)

      case Tm0.If(rty, c, t, f) =>
        val cty = goCTy(rty)
        (Tm.If(cty, go(c)._1, go(t)._1, go(f)._1), cty)

      case Tm0.Proj(rty, s, p) =>
        val (es, et) = go(s)
        et match
          case CTy.Rec(_) =>
            val cty = goCTy(rty)
            (Tm.CSelect(es, p.ix), cty)
          case CTy.Val(_) =>
            val vty = goTy(rty)
            (Tm.Select(vty, et.vty, es, p.ix), CTy(vty))
          case _ => impossible()

      case Tm0.RecordCon(ty, fs) =>
        goCTy(ty) match
          case ct @ CTy.Rec(_) => (Tm.CRecord(fs.map(f => go(f)._1)), ct)
          case CTy.Val(vty) => (Tm.Record(vty, fs.map(f => go(f)._1)), CTy(vty))
          case _            => impossible()

      case Tm0.Unsafe(rt, io, l, args) =>
        val el = forceAll1(eval1(l)(using venv)) match
          case V.LabelLit(v) => v
          case _             => impossible()
        val ty = goTy(rt)
        val eargs = args.map(go).map((tm, ty) => (tm, ty.vty))
        val rty = if io then CTy.IO(ty) else CTy(ty)
        (Tm.Unsafe(ty, io, el, eargs), rty)

      case Tm0.Case(rty, dty, s, cs) =>
        def goCases(cs: Core.Cases0): Cases =
          cs match
            case Core.Cases0.Empty        => Cases.Empty
            case Core.Cases0.Otherwise(b) => Cases.Otherwise(go(b)._1)
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
              val body = go(b)(using innertenv, innerenv, innerren)._1
              Cases.Ext(x, newps, body, goCases(r))
        val et = goCTy(rty)
        (Tm.Case(et, goTy(dty), go(s)._1, goCases(cs)), et)

      case Tm0.Wk1(tm) => go(tm)(using tenv, venv.wk1)
      case Tm0.Wk0(tm) => go(tm)(using tenv.tail, venv.wk0, ren.tail)

      case Tm0.Splice(tm) =>
        tm match
          case Tm1.Prim(Primitive.True)  => (Tm.True, CTy(VTy.Bool))
          case Tm1.Prim(Primitive.False) => (Tm.False, CTy(VTy.Bool))
          case Tm1.Prim(p @ Primitive.Lt) =>
            (
              Tm.Prim(RuntimePrimitive.Lt),
              CTy.Fun(VTy.Int, CTy.Fun(VTy.Int, CTy.Val(VTy.Bool)))
            )
          case Tm1.Prim(p @ Primitive.Add) =>
            (
              Tm.Prim(RuntimePrimitive.Add),
              CTy.Fun(VTy.Int, CTy.Fun(VTy.Int, CTy.Val(VTy.Int)))
            )
          case Tm1.Prim(p @ Primitive.Sub) =>
            (
              Tm.Prim(RuntimePrimitive.Sub),
              CTy.Fun(VTy.Int, CTy.Fun(VTy.Int, CTy.Val(VTy.Int)))
            )
          case Tm1.Prim(p @ Primitive.Mul) =>
            (
              Tm.Prim(RuntimePrimitive.Mul),
              CTy.Fun(VTy.Int, CTy.Fun(VTy.Int, CTy.Val(VTy.Int)))
            )
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
                (
                  IR.Tm.Con(
                    m,
                    dx,
                    cx,
                    State.conIndex(m, dx, cx),
                    dty,
                    as.map((t, ty) => (t, ty.vty))
                  ),
                  CTy(dty)
                )
              case (Tm1.Prim(Primitive.ReturnIO), List(ty, v)) =>
                val ety = goTy(ty._1)
                val ev = stgo(v._1)
                (IR.Tm.ReturnIO(ety, ev._1), CTy.IO(ety))
              case (Tm1.Prim(Primitive.BindIO), List(ty, _, v, k)) =>
                val ety = goTy(ty._1)
                val ev = stgo(v._1)
                val ek = stgo(k._1)
                val x = supply.next()
                val b = IR.Tm.App(ek._1, IR.Tm.Local(x, CTy(ety)), ety)
                (IR.Tm.BindIO(x, -1, ety, ev._1, b), ek._2.retty)
              case _ => impossible()
  // types
  private def goCTy(ty: Tm1, env: Env = Env.Empty): CTy =
    goCTy(eval1(ty)(using env))
  private def goTy(ty: Tm1, env: Env = Env.Empty): VTy =
    goVTy(eval1(ty)(using env))

  private def goCTy(ty: V): CTy =
    forceAll1(ty) match
      case V.Fun(pty, _, rty) => CTy.Fun(goVTy(pty), goCTy(rty))
      case V.IO(ty)           => CTy.IO(goVTy(ty))
      case vt @ V.RecordTy0(cv, fs) =>
        forceAll1(cv) match
          case V.Val  => CTy.Val(goVTy(vt))
          case V.Comp => CTy.Rec(fs.map((x, t) => (x.toOption, goCTy(t))))
          case _      => impossible()
      case _ => CTy.Val(goVTy(ty))

  private def goVTy(ty: V, menv: State.MonoEnv = Map.empty): VTy =
    forceAll1(ty) match
      case V.Bool => VTy.Bool
      case V.Int  => VTy.Int
      case V.TypeCon0(m, x, args) =>
        VTy.Data(m, x, args.map((a, _) => goVTy(a, menv)))
      case V.Var(lvl)         => menv(lvl)
      case V.RecordTy0(_, fs) => VTy.Record(fs.map((x, t) => (x, goVTy(t))))
      case V.Class(x) =>
        forceAll1(x) match
          case V.LabelLit(c) => VTy.Class(c)
          case _             => impossible()
      case _ => impossible()
