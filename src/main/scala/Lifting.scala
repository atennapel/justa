import Common.*
import IR.*
//import State.*
import Debug.debug

//import scala.annotation.tailrec
import scala.collection.mutable

// lift out local functions, create join points, rename with unique names
object Lifting:
  // the passed definitions should be simplified!
  def liftModules(mods: List[Module]): List[JVM.Module] =
    mods.map(liftModule)

  private def liftModule(mod: Module): JVM.Module =
    JVM.Module(mod.name, liftDefs(mod.name, mod.defs))

  private def liftDefs(mod: Name, ds: Defs): JVM.Defs =
    // currentModule = mod
    JVM.Defs(ds.toList.flatMap(d => liftDef(mod, d)))

  private final class Emit(
      name: Name,
      private val defs: mutable.ArrayBuffer[JVM.Def] = mutable.ArrayBuffer.empty
  ):
    inline def emit(inline k: Name => JVM.Def): Name =
      val x = Name(s"${name}$$${defs.size}")
      defs += k(x)
      x

    inline def toList: List[JVM.Def] = defs.toList

  private final class Supply(var id: LocalName):
    def next(): LocalName =
      val cur = id
      id += 1
      cur

  private type Ren = Map[LocalName, RenEntry]
  private enum RenEntry:
    case RenVar(name: LocalName)
    case JoinPoint(name: LocalName)
    case LiftedFun(mod: Name, name: Name, extraArgs: List[(LocalName, CTy)])
  // import RenEntry.*

  private def liftDef(mod: Name, d: Def): List[JVM.Def] =
    debug(s"liftDef $mod.${d.name}")
    println(d)
    ???
    /*
    newDefs.clear()
    val Def(pub, name, ty, v) = d
    given emit: Emit = new Emit(d.name)
    given Supply = new Supply(0)
    given Ren = renParams(ty)
    given (Name, Name) = (mod, name)
    val value = go(removeLams(ty, v), true, Some(lamTypes(v)))

    val retty = goVTy(ty.ret)
    val acc = if pub then JVM.Access.Pub else JVM.Access.Priv
    val cdef =
      if ty.params.isEmpty && !ty.io then JVM.Def.Value(acc, name, retty, value)
      else
        val ps = ty.params.zipWithIndex.map((ty, ix) => (ix, goVTy(ty)))
        JVM.Def.Function(acc, name, ps, retty, value)
    newDefs.toList ++ emit.toList :+ cdef


  private inline def renParams(ty: CTy, ren: Ren = Map.empty)(using
      supply: Supply
  ): Ren = renParamsN(ty.params.size, ren)

  @tailrec
  private def renParamsN(n: Int, ren: Ren = Map.empty, start: Int = 0)(using
      supply: Supply
  ): Ren =
    start match
      case _ if start >= n => ren
      case start =>
        renParamsN(n, ren + (start -> RenVar(supply.next())), start + 1)

  private def go(
      t: Tm,
      tail: Boolean,
      toplevel: Option[List[(Int, CTy)]] = None
  )(using
      ren: Ren,
      emit: Emit,
      supply: Supply,
      currentDef: (Name, Name)
  ): JVM.Tm =
    t match
      case Tm.Lam(_, _, _, _) => impossible()
      case Tm.Local(ix, ty) =>
        ren(ix) match
          case RenVar(x)          => JVM.Tm.Local(x, goCTy(ty))
          case JoinPoint(x)       => JVM.Tm.Jump(x, Nil)
          case LiftedFun(_, _, _) => impossible()
      case Tm.Global(m, x, ty) =>
        if ty.params.nonEmpty then impossible()
        else if ty.io then JVM.Tm.GlobalApp(m, x, Nil)
        else JVM.Tm.Global(m, x)
      case Tm.Prim(p)    => JVM.Tm.Prim(p, Nil)
      case Tm.BoolLit(v) => JVM.Tm.bool(v)
      case Tm.IntLit(v)  => JVM.Tm.IntLit(v)

      case Tm.ReturnIO(_, v) => go(v, tail)
      case Tm.BindIO(x, _, ty, v, b) =>
        val y = supply.next()
        JVM.Tm.Let(
          y,
          goVTy(ty),
          go(v, false),
          go(b, tail)(using ren = ren + (x -> RenVar(y)))
        )

      case Tm.If(_, c, t, f) =>
        JVM.Tm.If(go(c, false), go(t, tail), go(f, tail))
      case Tm.Con(m, _, cx, ix, dty, args) =>
        val (mdx, dx) = goData(dty)
        JVM.Tm.Con(mdx, dx, cx, ix, args.map(go(_, false)))
      case Tm.Record(dty, args) =>
        val (mdx, dx) = goData(dty)
        JVM.Tm.Con(mdx, dx, JVM.RecordConName, 0, args.map(go(_, false)))

      case Tm.Select(_, s, i) => JVM.Tm.Select(go(s, false), i)

      case Tm.App(_, _) =>
        val (f, a) = t.flattenApps
        f match
          case Tm.Global(m, x, _) =>
            JVM.Tm.GlobalApp(m, x, a.map(a => go(a, false)))
          case Tm.Prim(p) => JVM.Tm.Prim(p, a.map(a => go(a, false)))
          case Tm.Local(ix, ty) =>
            ren(ix) match
              case RenVar(x)    => impossible()
              case JoinPoint(x) => JVM.Tm.Jump(x, a.map(a => go(a, false)))
              case LiftedFun(m, x, args) =>
                val extraArgs = args.map((x, ty) => go(Tm.Local(x, ty), false))
                JVM.Tm.GlobalApp(m, x, extraArgs ++ a.map(a => go(a, false)))
          case _ => impossible()

      case Tm.Let(x, _, ty, v, b) if tail && isUsedInTailOnly(x, true, b) =>
        val y = supply.next()
        val lams = lamTypes(v)
        val valueRen = renLifted(lams, ren)
        val newLamTypes = renameLamTypes(lams, valueRen)
        JVM.Tm.Join(
          y,
          newLamTypes,
          go(removeLams(ty, v), false)(using ren = valueRen),
          go(b, tail)(using ren = ren + (x -> JoinPoint(y)))
        )

      case Tm.Let(x, _, CTy(Nil, false, ty), v, b) =>
        val y = supply.next()
        JVM.Tm.Let(
          y,
          goVTy(ty),
          go(v, false),
          go(b, tail)(using ren = ren + (x -> RenVar(y)))
        )

      case Tm.Let(x, _, ty, v, b) =>
        val freeps = free(v)
        val y = emit.emit { y =>
          val freen = freeps.size
          val ps = freeps.map((x, ty) =>
            (x, goCTy(ty))
          ) ++ ty.params.zipWithIndex.map((ty, x) => (x + freen, goVTy(ty)))
          given Supply = new Supply(0)
          given ren: Ren = renLifted(freeps ++ lamTypes(v))
          given Name = y
          val body = go(removeLams(ty, v), true)
          JVM.Def.Function(JVM.Access.Synth, y, ps, goVTy(ty.ret), body)
        }
        go(b, tail)(using
          ren = ren + (x -> LiftedFun(currentDef._1, y, freeps))
        )

      case Tm.LetRec(x, _, ty, v, b)
          if tail && isUsedInTailOnly(x, true, v) &&
            isUsedInTailOnly(x, true, b) =>
        val y = supply.next()
        val lams = lamTypes(v)
        val valueRen = renLifted(lams, ren) + (x -> JoinPoint(y))
        val newLamTypes = renameLamTypes(lams, valueRen)
        JVM.Tm.JoinRec(
          y,
          newLamTypes,
          go(removeLams(ty, v), false)(using ren = valueRen),
          go(b, tail)(using ren = ren + (x -> JoinPoint(y)))
        )

      case Tm.LetRec(x, _, ty, v, b) if shouldNotBeLifted(toplevel, x, b) =>
        val newbody = removeLams(ty, v)
        given Ren = renToplevel(
          lamTypes(v),
          toplevel.get,
          ren + (x -> LiftedFun(currentDef._1, currentDef._2, Nil))
        )
        go(newbody, tail)
      case Tm.LetRec(x, _, ty, v, b) =>
        val freeps = free(v).filterNot((y, _) => x == y)
        val y = emit.emit { y =>
          val freen = freeps.size
          val ps = freeps.map((x, ty) =>
            (x, goCTy(ty))
          ) ++ ty.params.zipWithIndex.map((ty, x) => (x + freen, goVTy(ty)))
          given Supply = new Supply(0)
          given ren: Ren =
            renLifted(freeps ++ lamTypes(v)) + (x -> LiftedFun(
              currentDef._1,
              y,
              freeps
            ))
          given Name = y
          val body = go(removeLams(ty, v), true)
          JVM.Def.Function(JVM.Access.Synth, y, ps, goVTy(ty.ret), body)
        }
        go(b, tail)(using
          ren = ren + (x -> LiftedFun(currentDef._1, y, freeps))
        )

      case Tm.Case(_, dty, s, cs) =>
        def goCases(cs: Cases): JVM.Cases =
          cs match
            case Cases.Empty        => JVM.Cases.Empty
            case Cases.Otherwise(b) => JVM.Cases.Otherwise(go(b, tail))
            case Cases.Ext(cx, ps, b, r) =>
              @tailrec
              def goParamsRec(
                  ps: List[(LocalName, VTy, Int)],
                  newps: List[(LocalName, JVM.Ty, Int)],
                  ren: Ren
              ): (List[(LocalName, JVM.Ty, Int)], Ren) =
                ps match
                  case Nil => (newps, ren)
                  case (x, ty, u) :: rest =>
                    val y = supply.next()
                    goParamsRec(
                      rest,
                      newps :+ (y, goVTy(ty), u),
                      ren + (x -> RenVar(y))
                    )
              inline def goParams(
                  ps: List[(LocalName, VTy, Int)]
              )(using ren: Ren): (List[(LocalName, JVM.Ty, Int)], Ren) =
                goParamsRec(ps, Nil, ren)
              val (newps, innerren) = goParams(ps)
              val newb = go(b, tail)(using innerren)
              JVM.Cases.Ext(cx, newps, newb, goCases(r))
        val (mdx, dx) = goData(dty)
        JVM.Tm.Case(mdx, dx, go(s, false), goCases(cs))

  @tailrec
  private def renLifted(ps: List[(Int, CTy)], ren: Ren = Map.empty)(using
      supply: Supply
  ): Ren =
    ps match
      case Nil            => ren
      case (i, _) :: rest => renLifted(rest, ren + (i -> RenVar(supply.next())))

  private def lamTypes(tm: Tm): List[(Int, CTy)] =
    tm match
      case Tm.Lam(x, _, ty, b) => (x, CTy(ty)) :: lamTypes(b)
      case _                   => Nil

  private def renameLamTypes(
      ps: List[(Int, CTy)],
      ren: Ren
  ): List[(Int, JVM.Ty)] =
    ps.map { (x, ty) =>
      ren(x) match
        case RenVar(y) => (y, goCTy(ty))
        case _         => impossible()
    }

  @tailrec
  private def renToplevel(
      lams: List[(Int, CTy)],
      top: List[(Int, CTy)],
      ren: Ren
  ): Ren =
    (lams, top) match
      case ((x, _) :: rest1, (y, _) :: rest2) =>
        renToplevel(rest1, rest2, ren + (x -> RenVar(y)))
      case (Nil, Nil) => ren
      case _          => impossible()

  private def shouldNotBeLifted(
      toplevel: Option[List[(Int, CTy)]],
      x: LocalName,
      body: Tm
  ): Boolean =
    toplevel match
      case Some(ps) =>
        body match
          case Tm.Local(y, _) => x == y
          case Tm.App(_, _) =>
            val (f, args) = body.flattenApps
            f match
              case Tm.Local(y, _) if x == y && args.size == ps.size =>
                ps.zip(args).forall {
                  case ((x, _), Tm.Local(y, _)) => x == y
                  case _                        => false
                }
              case _ => false
          case _ => false
      case _ => false

  private inline def goCTy(t: CTy): JVM.Ty =
    if t.params.nonEmpty then impossible() else goVTy(t.ret)

  private def goVTy(t: VTy): JVM.Ty =
    t match
      case VTy.Bool             => JVM.Ty.Bool
      case VTy.Int              => JVM.Ty.Int
      case VTy.Data(m, x, args) => monomorphize(m, x, args)
      case VTy.Record(fs)       => monomorphizeRec(fs)

  private def goData(dty: VTy): (Name, Name) =
    goVTy(dty) match
      case JVM.Ty.Data(m, dx) => (m, dx)
      case _                  => impossible()

  private def removeLams(ty: CTy, t: Tm): Tm =
    @tailrec
    def go(n: Int, t: Tm): Tm =
      (n, t) match
        case (n, Tm.Lam(_, _, _, b)) if n > 0 => go(n - 1, b)
        case (0, tm)                          => tm
        case _                                => impossible()
    go(ty.params.size, t)

  private def free(t: Tm): List[(LocalName, CTy)] =
    def merge(
        a: List[(LocalName, CTy)],
        b: List[(LocalName, CTy)]
    ): List[(LocalName, CTy)] =
      (a, b) match
        case (Nil, b)                                         => b
        case (a, Nil)                                         => a
        case (a, (x, ty) :: tl) if a.exists((y, _) => x == y) => merge(a, tl)
        case (a, e :: tl) => merge(a ++ List(e), tl)
    def remove(
        x: LocalName,
        a: List[(LocalName, CTy)]
    ): List[(LocalName, CTy)] =
      a.filterNot((y, _) => x == y)
    t match
      case Tm.Global(_, _, _) => Nil
      case Tm.Prim(_)         => Nil
      case Tm.BoolLit(_)      => Nil
      case Tm.IntLit(_)       => Nil

      case Tm.Local(ix, ty) => List(ix -> ty)

      case Tm.App(f, a)      => merge(free(f), free(a))
      case Tm.If(_, c, t, f) => merge(free(c), merge(free(t), free(f)))

      case Tm.Select(_, s, _) => free(s)

      case Tm.Lam(x, _, _, b) => remove(x, free(b))

      case Tm.ReturnIO(_, v) => free(v)

      case Tm.Let(x, _, _, v, b) => merge(free(v), remove(x, free(b)))
      case Tm.LetRec(x, _, _, v, b) =>
        merge(remove(x, free(v)), remove(x, free(b)))
      case Tm.BindIO(x, _, _, v, b) => merge(free(v), remove(x, free(b)))

      case Tm.Con(_, _, _, _, _, args) =>
        args.map(free).foldLeft(Nil)(merge)
      case Tm.Record(_, args) =>
        args.map(free).foldLeft(Nil)(merge)

      case Tm.Case(_, _, s, cs) =>
        def go(cs: Cases): List[(LocalName, CTy)] =
          cs match
            case Cases.Empty        => Nil
            case Cases.Otherwise(b) => free(b)
            case Cases.Ext(_, ps, b, r) =>
              merge(
                ps.foldLeft(free(b)) { case (f, (x, _, _)) => remove(x, f) },
                go(r)
              )
        merge(free(s), go(cs))

  private def isUsedInTailOnly(x: LocalName, tail: Boolean, t: Tm): Boolean =
    t match
      case Tm.Global(_, _, _) => true
      case Tm.Prim(_)         => true
      case Tm.BoolLit(_)      => true
      case Tm.IntLit(_)       => true

      case Tm.Lam(_, _, _, b) => isUsedInTailOnly(x, tail, b)

      case Tm.ReturnIO(_, v) => isUsedInTailOnly(x, tail, v)

      case Tm.Let(_, _, _, v, b) =>
        isUsedInTailOnly(x, false, v) && isUsedInTailOnly(x, tail, b)
      case Tm.LetRec(_, _, ty, v, b) =>
        isUsedInTailOnly(x, false, v) && isUsedInTailOnly(x, tail, b)
      case Tm.BindIO(_, _, ty, v, b) =>
        isUsedInTailOnly(x, false, v) && isUsedInTailOnly(x, tail, b)

      case Tm.If(_, c, t, f) =>
        isUsedInTailOnly(x, false, c) &&
        isUsedInTailOnly(x, tail, t) &&
        isUsedInTailOnly(x, tail, f)
      case Tm.Con(_, _, _, _, _, args) =>
        args.forall(isUsedInTailOnly(x, false, _))
      case Tm.Record(_, args) =>
        args.forall(isUsedInTailOnly(x, false, _))

      case Tm.Select(_, s, _) => isUsedInTailOnly(x, false, s)

      case Tm.Local(y, ty) => if x == y then tail else true

      case Tm.App(_, _) =>
        val (fn, args) = t.flattenApps
        val safeInArgs = args.forall(isUsedInTailOnly(x, false, _))
        fn match
          case Tm.Local(y, ty) if x == y => tail && safeInArgs
          case fn => safeInArgs && isUsedInTailOnly(x, tail, fn)

      case Tm.Case(_, _, s, cs) =>
        @tailrec
        def go(cs: Cases): Boolean =
          cs match
            case Cases.Empty           => true
            case Cases.Otherwise(b)    => isUsedInTailOnly(x, tail, b)
            case Cases.Ext(_, _, b, r) => isUsedInTailOnly(x, tail, b) && go(r)
        isUsedInTailOnly(x, false, s) && go(cs)

  // monomorphization
  private var currentModule: Name = null
  private val newDefs = mutable.ArrayBuffer.empty[JVM.Def]

  private type MonoKey = (Name, Name, List[IR.VTy])
  private type MonoRecKey = List[IR.VTy]
  private val monoStore = mutable.Map.empty[MonoKey, Name]
  private val monoRecStore = mutable.Map.empty[MonoRecKey, Name]

  private def monomorphize(m: Name, dx: Name, ps: List[IR.VTy]): JVM.Ty =
    val (pub, xs) = State.getGlobalDirect(m, dx) match
      case Some(GlobalEntry.Data0(pub, _, _, xs, _, _, _, _)) => (pub, xs)
      case _                                                  => impossible()
    val (nx, alreadyDone) = tryMonomorphize(m, dx, ps)
    if !alreadyDone then
      val menv: State.MonoEnv =
        ps.zipWithIndex.map((ty, i) => (mkLvl(i), ty)).toMap
      val ecs = xs.map { cx =>
        val ets =
          State
            .getMonoConParams(m, dx, cx, menv)
            .map((x, ty) => (x.toOption, goVTy(ty)))
        val acc =
          if State.checkAccessibility(m, cx) then JVM.Access.Pub
          else JVM.Access.Priv
        JVM.Constructor(acc, cx, ets)
      }
      val acc = if pub then JVM.Access.Pub else JVM.Access.Priv
      newDefs += JVM.Def.Data(acc, nx, ecs)
    JVM.Ty.Data(currentModule, nx)

  private def tryMonomorphize(
      mod: Name,
      name: Name,
      ps: List[IR.VTy]
  ): (Name, Boolean) =
    val k = (mod, name, ps)
    monoStore.get(k) match
      case Some(x) => (x, true)
      case None =>
        val x = createName(name, ps)
        monoStore += k -> x
        (x, false)

  private def monomorphizeRec(fs: AssocBind[VTy]): JVM.Ty =
    val (nx, alreadyDone) = tryMonomorphizeRec(fs.map((_, t) => t))
    if !alreadyDone then
      val con = JVM.Constructor(
        JVM.Access.Pub,
        JVM.RecordConName,
        fs.map((x, t) => (x.toOption, goVTy(t)))
      )
      newDefs += JVM.Def.Data(JVM.Access.Pub, nx, List(con))
    JVM.Ty.Data(currentModule, nx)

  private def tryMonomorphizeRec(ps: List[IR.VTy]): (Name, Boolean) =
    monoRecStore.get(ps) match
      case Some(x) => (x, true)
      case None =>
        val x = createName(Name("anonrec"), ps)
        monoRecStore += ps -> x
        (x, false)

  private def createName(name: Name, ps: List[IR.VTy]): Name =
    def paramStr(p: IR.VTy): String = p match
      case VTy.Bool            => "Bool"
      case VTy.Int             => "Int"
      case VTy.Data(m, x, Nil) => s"$m$$$x"
      case VTy.Data(m, x, args) =>
        s"$m$$${x}_${args.map(paramStr).mkString("_")}"
      case VTy.Record(fs) =>
        s"anonrec_${fs.map((_, t) => paramStr(t)).mkString("_")}"
    if ps.isEmpty then name
    else Name(s"${name}_${ps.map(paramStr).mkString("_")}")
     */
