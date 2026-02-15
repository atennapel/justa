import Common.*
import IR.*
import Debug.debug

import scala.collection.mutable
import scala.annotation.tailrec
import State.GlobalEntry

// lift out local functions, create join points, rename with unique names
object Lifting:
  // the passed definitions should be simplified!
  def liftModules(mods: List[Module]): List[JVM.Module] =
    mods.map(liftModule)

  private def defSame(a: JVM.Def, b: JVM.Def): Boolean =
    (a, b) match
      case (JVM.Def.Value(_, _, t1, v1), JVM.Def.Value(_, _, t2, v2)) =>
        t1 == t2 && v1 == v2
      case (
            JVM.Def.Function(_, _, p1, r1, v1),
            JVM.Def.Function(_, _, p2, r2, v2)
          ) =>
        p1 == p2 && r1 == r2 && v1 == v2
      case _ => impossible()

  private final case class Globals(
      shapes: mutable.Map[(Name, Name), Shape],
      defs: mutable.ArrayBuffer[JVM.Def],
      renames: mutable.Map[Name, Name]
  ):
    inline def get(m: Name, x: Name): Option[Shape] = shapes.get((m, x))
    inline def apply(m: Name, x: Name): Shape = shapes((m, x))
    inline def addShape(m: Name, x: Name, s: Shape): Unit =
      shapes += ((m, x) -> s)
    inline def getName(x: Name): Name = renames.get(x).getOrElse(x)
    inline def addDef(d: JVM.Def): Boolean =
      if d.isData || !d.isSynth then false
      else
        defs.find(defSame(_, d)) match
          case Some(d2) =>
            renames += d.name -> d2.name
            false
          case None =>
            defs += d
            true

  private object Globals:
    def empty: Globals =
      Globals(mutable.Map.empty, mutable.ArrayBuffer.empty, mutable.Map.empty)

  private def liftModule(mod: Module): JVM.Module =
    currentModule = mod.name
    monoStore.clear()
    monoRecStore.clear()
    given Globals = Globals.empty
    val ds = liftDefs(mod.name, mod.defs)
    JVM.Module(mod.name, removeUnused(ds.toList))

  private def removeUnused(ds: List[JVM.Def]): JVM.Defs =
    inline def strip(s: mutable.Set[(Name, Name)]) =
      s.toList.filter((m, _) => m == currentModule).map((_, x) => x).toSet
    inline def usages(ds: List[JVM.Def]): Set[Name] =
      val static = mutable.Set.empty[(Name, Name)]
      ds.foreach(_.globals(static))
      strip(static)
    def grow(
        forsure: List[JVM.Def],
        maybe: List[JVM.Def],
        cur: Set[Name],
        prev: Set[Name]
    ): List[JVM.Def] =
      if maybe.map(_.name).toSet == prev then forsure
      else
        val u = usages(forsure)
        val (used, notused) = maybe.partition(d => u.contains(d.name))
        grow(forsure ++ used, notused, notused.map(_.name).toSet, cur)
    val (synth, nonsynth) = ds.partition(_.isSynth)
    if synth.isEmpty then JVM.Defs(nonsynth)
    else
      val eds = grow(nonsynth, synth, synth.map(_.name).toSet, Set.empty)
      JVM.Defs(eds)

  private def liftDefs(mod: Name, ds: Defs)(using globals: Globals): JVM.Defs =
    JVM.Defs(ds.toList.flatMap(d => liftDef(mod, d)))

  private type LiftedGlobals =
    mutable.Map[Name, (CTy, Tm, List[(LocalName, CTy)])]
  private type LiftedLocals = mutable.Map[LocalName, (CTy, Tm)]

  private final class Supply(var id: LocalName = 0):
    def next(): LocalName =
      val cur = id
      id += 1
      cur

  private final class Emit(
      defs: mutable.ArrayBuffer[JVM.Def] = mutable.ArrayBuffer.empty
  ):
    inline def get: List[JVM.Def] = defs.toList
    inline def add(d: JVM.Def): Unit = defs += d

  private type Ren = Map[LocalName, RenEntry]
  private enum RenEntry:
    case RenVar(name: LocalName)
    case JoinPoint(name: LocalName)
    case LiftedFun(mod: Name, name: Name, extraArgs: List[(LocalName, CTy)])
    case LiftedRec(rec: Shape)

    def isLifted: Boolean = this match
      case RenVar(_)          => false
      case JoinPoint(_)       => true
      case LiftedFun(_, _, _) => true
      case LiftedRec(_)       => true
  import RenEntry.*

  private case class Ctx(
      mod: Name,
      defname: Name,
      supply: Supply,
      emit: Emit,
      ren: Ren
  ):
    inline def fresh(): LocalName = supply.next()
    inline def addRen(x: LocalName, y: LocalName): Ctx =
      Ctx(mod, defname, supply, emit, ren + (x -> RenVar(y)))
    inline def addFresh(x: LocalName): (Ctx, LocalName) =
      val y = supply.next()
      (addRen(x, y), y)
    inline def addLiftedFun(
        x: LocalName,
        r: Name,
        extraArgs: List[(LocalName, CTy)]
    ): Ctx =
      Ctx(mod, defname, supply, emit, ren + (x -> LiftedFun(mod, r, extraArgs)))
    inline def addLiftedRec(x: LocalName, rec: Shape): Ctx =
      Ctx(mod, defname, supply, emit, ren + (x -> LiftedRec(rec)))
    inline def get(x: LocalName): RenEntry = ren(x)
    inline def has(x: LocalName): Boolean = ren.contains(x)
    inline def isLifted(x: LocalName): Boolean =
      ren.get(x) match
        case Some(e) => e.isLifted
        case None    => false
    inline def addDef(d: JVM.Def)(using g: Globals): Unit =
      if g.addDef(d) then emit.add(d)
  private object Ctx:
    def dummy: Ctx = Ctx(null, null, null, null, Map.empty)

  private enum Shape:
    case Rec(fs: List[(Option[Name], Shape)])
    case Global(mod: Name, x: Name, ty: CTy, extraArgs: List[(LocalName, CTy)])
    case Local(x: LocalName)

  private def liftDef(mod: Name, d: Def)(using
      globals: Globals
  ): List[JVM.Def] =
    debug(s"liftDef $mod.${d.name}")
    newDefs.clear()
    val lifted: LiftedGlobals = mutable.Map.empty
    val rec = liftCTy(mod, d.name, None, d.ty, d.value, lifted)(using Ctx.dummy)
    globals.addShape(mod, d.name, rec)
    lifted.toList.flatMap { case (x, (ty, tm, extraArgs)) =>
      if extraArgs.nonEmpty then impossible()
      val pub =
        if x == d.name then if d.pub then JVM.Access.Pub else JVM.Access.Priv
        else JVM.Access.Synth
      liftDefInner(mod, pub, x, ty, tm)
    }

  private def liftDefInner(
      mod: Name,
      acc: JVM.Access,
      x: Name,
      ty: CTy,
      tm: Tm
  )(using globals: Globals): List[JVM.Def] =
    val (_, vrty, io) = defTy(ty)
    val retty = goVTy(vrty)
    val emit = Emit()
    val startctx = Ctx(mod, x, Supply(), emit, Map.empty)
    val (ctx, ps, body) = removeLamsCtx(tm)(using startctx)
    val etm = go(body, true, Some(ps))(using ctx)
    val cdef =
      if ps.isEmpty && !io then JVM.Def.Value(acc, x, retty, etm)
      else
        val nps = ps.map((_, x, t) => (x, t))
        JVM.Def.Function(acc, x, nps, retty, etm)
    newDefs.toList ++ emit.get ++ List(cdef)

  private def defTy(ty: CTy): (List[VTy], VTy, Boolean) =
    ty match
      case CTy.Fun(pty, rty) =>
        val (ps, rt, io) = defTy(rty)
        (pty :: ps, rt, io)
      case CTy.IO(ty)  => (Nil, ty, true)
      case CTy.Val(ty) => (Nil, ty, false)
      case CTy.Rec(_)  => impossible()

  private def liftCTy(
      mod: Name,
      defname: Name,
      local: Option[LocalName],
      ty: CTy,
      tm: Tm,
      res: LiftedGlobals
  )(using ctx: Ctx): Shape =
    @tailrec
    def liftedName(
        defname: Name,
        x: Option[Name],
        res: LiftedGlobals,
        i: Int = -1
    ): Name =
      val y = x match
        case Some(x) => Name(s"$defname$$$x$$${if i == -1 then "" else i}")
        case None    => Name(s"$defname$$${i + 1}")
      if res.contains(y) then liftedName(defname, x, res, i + 1)
      else y
    (ty, tm) match
      case (CTy.Rec(ts), Tm.CRecord(fs)) =>
        Shape.Rec(fs.zip(ts).map { case (tm, (x, ty)) =>
          val y = liftedName(defname, x, res)
          (x, liftCTy(mod, y, local, ty, tm, res))
        })
      case _ =>
        val freeps = local match
          case None    => free(tm)
          case Some(x) => free(tm).filterNot((y, _) => x == y)
        val freeps2 = freeps.filterNot((y, _) => ctx.isLifted(y))
        res += (defname -> (ty, tm, freeps2))
        Shape.Global(mod, defname, ty, freeps2)

  private def liftCTyLocal(
      ty: CTy,
      tm: Tm,
      res: LiftedLocals
  )(using ctx: Ctx): Shape =
    (ty, tm) match
      case (CTy.Rec(ts), Tm.CRecord(fs)) =>
        Shape.Rec(fs.zip(ts).map { case (tm, (x, ty)) =>
          (x, liftCTyLocal(ty, tm, res))
        })
      case _ =>
        val x = ctx.fresh()
        res += (x -> (ty, tm))
        Shape.Local(x)

  // lifting
  private def go(
      tm: Tm,
      tail: Boolean,
      toplevel: Option[List[(LocalName, LocalName, JVM.Ty)]] = None
  )(using
      ctx: Ctx,
      globals: Globals
  ): JVM.Tm =
    tm match
      case Tm.Lam(_, _, _, _) => impossible()
      case Tm.CRecord(_)      => impossible()

      case Tm.BoolLit(v)   => JVM.Tm.bool(v)
      case Tm.IntLit(v)    => JVM.Tm.IntLit(v)
      case Tm.StringLit(v) => JVM.Tm.StringLit(v)
      case Tm.Prim(p)      => JVM.Tm.Prim(p, Nil)

      case Tm.Local(ix, ty) =>
        ctx.get(ix) match
          case RenVar(x)    => JVM.Tm.Local(x, goCTy(ty))
          case JoinPoint(x) => JVM.Tm.Jump(x, Nil)
          case _            => impossible()

      case Tm.Global(m, x, ty) =>
        val (ps, _, io) = defTy(ty)
        val (m2, x2) = getGlobal(m, x)
        if ps.nonEmpty then impossible()
        else if io then JVM.Tm.GlobalApp(m2, x2, Nil)
        else JVM.Tm.Global(m2, x2)

      case Tm.ReturnIO(_, v) => go(v, tail)
      case Tm.BindIO(x, _, ty, v, b) =>
        val (nctx, y) = ctx.addFresh(x)
        JVM.Tm.Let(y, goVTy(ty), go(v, false), go(b, tail)(using nctx))

      case Tm.If(_, c, t, f) =>
        JVM.Tm.If(go(c, false), go(t, tail), go(f, tail))
      case Tm.Con(m, _, cx, ix, dty, args) =>
        val (mdx, dx) = goData(dty)
        JVM.Tm.Con(mdx, dx, cx, ix, args.map((a, _) => go(a, false)))
      case Tm.Record(dty, args) =>
        val (mdx, dx) = goData(dty)
        JVM.Tm.Con(mdx, dx, JVM.RecordConName, 0, args.map(go(_, false)))
      case Tm.Select(_, dty, s, i) =>
        val (mdx, dx) = goData(dty)
        JVM.Tm.Select(mdx, dx, go(s, false), i)
      case Tm.Unsafe(rt, io, l, args) =>
        val ty = goVTy(rt)
        val eargs = args.map((a, t) => (go(a, false), goVTy(t)))
        JVM.Tm.Unsafe(ty, io, l, eargs)
      case Tm.UnsafeRunIO(_, tm) => JVM.Tm.UnsafeRunIO(go(tm, tail))

      case tm @ Tm.App(_, _, _) =>
        val (hd, tl) = tm.flattenCompElims
        goCompElims(hd, tl, tail)
      case tm @ Tm.CSelect(_, _) =>
        val (hd, tl) = tm.flattenCompElims
        goCompElims(hd, tl, tail)

      case Tm.Let(x, _, ty, v, b) if tail && isUsedInTailOnly(x, true, b) =>
        val lifted: LiftedLocals = mutable.Map.empty
        val rec = liftCTyLocal(ty, v, lifted)
        val blocks = lifted.toList.map { case (y, (ty, tm)) =>
          val (lps, v) = removeLams(tm)
          val (innerctx, ps) = renameParams(lps.map((x, t) => (x, CTy(t))))
          val etm = go(v, true)(using innerctx)
          (y, ps, etm)
        }
        val body = go(b, tail)(using ctx.addLiftedRec(x, rec))
        JVM.Tm.Join(blocks, body)

      case Tm.Let(x, _, ty, v, b) =>
        matchVTy(ty) match
          case Some(vty) =>
            val (nctx, y) = ctx.addFresh(x)
            JVM.Tm.Let(y, goVTy(vty), go(v, false), go(b, tail)(using nctx))
          case None =>
            val lifted: LiftedGlobals = mutable.Map.empty
            val name = Name(s"${ctx.defname}$$let$x")
            val rec = liftCTy(ctx.mod, name, None, ty, v, lifted)
            lifted.foreach { case (y, (ty, tm, freeps)) =>
              val (_, vrty, io) = defTy(ty)
              val retty = goVTy(vrty)
              val ren = ctx.ren.filter((_, e) => e.isLifted)
              val startctx = Ctx(ctx.mod, y, Supply(), ctx.emit, ren)
              val (lps, body) = removeLams(tm)
              val (innerctx, ps) = renameParams(
                freeps.map((x, t) => (x, t)) ++ lps.map((x, t) => (x, CTy(t)))
              )(using startctx)
              val etm = go(body, true)(using innerctx)
              val cdef =
                if ps.isEmpty && !io then
                  JVM.Def.Value(JVM.Access.Synth, y, retty, etm)
                else JVM.Def.Function(JVM.Access.Synth, y, ps, retty, etm)
              ctx.addDef(cdef)
            }
            go(b, tail)(using ctx.addLiftedRec(x, rec))

      case Tm.LetRec(x, _, ty, v, b)
          if tail && isUsedInTailOnly(x, true, v) &&
            isUsedInTailOnly(x, true, b) =>
        val lifted: LiftedLocals = mutable.Map.empty
        val rec = liftCTyLocal(ty, v, lifted)
        val blocks = lifted.toList.map { case (y, (ty, tm)) =>
          val (lps, v) = removeLams(tm)
          val (innerctx, ps) = renameParams(lps.map((x, t) => (x, CTy(t))))
          val etm = go(v, true)(using innerctx.addLiftedRec(x, rec))
          (y, ps, etm)
        }
        val body = go(b, tail)(using ctx.addLiftedRec(x, rec))
        JVM.Tm.Join(blocks, body)

      case Tm.LetRec(x, _, ty, v, b) if shouldNotBeLifted(toplevel, x, b) =>
        val (ps, newbody) = removeLams(v)
        val nctx = ps.zip(toplevel.get).foldLeft(ctx) {
          case (ctx, ((x, _), (_, y, _))) => ctx.addRen(x, y)
        }
        go(newbody, tail)(using nctx.addLiftedFun(x, ctx.defname, Nil))

      case Tm.LetRec(x, _, ty, v, b) =>
        val lifted: LiftedGlobals = mutable.Map.empty
        val name = Name(s"${ctx.defname}$$letrec$x")
        val rec = liftCTy(ctx.mod, name, Some(x), ty, v, lifted)
        lifted.foreach { case (y, (ty, tm, freeps)) =>
          val (_, vrty, io) = defTy(ty)
          val retty = goVTy(vrty)
          val ren = ctx.ren.filter((_, e) => e.isLifted)
          val startctx = Ctx(ctx.mod, y, Supply(), ctx.emit, ren)
          val (lps, body) = removeLams(tm)
          val (innerctx, ps) = renameParams(
            freeps.map((x, t) => (x, t)) ++ lps.map((x, t) => (x, CTy(t)))
          )(using startctx)
          val etm = go(body, true)(using innerctx.addLiftedRec(x, rec))
          val cdef =
            if ps.isEmpty && !io then
              JVM.Def.Value(JVM.Access.Synth, y, retty, etm)
            else JVM.Def.Function(JVM.Access.Synth, y, ps, retty, etm)
          ctx.addDef(cdef)
        }
        go(b, tail)(using ctx.addLiftedRec(x, rec))

      case Tm.Case(_, dty, s, cs) =>
        def goCases(cs: Cases): JVM.Cases =
          cs match
            case Cases.Empty        => JVM.Cases.Empty
            case Cases.Otherwise(b) => JVM.Cases.Otherwise(go(b, tail))
            case Cases.Ext(cx, ps, b, r) =>
              @tailrec
              def goParams(
                  ps: List[(LocalName, VTy, Int)],
                  newps: List[(LocalName, JVM.Ty, Int)],
                  ctx: Ctx
              ): (List[(LocalName, JVM.Ty, Int)], Ctx) =
                ps match
                  case Nil => (newps, ctx)
                  case (x, ty, u) :: rest =>
                    val (nctx, y) = ctx.addFresh(x)
                    goParams(rest, newps :+ (y, goVTy(ty), u), nctx)
              val (newps, nctx) = goParams(ps, Nil, ctx)
              val newb = go(b, tail)(using nctx)
              JVM.Cases.Ext(cx, newps, newb, goCases(r))
        val (mdx, dx) = goData(dty)
        JVM.Tm.Case(mdx, dx, go(s, false), goCases(cs))

  private def goCompElims(hd: Tm, tl: List[Either[Int, Tm]], tail: Boolean)(
      using
      ctx: Ctx,
      globals: Globals
  ): JVM.Tm =
    def a = tl.map {
      case Left(_)  => ??? // TODO: handle comp projections
      case Right(a) => a
    }
    hd match
      case Tm.Global(m, x, _) =>
        val (g, a) = reduceCompElims(globals(m, x), tl)
        g match
          case Shape.Global(m, x, _, args) =>
            val extraArgs = args.map((x, ty) => go(Tm.Local(x, ty), false))
            val (m2, x2) = getGlobal(m, x)
            JVM.Tm.GlobalApp(m2, x2, extraArgs ++ a.map(a => go(a, false)))
          case _ => impossible()
      case Tm.Prim(p) => JVM.Tm.Prim(p, a.map(a => go(a, false)))
      case Tm.Local(ix, ty) =>
        ctx.get(ix) match
          case RenVar(x)    => impossible()
          case JoinPoint(x) => JVM.Tm.Jump(x, a.map(a => go(a, false)))
          case LiftedFun(m, x, args) =>
            val extraArgs = args.map((x, ty) => go(Tm.Local(x, ty), false))
            val (m2, x2) = getGlobal(m, x)
            JVM.Tm.GlobalApp(m2, x2, extraArgs ++ a.map(a => go(a, false)))
          case LiftedRec(rec) =>
            val (g, a) = reduceCompElims(rec, tl)
            g match
              case Shape.Global(m, x, _, args) =>
                val extraArgs = args.map((x, ty) => go(Tm.Local(x, ty), false))
                val (m2, x2) = getGlobal(m, x)
                JVM.Tm.GlobalApp(m2, x2, extraArgs ++ a.map(a => go(a, false)))
              case Shape.Local(x) =>
                JVM.Tm.Jump(x, a.map(a => go(a, false)))
              case _ => impossible()
      case _ => impossible()

  private def reduceCompElims(
      shape: Shape,
      es: List[Either[Int, Tm]]
  ): (Shape, List[Tm]) =
    (shape, es) match
      case (Shape.Rec(fs), Left(i) :: rest) =>
        reduceCompElims(fs(i)._2, rest)
      case _ =>
        val a = es.map {
          case Left(_)  => ??? // TODO: handle comp projections
          case Right(a) => a
        }
        (shape, a)

  // util
  private def getGlobal(m: Name, x: Name)(using
      globals: Globals
  ): (Name, Name) =
    if m == currentModule then (m, globals.getName(x))
    else (m, x)

  private def removeLamsCtx(tm: Tm)(using
      ctx: Ctx
  ): (Ctx, List[(LocalName, LocalName, JVM.Ty)], Tm) =
    tm match
      case Tm.Lam(x, _, ty, b) =>
        val (nctx, y) = ctx.addFresh(x)
        val (rctx, ps, body) = removeLamsCtx(b)(using nctx)
        (rctx, (x, y, goVTy(ty)) :: ps, body)
      case tm => (ctx, Nil, tm)

  private def removeLams(tm: Tm): (List[(LocalName, VTy)], Tm) =
    tm match
      case Tm.Lam(x, _, ty, b) =>
        val (ps, body) = removeLams(b)
        ((x, ty) :: ps, body)
      case tm => (Nil, tm)

  private def renameParams(ps: List[(LocalName, CTy)])(using
      ctx: Ctx
  ): (Ctx, List[(LocalName, JVM.Ty)]) =
    ps match
      case Nil => (ctx, Nil)
      case (x, ty) :: ps =>
        matchVTy(ty) match
          case None => impossible()
          case Some(vty) =>
            val (nctx, y) = ctx.addFresh(x)
            val (rctx, rps) = renameParams(ps)(using nctx)
            (rctx, (y, goVTy(vty)) :: rps)

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
      case Tm.StringLit(_)    => Nil

      case Tm.Local(ix, ty) => List(ix -> ty)

      case Tm.App(f, a, _)   => merge(free(f), free(a))
      case Tm.If(_, c, t, f) => merge(free(c), merge(free(t), free(f)))

      case Tm.Select(_, _, s, _) => free(s)
      case Tm.CSelect(s, _)      => free(s)

      case Tm.Lam(x, _, _, b) => remove(x, free(b))

      case Tm.ReturnIO(_, v) => free(v)

      case Tm.Let(x, _, _, v, b) => merge(free(v), remove(x, free(b)))
      case Tm.LetRec(x, _, _, v, b) =>
        merge(remove(x, free(v)), remove(x, free(b)))
      case Tm.BindIO(x, _, _, v, b) => merge(free(v), remove(x, free(b)))

      case Tm.Con(_, _, _, _, _, args) =>
        args.map((a, _) => free(a)).foldLeft(Nil)(merge)
      case Tm.Record(_, args) =>
        args.map(free).foldLeft(Nil)(merge)
      case Tm.CRecord(args) =>
        args.map(free).foldLeft(Nil)(merge)
      case Tm.Unsafe(_, _, _, args) =>
        args.map((a, _) => free(a)).foldLeft(Nil)(merge)
      case Tm.UnsafeRunIO(_, tm) => free(tm)

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

  private def shouldNotBeLifted(
      toplevel: Option[List[(LocalName, LocalName, JVM.Ty)]],
      x: LocalName,
      body: Tm
  ): Boolean =
    toplevel match
      case Some(ps) =>
        body match
          case Tm.Local(y, _) => x == y
          case Tm.App(_, _, _) =>
            val (f, args) = body.flattenApps
            f match
              case Tm.Local(y, _) if x == y && args.size == ps.size =>
                ps.zip(args).forall {
                  case ((x, _, _), Tm.Local(y, _)) => x == y
                  case _                           => false
                }
              case _ => false
          case _ => false
      case _ => false

  private def isUsedInTailOnly(x: LocalName, tail: Boolean, t: Tm): Boolean =
    t match
      case Tm.Global(_, _, _) => true
      case Tm.Prim(_)         => true
      case Tm.BoolLit(_)      => true
      case Tm.IntLit(_)       => true
      case Tm.StringLit(_)    => true

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
        args.forall((a, _) => isUsedInTailOnly(x, false, a))
      case Tm.Record(_, args) =>
        args.forall(isUsedInTailOnly(x, false, _))
      case Tm.Unsafe(_, _, _, args) =>
        args.forall((a, _) => isUsedInTailOnly(x, false, a))
      case Tm.UnsafeRunIO(_, tm) => isUsedInTailOnly(x, tail, tm)

      case Tm.Select(_, _, s, _) => isUsedInTailOnly(x, false, s)

      case Tm.Local(y, ty) => if x == y then tail else true

      case Tm.App(_, _, _) =>
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

      case Tm.CRecord(fs)   => fs.forall(isUsedInTailOnly(x, tail, _))
      case Tm.CSelect(s, _) => isUsedInTailOnly(x, tail, s)

  // types
  private inline def goCTy(t: CTy): JVM.Ty =
    t match
      case CTy.Val(ty) => goVTy(ty)
      case _           => impossible()

  private def goVTy(t: VTy): JVM.Ty =
    t match
      case VTy.Void             => JVM.Ty.Void
      case VTy.Bool             => JVM.Ty.Bool
      case VTy.Int              => JVM.Ty.Int
      case VTy.Class(x)         => JVM.Ty.Class(x)
      case VTy.Array(ty)        => JVM.Ty.Array(goVTy(ty))
      case VTy.Data(m, x, args) => monomorphize(m, x, args)
      case VTy.Record(fs)       => monomorphizeRec(fs)

  private def goData(dty: VTy): (Name, Name) =
    goVTy(dty) match
      case JVM.Ty.Data(m, dx) => (m, dx)
      case _                  => impossible()

  private def matchVTy(t: CTy): Option[VTy] =
    t match
      case CTy.Val(ty) => Some(ty)
      case _           => None

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
      case VTy.Void            => "Void"
      case VTy.Bool            => "Bool"
      case VTy.Int             => "Int"
      case VTy.Class(x)        => x.replace(".", "_")
      case VTy.Array(ty)       => s"Array_${paramStr(ty)}"
      case VTy.Data(m, x, Nil) => s"$m$$$x"
      case VTy.Data(m, x, args) =>
        s"$m$$${x}_${args.map(paramStr).mkString("_")}"
      case VTy.Record(fs) =>
        s"anonrec_${fs.map((_, t) => paramStr(t)).mkString("_")}"
    if ps.isEmpty then name
    else Name(s"${name}_${ps.map(paramStr).mkString("_")}")
