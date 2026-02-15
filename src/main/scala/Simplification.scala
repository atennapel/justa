import Common.{impossible, Name, RuntimePrimitive}
import IR.*
import Debug.debug

import scala.annotation.tailrec

// eta-expand, remove dead lets, inlining, constant folding, remove closures
object Simplification:
  def simplifyModules(m: List[Module]): List[Module] =
    m.map(simplifyModule)

  private def simplifyModule(m: Module): Module =
    Module(m.name, simplifyDefs(m.defs))

  private def simplifyDefs(ds: Defs): Defs =
    Defs(ds.toList.map(simplifyDef))

  private type Scope = Set[LocalName]
  private type Subst = Map[LocalName, Tm]

  private def simplifyDef(d: Def): Def =
    debug(s"simplifyDef ${d.name}")
    val simp = correctUsages(simplify(d.ty, d.value))
    Def(d.pub, d.name, d.ty, simp)

  @tailrec
  private def simplify(ty: CTy, t: Tm): Tm =
    debug(s"simplify $t")
    val next = go(ty, correctUsages(t), Nil)(using Ctx.empty)
    if next == t then t else simplify(ty, next)

  private enum Elim derives CanEqual:
    case Arg(tm: Tm, ty: VTy)
    case CSelect(ix: Int)

    def isArg: Boolean =
      this match
        case Arg(_, _) => true
        case _         => false

    def getArg: Tm =
      this match
        case Arg(a, _) => a
        case _         => impossible()

  private object Elim:
    def apply(head: Tm, arg: Elim): Tm =
      arg match
        case Arg(tm, ty) => Tm.App(head, tm, ty)
        case CSelect(i)  => Tm.CSelect(head, i)

  private def reduce(ty: CTy, args: List[Elim]): CTy =
    (ty, args) match
      case (ty, Nil)                               => ty
      case (CTy.Rec(fs), Elim.CSelect(i) :: args)  => reduce(fs(i)._2, args)
      case (CTy.Fun(_, b), Elim.Arg(_, _) :: args) => reduce(b, args)
      case _                                       => impossible()

  private inline def apply(tm: Tm, args: List[Elim]): Tm =
    args.foldLeft(tm)(Elim.apply)

  private final case class Ctx(
      scope: Scope,
      subst: Subst,
      nextFresh: LocalName
  ):
    inline def contains(x: LocalName): Boolean = scope.contains(x)

    @tailrec
    private def fresh(x: LocalName = nextFresh): LocalName =
      if contains(x) then fresh(x + 1) else x

    inline def get(x: LocalName): Option[Tm] = subst.get(x)
    inline def assign(x: LocalName, v: Tm): Ctx =
      Ctx(scope, subst + (x -> v), nextFresh)

    inline def used(x: LocalName, ty: CTy): (Ctx, LocalName) =
      val y = fresh()
      (Ctx(scope + y, subst + (x -> Tm.Local(y, ty)), y + 1), y)
    inline def used(x: LocalName, ty: VTy): (Ctx, LocalName) =
      used(x, CTy(ty))
    inline def notused(x: LocalName): Ctx =
      Ctx(scope + x, subst - x, nextFresh + 1)

    inline def enter(x: LocalName, ty: CTy): (LocalName, Ctx) =
      if contains(x) then
        val (nctx, y) = used(x, ty)
        (y, nctx)
      else (x, notused(x))

    inline def enter(
        x: LocalName,
        ty: CTy,
        inline body: Ctx ?=> Tm
    ): (LocalName, Tm) =
      val (y, nctx) = enter(x, ty)
      val b = body(using nctx)
      (y, b)
    inline def enter(
        x: LocalName,
        ty: VTy,
        inline body: Ctx ?=> Tm
    ): (LocalName, Tm) = enter(x, CTy(ty), ctx ?=> body)
    inline def insert(ty: CTy, inline body: Ctx ?=> Tm => Tm): (LocalName, Tm) =
      val x = fresh()
      val b = body(using notused(x))(Tm.Local(x, ty))
      (x, b)
    inline def insert(ty: VTy, inline body: Ctx ?=> Tm => Tm): (LocalName, Tm) =
      insert(CTy(ty), ctx ?=> body)
  private object Ctx:
    val empty: Ctx = Ctx(Set.empty, Map.empty, 0)

  private def go(ty: CTy, tm: Tm, args: List[Elim])(using ctx: Ctx): Tm =
    (ty, tm) match
      // eta-expansion
      case (CTy.Fun(_, rty), Tm.Lam(x, _, ty, b0)) if args.isEmpty =>
        val (y, b) = ctx.enter(x, ty, ctx ?=> go(rty, b0, Nil))
        Tm.Lam(y, -1, ty, b)
      case (CTy.Fun(pty, rty), tm) =>
        val (x, b) =
          ctx.insert(
            pty,
            ctx ?=> (vr: Tm) => go(rty, tm, args :+ Elim.Arg(vr, pty))
          )
        Tm.Lam(x, -1, pty, b)

      case (CTy.Rec(fs), Tm.CRecord(vs)) if args.isEmpty =>
        val vs2 = fs.zip(vs).map { case ((_, ty), tm) => go(ty, tm, Nil) }
        Tm.CRecord(vs2)
      case (CTy.Rec(fs), tm) =>
        val vs = fs.zipWithIndex.map { case ((_, ty), i) =>
          go(ty, tm, args :+ Elim.CSelect(i))
        }
        Tm.CRecord(vs)

      // other simplifications
      case (_, tm) =>
        tm match
          case Tm.BoolLit(v)   => tm
          case Tm.IntLit(v)    => tm
          case Tm.StringLit(v) => tm

          case Tm.Global(_, _, _) => apply(tm, args)

          case Tm.ReturnIO(vty, v) => Tm.ReturnIO(vty, go(CTy(vty), v, Nil))
          case Tm.Con(m, dx, cx, ix, dty, args) =>
            Tm.Con(
              m,
              dx,
              cx,
              ix,
              dty,
              args.map((a, vt) => (go(CTy(vt), a, Nil), vt))
            )
          case Tm.Record(ty, args) =>
            ty match
              case VTy.Record(ts) =>
                val eargs =
                  ts.zip(args).map { case ((_, vty), a) =>
                    go(CTy(vty), a, Nil)
                  }
                Tm.Record(ty, eargs)
              case _ => impossible()

          case Tm.Prim(p) =>
            if args.size == 2 && args.forall(_.isArg) then
              foldConstants2(p, args(0).getArg, args(1).getArg) match
                case Some(tm) => tm
                case None     => apply(tm, args)
            else apply(tm, args)

          case Tm.Local(x, _) =>
            ctx.get(x) match
              case Some(tm) => apply(tm, args)
              case None     => apply(tm, args)

          case Tm.App(f, a, aty) =>
            go(ty, f, Elim.Arg(go(CTy(aty), a, Nil), aty) :: args)

          case Tm.CSelect(s, i) => go(ty, s, Elim.CSelect(i) :: args)

          case Tm.Lam(x, u, vty, b) if args.nonEmpty =>
            go(ty, Tm.Let(x, u, CTy(vty), args.head.getArg, b), args.tail)
          case Tm.Lam(_, _, _, _) => impossible()

          case Tm.CRecord(fs) if args.nonEmpty =>
            args.head match
              case Elim.CSelect(i) => go(ty, fs(i), args.tail)
              case _               => impossible()
          case Tm.CRecord(fs) => impossible()

          case Tm.If(_, Tm.BoolLit(b), t, f) =>
            if b then go(ty, t, args) else go(ty, f, args)
          case Tm.If(ty, c, t, f) =>
            val rty = reduce(ty, args)
            Tm.If(
              reduce(ty, args),
              go(CTy(VTy.Bool), c, Nil),
              go(rty, t, args),
              go(rty, f, args)
            )

          case Tm.Unsafe(rt, io, l, args) =>
            val eargs = args.map((tm, ty) => (go(CTy(ty), tm, Nil), ty))
            Tm.Unsafe(rt, io, l, eargs)
          case Tm.UnsafeRunIO(rt, tm) =>
            Tm.UnsafeRunIO(rt, go(CTy.IO(rt), tm, args))

          case Tm.Select(rty, sty, Tm.If(_, c, t, f), i) =>
            go(
              ty,
              Tm.If(
                CTy(rty),
                c,
                Tm.Select(rty, sty, f, i),
                Tm.Select(rty, sty, t, i)
              ),
              args
            )
          case Tm.Select(rty, sty, Tm.Let(x, u, ty2, v, b), i) =>
            go(ty, Tm.Let(x, u, ty2, v, Tm.Select(rty, sty, b, i)), args)
          case Tm.Select(rty, sty, Tm.LetRec(x, u, ty2, v, b), i) =>
            go(ty, Tm.LetRec(x, u, ty2, v, Tm.Select(rty, sty, b, i)), args)
          case Tm.Select(_, _, Tm.Con(_, _, _, _, _, cargs), i) =>
            go(ty, cargs(i)._1, args)
          case Tm.Select(_, _, Tm.Record(_, cargs), i) => go(ty, cargs(i), args)
          case Tm.Select(ty, sty, s, i) =>
            Tm.Select(ty, sty, go(CTy(sty), s, Nil), i)

          // TODO: some of these might not be a good idea
          case Tm.Let(x, _, ty2, Tm.Let(y, _, ty1, v, b1), b2) =>
            go(ty, Tm.Let(y, -1, ty1, v, Tm.Let(x, -1, ty2, b1, b2)), args)
          case Tm.LetRec(x, _, ty2, Tm.LetRec(y, _, ty1, v, b1), b2) =>
            go(
              ty,
              Tm.LetRec(y, -1, ty1, v, Tm.LetRec(x, -1, ty2, b1, b2)),
              args
            )
          case Tm.Let(x, _, ty2, Tm.LetRec(y, _, ty1, v, b1), b2) =>
            go(ty, Tm.LetRec(y, -1, ty1, v, Tm.Let(x, -1, ty2, b1, b2)), args)
          case Tm.LetRec(x, _, ty2, Tm.Let(y, _, ty1, v, b1), b2) =>
            go(ty, Tm.Let(y, -1, ty1, v, Tm.LetRec(x, -1, ty2, b1, b2)), args)
          case Tm.BindIO(x, _, ty2, Tm.BindIO(y, _, ty1, v, b1), b2) =>
            go(
              ty,
              Tm.BindIO(y, -1, ty1, v, Tm.BindIO(x, -1, ty2, b1, b2)),
              args
            )
          case Tm.BindIO(x, _, ty2, Tm.Let(y, _, ty1, v, b1), b2) =>
            go(ty, Tm.Let(y, -1, ty1, v, Tm.BindIO(x, -1, ty2, b1, b2)), args)
          case Tm.BindIO(x, _, ty2, Tm.LetRec(y, _, ty1, v, b1), b2) =>
            go(
              ty,
              Tm.LetRec(y, -1, ty1, v, Tm.BindIO(x, -1, ty2, b1, b2)),
              args
            )
          case Tm.Let(x, _, ty2, Tm.BindIO(y, _, ty1, v, b1), b2) =>
            go(ty, Tm.BindIO(y, -1, ty1, v, Tm.Let(x, -1, ty2, b1, b2)), args)
          case Tm.LetRec(x, _, ty2, Tm.BindIO(y, _, ty1, v, b1), b2) =>
            go(
              ty,
              Tm.BindIO(y, -1, ty1, v, Tm.LetRec(x, -1, ty2, b1, b2)),
              args
            )

          case Tm.Let(_, u, _, v, b) if u == 0 && !doNotRemove(v) =>
            go(ty, b, args)
          case Tm.Let(x, u, vty, v0, b)
              if (u == 1 || isSmall(v0)) && !doNotInline(v0) =>
            val v = go(vty, v0, Nil)
            go(ty, b, args)(using ctx.assign(x, v))
          case Tm.Let(x, _, vty, v0, b0) =>
            val v = go(vty, v0, Nil)
            val (y, b) = ctx.enter(x, vty, ctx ?=> go(ty, b0, args))
            Tm.Let(y, -1, vty, v, b)

          case Tm.LetRec(_, u, _, v, b) if u == 0 && !doNotRemove(v) =>
            go(ty, b, args)
          case Tm.LetRec(x, _, vty, v0, b0) =>
            val (y, v) = ctx.enter(x, vty, ctx ?=> go(vty, v0, Nil))
            val (_, b) = ctx.enter(x, vty, ctx ?=> go(ty, b0, args))
            Tm.LetRec(y, -1, vty, v, b)

          case Tm.BindIO(x, u, ty2, Tm.ReturnIO(_, v), b) =>
            go(ty, Tm.Let(x, u, CTy(ty2), v, b), args)
          case Tm.BindIO(x, _, ty2, v, Tm.ReturnIO(_, Tm.Local(y, _)))
              if x == y =>
            go(ty, v, Nil)
          case Tm.BindIO(x, _, vty, v0, b0) =>
            val v = go(CTy(vty), v0, Nil)
            val (y, b) = ctx.enter(x, ty, ctx ?=> go(ty, b0, args))
            Tm.BindIO(y, -1, vty, v, b)

          case Tm.Case(rty, dty, Tm.Let(x, u, vty, v, b), cs) =>
            go(ty, Tm.Let(x, u, vty, v, Tm.Case(rty, dty, b, cs)), args)
          case Tm.Case(rty, dty, Tm.LetRec(x, u, vty, v, b), cs) =>
            go(ty, Tm.LetRec(x, u, vty, v, Tm.Case(rty, dty, b, cs)), args)
          case Tm.Case(_, _, Tm.Con(_, _, cx, _, _, cargs), cs) =>
            @tailrec
            def lookup(
                cx: Name,
                cs: Cases
            ): Either[Tm, (List[(LocalName, VTy, Int)], Tm)] =
              cs match
                case Cases.Empty                           => impossible()
                case Cases.Otherwise(b)                    => Left(b)
                case Cases.Ext(cx2, ps, b, r) if cx == cx2 => Right((ps, b))
                case Cases.Ext(_, _, _, r)                 => lookup(cx, r)
            lookup(cx, cs) match
              case Left(b) => go(ty, b, args)
              case Right((ps, b)) =>
                val lets = ps.zipWithIndex.foldRight(b) {
                  case (((x, ty, u), i), b) =>
                    Tm.Let(x, u, CTy(ty), cargs(i)._1, b)
                }
                go(ty, lets, args)
          case Tm.Case(_, _, _, Cases.Otherwise(b)) => go(ty, b, args)
          case Tm.Case(rty, dty, s, cs) =>
            @tailrec
            def goParamsRec(
                ps: List[(LocalName, VTy, Int)],
                newps: List[(LocalName, VTy, Int)],
                ctx: Ctx
            ): (List[(LocalName, VTy, Int)], Ctx) =
              ps match
                case Nil => (newps, ctx)
                case (x, ty, _) :: rest =>
                  val (y, nctx) = ctx.enter(x, CTy(ty))
                  goParamsRec(rest, newps :+ (y, ty, -1), nctx)
            inline def goParams(
                ps: List[(LocalName, VTy, Int)]
            )(using ctx: Ctx) = goParamsRec(ps, Nil, ctx)
            def goCases(cs: Cases): Cases =
              cs match
                case Cases.Ext(x, ps, b, r) =>
                  val (nps, nctx) = goParams(ps)
                  val nb = go(ty, b, args)(using nctx)
                  Cases.Ext(x, nps, nb, goCases(r))
                case Cases.Otherwise(b) => Cases.Otherwise(go(ty, b, args))
                case Cases.Empty        => Cases.Empty
            Tm.Case(rty, dty, go(CTy(dty), s, Nil), goCases(cs))

  private def isSmall(t: Tm): Boolean = t match
    case Tm.Local(_, _)                  => true
    case Tm.Global(_, _, _)              => true
    case Tm.Prim(_)                      => true
    case Tm.BoolLit(_)                   => true
    case Tm.IntLit(_)                    => true
    case Tm.StringLit(_)                 => true
    case Tm.CRecord(Nil)                 => true
    case Tm.Con(_, _, _, _, _, Nil)      => true
    case Tm.Record(_, Nil)               => true
    case Tm.ReturnIO(_, v) if isSmall(v) => true
    case _                               => false

  private def doNotInline(t: Tm): Boolean = t match
    case Tm.UnsafeRunIO(_, _) => true
    case _                    => false

  private def doNotRemove(t: Tm): Boolean = t match
    case Tm.UnsafeRunIO(_, _) => true
    case _                    => false

  private def foldConstants2(p: RuntimePrimitive, a: Tm, b: Tm): Option[Tm] =
    import RuntimePrimitive.*
    (p, a, b) match
      case (Add, Tm.IntLit(0), t)            => Some(t)
      case (Add, t, Tm.IntLit(0))            => Some(t)
      case (Add, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a + b))

      case (Sub, t, Tm.IntLit(0))            => Some(t)
      case (Sub, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a - b))

      case (Mul, Tm.IntLit(0), _)            => Some(Tm.Zero)
      case (Mul, _, Tm.IntLit(0))            => Some(Tm.Zero)
      case (Mul, Tm.IntLit(1), t)            => Some(t)
      case (Mul, t, Tm.IntLit(1))            => Some(t)
      case (Mul, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a * b))

      case (Lt, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.bool(a < b))

      case _ => None

  // compute usages
  private type Usages = Map[LocalName, Int]
  private def mergeUsages(a: Usages, b: Usages): Usages =
    b.foldLeft(a) { case (map, (x, u)) =>
      map + (x -> (map.getOrElse(x, 0) + u))
    }

  private inline def correctUsages(t: Tm): Tm = correctUsagesRec(t)._1

  private def correctUsagesRec(t: Tm): (Tm, Usages) =
    def fold(args: List[Tm]): (List[Tm], Usages) =
      args.foldLeft[(List[Tm], Usages)]((Nil, Map.empty)) {
        case ((cargs, usages), arg) =>
          val (a, ua) = correctUsagesRec(arg)
          (cargs :+ a, mergeUsages(usages, ua))
      }
    t match
      case Tm.Global(_, _, _) => (t, Map.empty)
      case Tm.Prim(_)         => (t, Map.empty)
      case Tm.BoolLit(_)      => (t, Map.empty)
      case Tm.IntLit(_)       => (t, Map.empty)
      case Tm.StringLit(_)    => (t, Map.empty)

      case Tm.CRecord(fs) =>
        val (cfs, usages) = fold(fs)
        (Tm.CRecord(cfs), usages)

      case Tm.CSelect(s, i) =>
        val (es, us) = correctUsagesRec(s)
        (Tm.CSelect(es, i), us)

      case Tm.Local(x, _) => (t, Map(x -> 1))

      case Tm.ReturnIO(ty, v) =>
        val (cv, uv) = correctUsagesRec(v)
        (Tm.ReturnIO(ty, cv), uv)

      case Tm.Lam(x, _, ty, b0) =>
        val (b, u) = correctUsagesRec(b0)
        (Tm.Lam(x, u.getOrElse(x, 0), ty, b), u - x)

      case Tm.App(f0, a0, vt) =>
        val (f, uf) = correctUsagesRec(f0)
        val (a, ua) = correctUsagesRec(a0)
        (Tm.App(f, a, vt), mergeUsages(uf, ua))
      case Tm.If(ty, c0, t0, f0) =>
        val (c, uc) = correctUsagesRec(c0)
        val (t, ut) = correctUsagesRec(t0)
        val (f, uf) = correctUsagesRec(f0)
        (Tm.If(ty, c, t, f), mergeUsages(uc, mergeUsages(ut, uf)))
      case Tm.Con(m, dx, cx, ix, dty, args) =>
        val (cargs, usages) = fold(args.map(_._1))
        (Tm.Con(m, dx, cx, ix, dty, cargs.zip(args.map(_._2))), usages)
      case Tm.Unsafe(rt, io, l, args) =>
        val (cargs, usages) = fold(args.map(_._1))
        (Tm.Unsafe(rt, io, l, cargs.zip(args.map(_._2))), usages)
      case Tm.UnsafeRunIO(rt, tm) =>
        val (etm, u) = correctUsagesRec(tm)
        (Tm.UnsafeRunIO(rt, etm), u)

      case Tm.Record(ty, args) =>
        val (cargs, usages) = fold(args)
        (Tm.Record(ty, cargs), usages)

      case Tm.Select(ty, sty, s, i) =>
        val (cs, us) = correctUsagesRec(s)
        (Tm.Select(ty, sty, cs, i), us)

      case Tm.Case(rt, dt, s, cs) =>
        def go(cs: Cases): (Cases, Usages) =
          cs match
            case Cases.Empty => (Cases.Empty, Map.empty)
            case Cases.Otherwise(b) =>
              val (cb, ub) = correctUsagesRec(b)
              (Cases.Otherwise(cb), ub)
            case Cases.Ext(x, ps, b, r) =>
              val (cb, ub) = correctUsagesRec(b)
              val nps = ps.map((x, ty, _) => (x, ty, ub.getOrElse(x, 0)))
              val ub2 = ub -- ps.map((x, _, _) => x)
              val (cr, ur) = go(r)
              (Cases.Ext(x, nps, cb, cr), mergeUsages(ub2, ur))
        val (scrut, us) = correctUsagesRec(s)
        val (ccs, ucs) = go(cs)
        (Tm.Case(rt, dt, scrut, ccs), mergeUsages(us, ucs))

      case Tm.Let(x, _, ty, v0, b0) =>
        val (v, uv) = correctUsagesRec(v0)
        val (b, ub) = correctUsagesRec(b0)
        (Tm.Let(x, ub.getOrElse(x, 0), ty, v, b), mergeUsages(uv, ub - x))
      case Tm.LetRec(x, _, ty, v0, b0) =>
        val (v, uv) = correctUsagesRec(v0)
        val (b, ub) = correctUsagesRec(b0)
        (
          Tm.LetRec(x, uv.getOrElse(x, 0) + ub.getOrElse(x, 0), ty, v, b),
          mergeUsages(uv, ub) - x
        )
      case Tm.BindIO(x, _, ty, v0, b0) =>
        val (v, uv) = correctUsagesRec(v0)
        val (b, ub) = correctUsagesRec(b0)
        (
          Tm.BindIO(x, ub.getOrElse(x, 0), ty, v, b),
          mergeUsages(uv, ub - x)
        )
