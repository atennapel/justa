import Common.{Name, RuntimePrimitive}
import IR.*
import Debug.debug

import scala.annotation.tailrec
import Common.impossible

// eta-expand, remove dead lets, inlining, constant folding, remove closures
object Simplification:
  def simplifyDefs(ds: Defs): Defs =
    Defs(ds.toList.map(simplifyDef))

  private type Scope = Set[LocalName]
  private type Subst = Map[LocalName, Tm]

  private def simplifyDef(d: Def): Def =
    debug(s"simplifyDef ${d.name}")
    val (ps, nargs, nscope) = eta(d.ty)(using Set.empty)
    val expanded = go(d.value, nargs)(using nscope, Map.empty)
    val simp = correctUsages(simplify(lams(ps, expanded)))
    Def(d.name, d.ty, simp)

  @tailrec
  private def simplify(t: Tm): Tm =
    debug(s"simplify $t")
    val next = go(correctUsages(t), Nil)(using Set.empty, Map.empty)
    if next == t then t else simplify(next)

  private def go(t: Tm, args: List[Tm])(using scope: Scope, subst: Subst): Tm =
    t match
      case Tm.Global(_) => args.foldLeft(t)(Tm.App.apply)
      case Tm.Prim(p) =>
        if args.size == 2 then
          foldConstants2(p, args(0), args(1)) match
            case Some(tm) => tm
            case None     => args.foldLeft(t)(Tm.App.apply)
        else args.foldLeft(t)(Tm.App.apply)
      case Tm.BoolLit(_) => t
      case Tm.IntLit(_)  => t

      case Tm.Con(dx, cx, ix, dty, args) =>
        Tm.Con(dx, cx, ix, dty, args.map(a => go(a, Nil)))

      case Tm.Local(x, ty) =>
        subst.get(x) match
          case Some(tm) if tm != t => go(tm, args)
          case _                   => args.foldLeft(t)(Tm.App.apply)

      case Tm.If(_, Tm.BoolLit(b), t, f) =>
        if b then go(t, args) else go(f, args)
      case Tm.If(ty, c, t, f) =>
        Tm.If(ty.drop(args.size), go(c, Nil), go(t, args), go(f, args))

      case Tm.App(f, a) => go(f, go(a, Nil) :: args)

      case Tm.Lam(x, u, ty, b) if args.nonEmpty =>
        go(Tm.Let(x, u, CTy(ty), args.head, b), args.tail)
      case Tm.Lam(x, _, ty, b0) =>
        if scope.contains(x) then
          val y = scope.size
          val b =
            go(b0, Nil)(using scope + y, subst + (x -> Tm.Local(y, CTy(ty))))
          Tm.Lam(y, -1, ty, b)
        else
          val b = go(b0, Nil)(using scope + x, subst - x)
          Tm.Lam(x, -1, ty, b)

      case Tm.Let(x, _, ty2, Tm.Let(y, _, ty1, v, b1), b2) =>
        go(Tm.Let(y, -1, ty1, v, Tm.Let(x, -1, ty2, b1, b2)), args)
      case Tm.LetRec(x, _, ty2, Tm.LetRec(y, _, ty1, v, b1), b2) =>
        go(Tm.LetRec(y, -1, ty1, v, Tm.LetRec(x, -1, ty2, b1, b2)), args)
      case Tm.Let(x, _, ty2, Tm.LetRec(y, _, ty1, v, b1), b2) =>
        go(Tm.LetRec(y, -1, ty1, v, Tm.Let(x, -1, ty2, b1, b2)), args)
      case Tm.LetRec(x, _, ty2, Tm.Let(y, _, ty1, v, b1), b2) =>
        go(Tm.Let(y, -1, ty1, v, Tm.LetRec(x, -1, ty2, b1, b2)), args)

      case Tm.Let(_, u, _, _, b) if u == 0 => go(b, args)
      case Tm.Let(x, u, _, v, b) if u == 1 || isSmall(v) =>
        go(b, args)(using scope, subst + (x -> v))
      case Tm.Let(x, _, ty, v0, b0) =>
        val v =
          if isEtaExpanded(ty, v0) then go(v0, Nil)
          else
            val (ps, nargs, nscope) = eta(ty)
            lams(ps, go(v0, nargs)(using nscope))
        val (y, b) = if scope.contains(x) then
          val y = scope.size
          (y, go(b0, args)(using scope + y, subst + (x -> Tm.Local(y, ty))))
        else (x, go(b0, args)(using scope + x, subst - x))
        Tm.Let(x, -1, ty, v, b)

      case Tm.LetRec(_, u, _, _, b) if u == 0 => go(b, args)
      case Tm.LetRec(x, _, ty, v0, b0) =>
        val (y, nscope, nsubst) = if scope.contains(x) then
          val y = scope.size
          (y, scope + y, subst + (x -> Tm.Local(y, ty)))
        else (x, scope + x, subst - x)
        val v =
          if isEtaExpanded(ty, v0) then go(v0, Nil)(using nscope, nsubst)
          else
            val (ps, nargs, nscope2) = eta(ty)(using nscope)
            val body = go(v0, nargs)(using nscope2, nsubst)
            lams(ps, body)
        val b = go(b0, args)(using nscope, nsubst)
        Tm.LetRec(x, -1, ty, v, b)

      case Tm.Case(_, _, Tm.Con(_, cx, _, _, cargs), cs) =>
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
          case Left(b) => go(b, args)
          case Right((ps, b)) =>
            val lets = ps.zipWithIndex.foldRight(b) {
              case (((x, ty, u), i), b) =>
                Tm.Let(x, u, CTy(ty), cargs(i), b)
            }
            go(lets, args)
      case Tm.Case(rty, dty, s, cs) =>
        @tailrec
        def goParamsRec(
            ps: List[(LocalName, VTy, Int)],
            newps: List[(LocalName, VTy, Int)],
            scope: Scope,
            subst: Subst
        ): (List[(LocalName, VTy, Int)], Scope, Subst) =
          ps match
            case Nil => (newps, scope, subst)
            case (x, ty, _) :: rest =>
              if scope.contains(x) then
                val y = scope.size
                goParamsRec(
                  rest,
                  newps ++ List((y, ty, -1)),
                  scope + y,
                  subst + (x -> Tm.Local(y, CTy(ty)))
                )
              else
                goParamsRec(
                  rest,
                  newps ++ List((x, ty, -1)),
                  scope + x,
                  subst - x
                )
        inline def goParams(
            ps: List[(LocalName, VTy, Int)]
        )(using scope: Scope, subst: Subst) =
          goParamsRec(ps, Nil, scope, subst)
        def goCases(cs: Cases): Cases =
          cs match
            case Cases.Ext(x, ps, b, r) =>
              val (nps, innerscope, innersubst) = goParams(ps)
              val nb = go(b, args)(using innerscope, innersubst)
              Cases.Ext(x, nps, nb, goCases(r))
            case Cases.Otherwise(b) => Cases.Otherwise(go(b, args))
            case Cases.Empty        => Cases.Empty
        Tm.Case(rty, dty, go(s, Nil), goCases(cs))

  private def eta(ty: CTy)(using
      scope: Scope
  ): (List[(LocalName, VTy)], List[Tm], Scope) =
    val base = scope.size
    val params = ty.params.zipWithIndex.map((t, n) => (base + n, t))
    val args = params.map { case (x, ty) => Tm.Local(x, CTy(ty)) }
    (params, args, scope ++ params.map(_._1))

  private def lams(ps: List[(LocalName, VTy)], b: Tm): Tm =
    ps.foldRight(b) { case ((x, ty), b) => Tm.Lam(x, -1, ty, b) }

  private def isEtaExpanded(ty: CTy, v: Tm): Boolean =
    @tailrec
    def go(ps: List[VTy], v: Tm): Boolean =
      (ps, v) match
        case (Nil, _)                        => true
        case (_ :: rest, Tm.Lam(_, _, _, b)) => go(rest, b)
        case _                               => false
    go(ty.params, v)

  private def isSmall(t: Tm) = t match
    case Tm.Local(_, _)          => true
    case Tm.Global(name)         => true
    case Tm.Prim(_)              => true
    case Tm.BoolLit(_)           => true
    case Tm.IntLit(_)            => true
    case Tm.Con(_, _, _, _, Nil) => true
    case _                       => false

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
    t match
      case Tm.Global(_)  => (t, Map.empty)
      case Tm.Prim(_)    => (t, Map.empty)
      case Tm.BoolLit(_) => (t, Map.empty)
      case Tm.IntLit(_)  => (t, Map.empty)

      case Tm.Local(x, _) => (t, Map(x -> 1))

      case Tm.Lam(x, _, ty, b0) =>
        val (b, u) = correctUsagesRec(b0)
        (Tm.Lam(x, u.getOrElse(x, 0), ty, b), u - x)

      case Tm.App(f0, a0) =>
        val (f, uf) = correctUsagesRec(f0)
        val (a, ua) = correctUsagesRec(a0)
        (Tm.App(f, a), mergeUsages(uf, ua))
      case Tm.If(ty, c0, t0, f0) =>
        val (c, uc) = correctUsagesRec(c0)
        val (t, ut) = correctUsagesRec(t0)
        val (f, uf) = correctUsagesRec(f0)
        (Tm.If(ty, c, t, f), mergeUsages(uc, mergeUsages(ut, uf)))
      case Tm.Con(dx, cx, ix, dty, args) =>
        val (cargs, usages) =
          args.foldLeft[(List[Tm], Usages)]((Nil, Map.empty)) {
            case ((cargs, usages), arg) =>
              val (a, ua) = correctUsagesRec(arg)
              (cargs ++ List(a), mergeUsages(usages, ua))
          }
        (Tm.Con(dx, cx, ix, dty, cargs), usages)

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
