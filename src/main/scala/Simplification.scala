import Common.Primitive
import IR.*

import scala.annotation.tailrec

object Simplification:
  def simplifyDefs(ds: Defs): Defs =
    Defs(ds.toList.map(simplifyDef))

  private type Scope = Set[LocalName]
  private type Subst = Map[LocalName, Tm]

  private def simplifyDef(d: Def): Def =
    val expanded = Tm.Let(0, -1, d.ty, d.value, Tm.Local(0, d.ty))
    val simp = simplify(expanded)(using Set.empty, Map.empty)
    Def(d.name, d.ty, simp)

  @tailrec
  private def simplify(t: Tm)(using scope: Scope, subst: Subst): Tm =
    val next = go(correctUsages(t), Nil)
    if next == t then t else simplify(next)

  // TODO: eta-expansion, let flattening
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

      case Tm.Local(x, ty) =>
        subst.get(x) match
          case Some(tm) => go(tm, args)
          case None     => args.foldLeft(t)(Tm.App.apply)

      case Tm.If(_, Tm.BoolLit(b), t, f) => if b then t else f
      case Tm.If(ty, c, t, f) if ty.params.nonEmpty =>
        val (ps, nargs, nscope) = eta(ty)
        val b = Tm.If(
          CTy(ty.ret),
          go(c, Nil),
          go(t, args ++ nargs)(using nscope),
          go(f, args ++ nargs)(using nscope)
        )
        ps.foldRight(b) { case ((x, ty), b) => Tm.Lam(x, -1, ty, b) }
      case Tm.If(ty, c, t, f) => Tm.If(ty, go(c, Nil), go(t, args), go(f, args))

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

      case Tm.Let(_, u, _, _, b) if u == 0 => b
      case Tm.Let(x, u, _, v, b) if u == 1 || isSmall(v) =>
        go(b, args)(using scope, subst + (x -> v))
      case Tm.Let(x, _, ty, v0, b0) =>
        val v = go(v0, Nil)
        val (y, b) = if scope.contains(x) then
          val y = scope.size
          (y, go(b0, args)(using scope + y, subst + (x -> Tm.Local(y, ty))))
        else (x, go(b0, args)(using scope + x, subst - x))
        Tm.Let(x, -1, ty, v, b)

      case Tm.LetRec(_, u, _, _, b) if u == 0 => b
      case Tm.LetRec(x, _, ty, v0, b0) =>
        val (y, nscope, nsubst) = if scope.contains(x) then
          val y = scope.size
          (y, scope + y, subst + (x -> Tm.Local(y, ty)))
        else (x, scope + x, subst - x)
        val v = go(v0, Nil)(using nscope, nsubst)
        val b = go(b0, args)(using nscope, nsubst)
        Tm.LetRec(x, -1, ty, v, b)

  private def eta(ty: CTy)(using
      scope: Scope
  ): (List[(LocalName, VTy)], List[Tm], Scope) =
    val base = scope.size
    val params = ty.params.zipWithIndex.map((t, n) => (base + n, t))
    val args = params.map { case (x, ty) => Tm.Local(x, CTy(ty)) }
    (params, args, scope ++ params.map(_._1))

  private def isSmall(t: Tm) = t match
    case Tm.Local(_, _)  => true
    case Tm.Global(name) => true
    case Tm.Prim(_)      => true
    case Tm.BoolLit(_)   => true
    case Tm.IntLit(_)    => true
    case _               => false

  private def foldConstants2(p: Primitive, a: Tm, b: Tm): Option[Tm] =
    (p, a, b) match
      case (Primitive.Add, Tm.IntLit(0), t)            => Some(t)
      case (Primitive.Add, t, Tm.IntLit(0))            => Some(t)
      case (Primitive.Add, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a + b))

      case (Primitive.Sub, t, Tm.IntLit(0))            => Some(t)
      case (Primitive.Sub, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a - b))

      case (Primitive.Mul, Tm.IntLit(0), _)            => Some(Tm.Zero)
      case (Primitive.Mul, _, Tm.IntLit(0))            => Some(Tm.Zero)
      case (Primitive.Mul, Tm.IntLit(1), t)            => Some(t)
      case (Primitive.Mul, t, Tm.IntLit(1))            => Some(t)
      case (Primitive.Mul, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.IntLit(a * b))

      case (Primitive.Lt, Tm.IntLit(a), Tm.IntLit(b)) => Some(Tm.bool(a < b))

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
