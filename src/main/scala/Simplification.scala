import Common.*
import IR.*
import scala.annotation.tailrec

object Simplification:
  def simplifyDefs(ds: Defs): Defs =
    Defs(ds.toList.map(simplifyDef))

  private type Scope = Set[LocalName]
  private type Subst = Map[LocalName, Tm]

  private def simplifyDef(d: Def): Def =
    val params = d.ty.params.zipWithIndex
    given Scope = (0 until params.size).toSet
    val apps = params.foldLeft(d.value) { case (f, (ty, x)) =>
      Tm.App(f, Tm.Local(x, CTy(ty)))
    }
    val tm = params.foldRight(apps) { case ((ty, x), body) =>
      Tm.Lam(x, ty, body)
    }
    val simp = simplify(tm)(using Set.empty, Map.empty)
    Def(d.name, d.ty, simp)

  private final case class Occ(vars: Map[LocalName, (CTy, Int)]):
    def remove(x: LocalName): Occ = Occ(vars - x)
    def usage(x: LocalName): Int = vars.get(x) match
      case Some((_, n)) => n
      case None         => 0
    def merge(other: Occ): Occ =
      Occ(other.vars.foldLeft(vars) { case (map, (x, (ty, u))) =>
        map.get(x) match
          case Some((ty2, v)) => map + (x -> (ty, v + u))
          case None           => map + (x -> (ty, u))
      })
  private object Occ:
    val empty: Occ = Occ(Map.empty)
    def apply(x: LocalName, ty: CTy): Occ = Occ(Map(x -> (ty, 1)))
    def apply(occs: List[Occ]): Occ = occs.foldLeft(empty)((a, b) => a.merge(b))

  private enum Result:
    case Unchanged(_occ: Occ)
    case Changed(_occ: Occ, tm: Tm)

    def occ: Occ = this match
      case Unchanged(_occ)  => _occ
      case Changed(_occ, _) => _occ

    def get(orig: Tm): Tm = this match
      case Unchanged(_)   => orig
      case Changed(_, tm) => tm

    def map(occf: Occ => Occ, tmf: Tm => Tm): Result = this match
      case Unchanged(occ)   => Unchanged(occf(occ))
      case Changed(occ, tm) => Changed(occf(occ), tmf(tm))

    def mapIfChanged(
        occf: Occ => Occ,
        tmf: Tm => Tm,
        isChanged: Boolean,
        tm: Tm
    ): Result = this match
      case Unchanged(occ) if !isChanged => Unchanged(occf(occ))
      case Unchanged(occ)               => Changed(occf(occ), tmf(tm))
      case Changed(occ, tm)             => Changed(occf(occ), tmf(tm))

    def changed(tm: Tm): Result = this match
      case Unchanged(occ)   => Changed(occ, tm)
      case Changed(occ, tm) => this
  import Result.*

  private enum ResultN:
    case UnchangedN(_occs: List[Occ])
    case ChangedN(_occs: List[Occ], tms: List[Tm])

    def merge(
        occsf: PartialFunction[List[Occ], Occ],
        tmf: PartialFunction[List[Tm], Tm]
    ): Result =
      this match
        case UnchangedN(occs) =>
          Unchanged(occsf.applyOrElse(occs, _ => impossible()))
        case ChangedN(occs, tms) =>
          Changed(
            occsf.applyOrElse(occs, _ => impossible()),
            tmf.applyOrElse(tms, _ => impossible())
          )

    def mergeIfChanged(
        occsf: PartialFunction[List[Occ], Occ],
        tmf: PartialFunction[List[Tm], Tm],
        isChanged: Boolean,
        termsIfChanged: List[Tm]
    ): Result =
      this match
        case UnchangedN(occs) if !isChanged =>
          Unchanged(occsf.applyOrElse(occs, _ => impossible()))
        case UnchangedN(occs) =>
          Changed(
            occsf.applyOrElse(occs, _ => impossible()),
            tmf.applyOrElse(termsIfChanged, _ => impossible())
          )
        case ChangedN(occs, tms) =>
          Changed(
            occsf.applyOrElse(occs, _ => impossible()),
            tmf.applyOrElse(tms, _ => impossible())
          )
  import ResultN.*

  @tailrec
  private def simplify(tm: Tm)(using scope: Scope, subst: Subst): Tm =
    go(tm) match
      case Unchanged(_)      => tm
      case Changed(_, newtm) => simplify(newtm)

  // TODO: inlining, eta-expansion, let-flattening
  private def go(tm: Tm)(using scope: Scope, subst: Subst): Result =
    println(s"go $scope $subst: $tm")
    inline def goChanged(tm: Tm) =
      val cache = tm
      go(cache).changed(cache)
    inline def goNmergeIfChanged(
        terms: List[Tm],
        isChanged: Boolean,
        occsf: PartialFunction[List[Occ], Occ],
        tmsf: PartialFunction[List[Tm], Tm]
    )(using scope: Scope, subst: Subst) =
      val tms = terms
      goN(tms).mergeIfChanged(occsf, tmsf, isChanged, tms)
    inline def goIfChanged(
        tm: Tm,
        isChanged: Boolean,
        occf: Occ => Occ,
        tmf: Tm => Tm
    )(using scope: Scope, subst: Subst) =
      val rtm = tm
      go(rtm).mapIfChanged(occf, tmf, isChanged, rtm)
    inline def inScopeExpl(
        x: LocalName,
        ty: CTy
    )(inline k: (Scope, Subst, LocalName, Boolean) => Result): Result =
      if scope.contains(x) then
        val y = scope.size
        k(scope + y, subst + (x -> Tm.Local(y, ty)), y, true)
      else k(scope + x, subst - x, x, false)
    inline def inScope(
        x: LocalName,
        ty: CTy
    )(k: Scope ?=> Subst ?=> (LocalName, Boolean) => Result): Result =
      inScopeExpl(x, ty): (scope, subst, x, isChanged) =>
        k(using scope)(using subst)(x, isChanged)
    tm match
      case Tm.Local(x, ty) =>
        subst.get(x) match
          case Some(tm) => goChanged(tm)
          case None     => Unchanged(Occ(x, ty))
      case Tm.Global(_)  => Unchanged(Occ.empty)
      case Tm.BoolLit(_) => Unchanged(Occ.empty)
      case Tm.IntLit(_)  => Unchanged(Occ.empty)
      case Tm.Prim(_)    => Unchanged(Occ.empty)

      case Tm.Let(x, ty, v, b) =>
        inScopeExpl(x, ty): (scope, subst, x, isChanged) =>
          go(b)(using scope, subst) match
            case Unchanged(occ) =>
              go(v) match
                case Unchanged(occ2) if !isChanged =>
                  Unchanged(occ.merge(occ2.remove(x)))
                case Unchanged(occ2) =>
                  Changed(occ.merge(occ2.remove(x)), Tm.Let(x, ty, v, b))
                case Changed(occ2, v) =>
                  Changed(occ.merge(occ2.remove(x)), Tm.Let(x, ty, v, b))
            case Changed(occ, b) =>
              go(v) match
                case Unchanged(occ2) =>
                  Changed(occ.merge(occ2.remove(x)), Tm.Let(x, ty, v, b))
                case Changed(occ2, v) =>
                  Changed(occ.merge(occ2.remove(x)), Tm.Let(x, ty, v, b))

      case Tm.LetRec(x, ty, v, b) =>
        inScope(x, ty): (x, isChanged) =>
          goNmergeIfChanged(
            List(v, b),
            isChanged,
            { case List(occ, occ2) => occ.merge(occ2).remove(x) },
            { case List(v, b) => Tm.LetRec(x, ty, v, b) }
          )

      case Tm.Lam(x, ty, b) =>
        inScope(x, CTy(ty)): (x, isChanged) =>
          goIfChanged(b, isChanged, _.remove(x), Tm.Lam(x, ty, _))

      // constant folding
      case Tm.App(Tm.App(Tm.Prim(Primitive.Add), Tm.IntLit(0)), b) => go(b)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Add), a), Tm.IntLit(0)) => go(a)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Add), Tm.IntLit(a)), Tm.IntLit(b)) =>
        Changed(Occ.empty, Tm.IntLit(a + b))

      case Tm.App(Tm.App(Tm.Prim(Primitive.Sub), a), Tm.IntLit(0)) => go(a)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Sub), Tm.IntLit(a)), Tm.IntLit(b)) =>
        Changed(Occ.empty, Tm.IntLit(a - b))

      case Tm.App(Tm.App(Tm.Prim(Primitive.Mul), Tm.IntLit(0)), _) =>
        Changed(Occ.empty, Tm.Zero)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Mul), _), Tm.IntLit(0)) =>
        Changed(Occ.empty, Tm.Zero)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Mul), Tm.IntLit(1)), b) => go(b)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Mul), a), Tm.IntLit(1)) => go(a)
      case Tm.App(Tm.App(Tm.Prim(Primitive.Mul), Tm.IntLit(a)), Tm.IntLit(b)) =>
        Changed(Occ.empty, Tm.IntLit(a * b))

      case Tm.App(Tm.App(Tm.Prim(Primitive.Lt), Tm.IntLit(a)), Tm.IntLit(b)) =>
        Changed(Occ.empty, Tm.bool(a < b))

      case Tm.App(fn, arg) =>
        fn match
          // (\(x : t) => b) a ~> let x : t = a; b
          case Tm.Lam(x, ty, b) => goChanged(Tm.Let(x, CTy(ty), arg, b))
          case _ =>
            goN(List(fn, arg))
              .merge(Occ(_), { case List(f, a) => Tm.App(f, a) })

      case Tm.If(ty, c, t, f) =>
        c match
          case Tm.BoolLit(b) => goChanged(if b then t else f)
          case _ =>
            goN(List(c, t, f))
              .merge(Occ(_), { case List(c, t, f) => Tm.If(ty, c, t, f) })

  private def goN(tm: List[Tm])(using scope: Scope, subst: Subst): ResultN =
    tm match
      case Nil => UnchangedN(Nil)
      case tm :: rest =>
        val prev = goN(rest)
        go(tm) match
          case Unchanged(occ) =>
            prev match
              case UnchangedN(occs)    => UnchangedN(occ :: occs)
              case ChangedN(occs, tms) => ChangedN(occ :: occs, tm :: tms)
          case Changed(occ, tm) =>
            prev match
              case UnchangedN(occs)    => ChangedN(occ :: occs, tm :: rest)
              case ChangedN(occs, tms) => ChangedN(occ :: occs, tm :: tms)
