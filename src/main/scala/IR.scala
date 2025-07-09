import scala.annotation.tailrec
import scala.collection.mutable

object IR:
  type Name = String
  type Ix = Int

  final case class Module(name: Name, defs: List[Def])

  enum Def:
    case Value(name: Name, ty: TypeDef, value: Expr)

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double

  final case class TypeDef(params: List[Type], returnty: Type)

  enum Expr:
    case Local(ix: Ix)
    case Global(name: Name)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case App(fn: Expr, arg: Expr)
    case Lam(ty: Type, body: Expr)

    case Let(ty: TypeDef, value: Expr, body: Expr)

    // TODO: datatypes, records, let-rec, if

    override def toString: String = this match
      case Expr.Local(i)            => s"'$i"
      case Expr.Global(name)        => name
      case Expr.IntLit(value)       => value.toString
      case Expr.BoolLit(value)      => if value then "True" else "False"
      case Expr.App(fn, arg)        => s"($fn $arg)"
      case Expr.Lam(_, body)        => s"(\\$body)"
      case Expr.Let(_, value, body) => s"(let $value in $body)"

    def shift(c: Int, d: Int): Expr = this match
      case l @ Expr.Local(i)   => if i < c then l else Expr.Local(i + d)
      case g @ Expr.Global(_)  => g
      case i @ Expr.IntLit(_)  => i
      case b @ Expr.BoolLit(_) => b
      case Expr.App(fn, arg)   => Expr.App(fn.shift(c, d), arg.shift(c, d))
      case Expr.Lam(ty, body)  => Expr.Lam(ty, body.shift(c + 1, d))
      case Expr.Let(ty, value, body) =>
        Expr.Let(ty, value.shift(c, d), body.shift(c + 1, d))

    private def subst(i: Ix, v: Expr): Expr = this match
      case loc @ Expr.Local(j) => if j == i then v else loc
      case g @ Expr.Global(_)  => g
      case i @ Expr.IntLit(_)  => i
      case b @ Expr.BoolLit(_) => b
      case Expr.App(fn, arg)   => Expr.App(fn.subst(i, v), arg.subst(i, v))
      case Expr.Lam(ty, body)  => Expr.Lam(ty, body.subst(i + 1, v.shift(0, 1)))
      case Expr.Let(ty, value, body) =>
        Expr.Let(ty, value.subst(i + 1, v), body.subst(i + 1, v.shift(0, 1)))

    def beta(arg: Expr): Expr = subst(0, arg.shift(0, 1)).shift(0, -1)

  // to JVM IR
  def toJVM(module: Module): JVM.Module =
    val newdefs = module.defs.flatMap(toJVM)
    JVM.Module(module.name, newdefs)

  private def toJVM(defn: Def): List[JVM.Def] = defn match
    case Def.Value(name, ty, value) =>
      val simplified = simplifyTopLevelUntilDone(eta(ty, value))
      given liftedDefs: mutable.ArrayBuffer[JVM.Def] = mutable.ArrayBuffer.empty
      val lifted = lift(removeLams(simplified), true)
      val defn =
        if ty.params.isEmpty then
          JVM.Def.Value(name, toJVM(ty.returnty), lifted)
        else
          JVM.Def.Function(
            name,
            ty.params.map(toJVM),
            toJVM(ty.returnty),
            lifted
          )
      defn :: liftedDefs.toList

  private def toJVM(ty: Type): JVM.Type = ty match
    case Type.Boolean => JVM.Type.Boolean
    case Type.Byte    => JVM.Type.Byte
    case Type.Char    => JVM.Type.Char
    case Type.Short   => JVM.Type.Short
    case Type.Int     => JVM.Type.Int
    case Type.Long    => JVM.Type.Long
    case Type.Float   => JVM.Type.Float
    case Type.Double  => JVM.Type.Double

  // simplification:
  // - remove dead lets
  // - inline once-used lets
  // - eta-expand lets
  private type Occ = Map[Ix, Int]

  @tailrec
  private def simplifyTopLevelUntilDone(expr: Expr): Expr =
    simplify(expr)._1 match
      case None          => expr
      case Some(newexpr) => simplifyTopLevelUntilDone(newexpr)

  private def simplify(expr: Expr): (Option[Expr], Occ) =
    expr match
      case Expr.Local(ix)  => (None, Map(ix -> 1))
      case Expr.Global(_)  => (None, Map.empty)
      case Expr.IntLit(_)  => (None, Map.empty)
      case Expr.BoolLit(_) => (None, Map.empty)

      case Expr.App(Expr.Lam(ty, body), arg) =>
        val (res, occ1, occ2) = simplify2(body, arg)
        val (sbody, sarg) = res.getOrElse((body, arg))
        val occ = merge(leave(occ1), occ2)
        (Some(Expr.Let(TypeDef(Nil, ty), sarg, sbody)), occ)
      case Expr.App(Expr.Let(ty, value, body), arg) =>
        val (res1, occ1) = simplify(value)
        val svalue = res1.getOrElse(value)
        val (res2, occ2, occ3) = simplify2(body, arg)
        val (sbody, sarg) = res2.getOrElse((body, arg))
        (
          Some(Expr.Let(ty, svalue, Expr.App(sbody, sarg.shift(0, 1)))),
          merge(merge(occ1, occ2), shift(1, occ3))
        )
      case Expr.App(fn, arg) =>
        simplify2(fn, arg) match
          case (Some((fn, arg)), occ1, occ2) =>
            (Some(Expr.App(fn, arg)), merge(occ1, occ2))
          case (None, occ1, occ2) => (None, merge(occ1, occ2))

      case Expr.Lam(ty, body) =>
        simplify(body) match
          case (None, occ)       => (None, leave(occ))
          case (Some(body), occ) => (Some(Expr.Lam(ty, body)), leave(occ))

      case Expr.Let(ty, value, body) =>
        simplify2(value, body) match
          case (Some((value, body)), occ1, occ2) =>
            (Some(Expr.Let(ty, value, body)), merge(occ1, leave(occ2)))
          case (None, occ1, occ2) =>
            val occ = merge(occ1, leave(occ2))
            occ2.getOrElse(0, 0) match
              case 0 => (Some(body.shift(0, -1)), occ) // not used
              case n if n == 1 || isSmall(value) =>
                (Some(body.beta(value)), occ) // once used => inline
              case _ if !isEtaExpanded(ty.params.size, value) => // eta-expand
                (Some(Expr.Let(ty, eta(ty, value), body)), occ)
              case _ => (None, occ)

  private def simplify2(e1: Expr, e2: Expr): (Option[(Expr, Expr)], Occ, Occ) =
    (simplify(e1), simplify(e2)) match
      case ((None, o1), (None, o2))         => (None, o1, o2)
      case ((Some(e1), o1), (None, o2))     => (Some((e1, e2)), o1, o2)
      case ((None, o1), (Some(e2), o2))     => (Some((e1, e2)), o1, o2)
      case ((Some(e1), o1), (Some(e2), o2)) => (Some((e1, e2)), o1, o2)

  private def isSmall(expr: IR.Expr): Boolean = expr match
    case Expr.Local(_)   => true
    case Expr.Global(_)  => true
    case Expr.IntLit(_)  => true
    case Expr.BoolLit(_) => true
    case _               => false

  @tailrec
  private def isEtaExpanded(n: Int, expr: IR.Expr): Boolean =
    n match
      case 0 => true
      case n =>
        expr match
          case Expr.Lam(_, body) => isEtaExpanded(n - 1, body)
          case _                 => false

  private def eta(ty: TypeDef, value: Expr): Expr =
    val newvalue =
      ty.params.indices.reverse
        .map(Expr.Local.apply)
        .foldLeft(value)(Expr.App.apply)
    ty.params.foldRight(newvalue)(Expr.Lam.apply)

  private def merge(o1: Occ, o2: Occ): Occ =
    val map = mutable.Map.empty[Ix, Int]
    o1.foreach((k, v) => map(k) = v)
    o2.foreach { (k, v) => map(k) = if map.contains(k) then map(k) + v else v }
    map.toMap

  private def shift(d: Int, o: Occ): Occ =
    o.toList.map((k, v) => (k + d, v)).toMap

  // leave a scope
  private def leave(o: Occ): Occ = shift(-1, o.removed(0))

  // lifting
  // - lift function lets to top-level
  // - create join points where possible
  // - translate to JVM IR
  private def lift(expr: Expr, tail: Boolean)(using
      liftedDefs: mutable.ArrayBuffer[JVM.Def]
  ): JVM.Expr = expr match
    case Expr.Local(_)   => ???
    case Expr.Global(_)  => ???
    case Expr.IntLit(v)  => JVM.Expr.IntLit(v)
    case Expr.BoolLit(v) => JVM.Expr.BoolLit(v)

    case Expr.App(fn, arg)         => ???
    case Expr.Lam(ty, body)        => ???
    case Expr.Let(ty, value, body) => ???

  @tailrec
  private def removeLams(expr: Expr): Expr = expr match
    case Expr.Lam(_, body) => removeLams(body)
    case expr              => expr
