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

  final case class TypeDef(params: List[Type], returnty: Type):
    def tail: TypeDef = TypeDef(params.tail, returnty)
    def get: Type =
      if params.isEmpty then returnty
      else throw new Exception("expected non-function type")

  object TypeDef:
    def apply(ty: Type): TypeDef = TypeDef(Nil, ty)

  type IxMap = Map[Ix, TypeDef]

  enum Expr:
    case Local(ix: Ix, ty: TypeDef)
    case Global(name: Name)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case App(fn: Expr, arg: Expr)
    case Lam(ty: Type, body: Expr)

    case Let(ty: TypeDef, value: Expr, body: Expr)
    case LetRec(ty: TypeDef, value: Expr, body: Expr)

    case If(ty: TypeDef, scrut: Expr, ifTrue: Expr, ifFalse: Expr)

    case Instr(opcode: Int, args: List[Expr])

    // TODO: datatypes, records

    override def toString: String = this match
      case Expr.Local(i, _)            => s"'$i"
      case Expr.Global(name)           => name
      case Expr.IntLit(value)          => value.toString
      case Expr.BoolLit(value)         => if value then "True" else "False"
      case Expr.App(fn, arg)           => s"($fn $arg)"
      case Expr.Lam(_, body)           => s"(\\$body)"
      case Expr.Let(_, value, body)    => s"(let $value in $body)"
      case Expr.LetRec(_, value, body) => s"(letrec $value in $body)"
      case Expr.If(_, s, t, f)         => s"(if $s then $t else $f)"
      case Expr.Instr(opcode, args) => s"(instr $opcode ${args.mkString(" ")})"

    def shift(c: Int, d: Int): Expr = this match
      case l @ Expr.Local(i, ty) => if i < c then l else Expr.Local(i + d, ty)
      case g @ Expr.Global(_)    => g
      case i @ Expr.IntLit(_)    => i
      case b @ Expr.BoolLit(_)   => b
      case Expr.App(fn, arg)     => Expr.App(fn.shift(c, d), arg.shift(c, d))
      case Expr.Lam(ty, body)    => Expr.Lam(ty, body.shift(c + 1, d))
      case Expr.Let(ty, value, body) =>
        Expr.Let(ty, value.shift(c, d), body.shift(c + 1, d))
      case Expr.LetRec(ty, value, body) =>
        Expr.LetRec(ty, value.shift(c + 1, d), body.shift(c + 1, d))
      case Expr.If(ty, s, t, f) =>
        Expr.If(ty, s.shift(c, d), t.shift(c, d), f.shift(c, d))
      case Expr.Instr(opcode, args) =>
        Expr.Instr(opcode, args.map(_.shift(c, d)))

    def subst(i: Ix, v: Expr): Expr = this match
      case loc @ Expr.Local(j, _) => if j == i then v else loc
      case g @ Expr.Global(_)     => g
      case i @ Expr.IntLit(_)     => i
      case b @ Expr.BoolLit(_)    => b
      case Expr.App(fn, arg)      => Expr.App(fn.subst(i, v), arg.subst(i, v))
      case Expr.Lam(ty, body) => Expr.Lam(ty, body.subst(i + 1, v.shift(0, 1)))
      case Expr.Let(ty, value, body) =>
        Expr.Let(ty, value.subst(i + 1, v), body.subst(i + 1, v.shift(0, 1)))
      case Expr.LetRec(ty, value, body) =>
        Expr.LetRec(
          ty,
          value.subst(i + 1, v.shift(0, 1)),
          body.subst(i + 1, v.shift(0, 1))
        )
      case Expr.If(ty, s, t, f) =>
        Expr.If(ty, s.subst(i, v), t.subst(i, v), f.subst(i, v))
      case Expr.Instr(opcode, args) =>
        Expr.Instr(opcode, args.map(_.subst(i, v)))

    def beta(arg: Expr): Expr = subst(0, arg.shift(0, 1)).shift(0, -1)

    def free: IxMap = this match
      case Expr.Local(ix, ty)                 => Map(ix -> ty)
      case Expr.Global(_)                     => Map.empty
      case Expr.IntLit(_)                     => Map.empty
      case Expr.BoolLit(_)                    => Map.empty
      case Expr.App(fn, arg)                  => fn.free ++ arg.free
      case Expr.If(_, scrut, ifTrue, ifFalse) =>
        scrut.free ++ ifTrue.free ++ ifFalse.free
      case Expr.Instr(_, args) => args.map(_.free).fold(Map.empty)(_ ++ _)
      case Expr.Lam(_, body)   =>
        body.free
          .removed(0)
          .toList
          .map((k, v) => (k - 1, v))
          .toMap
      case Expr.Let(_, value, body) =>
        value.free ++ body.free
          .removed(0)
          .toList
          .map((k, v) => (k - 1, v))
          .toMap
      case Expr.LetRec(_, value, body) =>
        value.free
          .removed(0)
          .toList
          .map((k, v) => (k - 1, v))
          .toMap ++ body.free
          .removed(0)
          .toList
          .map((k, v) => (k - 1, v))
          .toMap

  // to JVM IR
  def toJVM(module: Module): JVM.Module =
    val newdefs = module.defs.flatMap(toJVM)
    JVM.Module(module.name, newdefs)

  private type EmitDef = (Name => JVM.Def) => Name

  private def toJVM(defn: Def): List[JVM.Def] = defn match
    case Def.Value(name, ty, value) =>
      println(s"===simplify $name===")
      val simplified = simplifyTopLevelUntilDone(eta(ty, value))
      val liftedDefs: mutable.ArrayBuffer[JVM.Def] = mutable.ArrayBuffer.empty
      given emitDef: EmitDef = k => {
        val x = s"$name$$${liftedDefs.size}"
        liftedDefs += k(x)
        x
      }
      println(s"===lift $name===")
      val lifted = lift(removeLams(simplified), ty.params.size, true, Set.empty)
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
      case Expr.Local(ix, _) => (None, Map(ix -> 1))
      case Expr.Global(_)    => (None, Map.empty)
      case Expr.IntLit(_)    => (None, Map.empty)
      case Expr.BoolLit(_)   => (None, Map.empty)

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
      case Expr.App(Expr.LetRec(ty, value, body), arg) =>
        val (res1, occ1) = simplify(value)
        val svalue = res1.getOrElse(value)
        val (res2, occ2, occ3) = simplify2(body, arg)
        val (sbody, sarg) = res2.getOrElse((body, arg))
        (
          Some(Expr.Let(ty, svalue, Expr.App(sbody, sarg.shift(0, 1)))),
          merge(merge(leave(occ1), occ2), shift(1, occ3))
        )
      case Expr.App(Expr.If(ty, s, t, f), arg) =>
        val (res1, occ1) = simplify(s)
        val ss = res1.getOrElse(s)
        val (res2, occ2, occ3) = simplify2(t, f)
        val (st, sf) = res2.getOrElse((t, f))
        val argty = ty.params.head
        (
          Some(
            Expr.Let(
              TypeDef(Nil, argty),
              arg,
              Expr.If(
                ty.tail,
                ss.shift(0, 1),
                Expr.App(st.shift(0, 1), Expr.Local(0, TypeDef(argty))),
                Expr.App(sf.shift(0, 1), Expr.Local(0, TypeDef(argty)))
              )
            )
          ),
          merge(merge(shift(1, occ1), shift(1, occ2)), shift(1, occ3))
        )
      case Expr.App(fn, arg) =>
        simplify2(fn, arg) match
          case (Some((fn, arg)), occ1, occ2) =>
            (Some(Expr.App(fn, arg)), merge(occ1, occ2))
          case (None, occ1, occ2) => (None, merge(occ1, occ2))

      case Expr.Instr(opcode, args) =>
        val (results, occ) =
          args.foldLeft[(List[Option[Expr]], Occ)]((Nil, Map.empty)) {
            case ((results, occ1), arg) =>
              simplify(arg) match
                case (res, occ2) => (results :+ res, merge(occ1, occ2))
          }
        if results.forall(_.isEmpty) then (None, occ)
        else
          (
            Some(
              Expr
                .Instr(opcode, results.zip(args).map((o, d) => o.getOrElse(d)))
            ),
            occ
          )

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

      case Expr.LetRec(ty, value, body) =>
        simplify2(value, body) match
          case (Some((value, body)), occ1, occ2) =>
            (
              Some(Expr.LetRec(ty, value, body)),
              merge(leave(occ1), leave(occ2))
            )
          case (None, occ1, occ2) =>
            val occ = merge(leave(occ1), leave(occ2))
            occ2.getOrElse(0, 0) match
              case 0 => (Some(body.shift(0, -1)), occ) // not used
              case _ if !isEtaExpanded(ty.params.size, value) => // eta-expand
                (Some(Expr.LetRec(ty, eta(ty, value), body)), occ)
              case _ => (None, occ)

      case Expr.If(ty, s, t, f) =>
        simplify(s) match
          case (Some(s), occ1) =>
            simplify2(t, f) match
              case (Some((t, f)), occ2, occ3) =>
                (Some(Expr.If(ty, s, t, f)), merge(merge(occ1, occ2), occ3))
              case (None, occ2, occ3) =>
                (Some(Expr.If(ty, s, t, f)), merge(merge(occ1, occ2), occ3))
          case (None, occ1) =>
            simplify2(t, f) match
              case (Some((t, f)), occ2, occ3) =>
                (Some(Expr.If(ty, s, t, f)), merge(merge(occ1, occ2), occ3))
              case (None, occ2, occ3) =>
                s match
                  case Expr.BoolLit(true)  => (Some(t), occ2)
                  case Expr.BoolLit(false) => (Some(f), occ3)
                  case _                   =>
                    (None, merge(merge(occ1, occ2), occ3))

  private def simplify2(e1: Expr, e2: Expr): (Option[(Expr, Expr)], Occ, Occ) =
    (simplify(e1), simplify(e2)) match
      case ((None, o1), (None, o2))         => (None, o1, o2)
      case ((Some(e1), o1), (None, o2))     => (Some((e1, e2)), o1, o2)
      case ((None, o1), (Some(e2), o2))     => (Some((e1, e2)), o1, o2)
      case ((Some(e1), o1), (Some(e2), o2)) => (Some((e1, e2)), o1, o2)

  private def isSmall(expr: IR.Expr): Boolean = expr match
    case Expr.Local(_, _) => true
    case Expr.Global(_)   => true
    case Expr.IntLit(_)   => true
    case Expr.BoolLit(_)  => true
    case _                => false

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
      ty.params.zipWithIndex.reverse
        .map((ty, ix) => Expr.Local(ix, TypeDef(ty)))
        .foldLeft(value.shift(0, ty.params.size))(Expr.App.apply)
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
  private def lift(
      expr: Expr,
      lvl: Int,
      tail: Boolean,
      jumps: Set[Int]
  )(using
      emitDef: EmitDef
  ): JVM.Expr =
    expr match
      case Expr.Local(ix, _) =>
        val l = lvl - ix - 1
        if jumps.contains(l) then JVM.Expr.Jump(l, Nil)
        else JVM.Expr.Local(l)
      case Expr.Global(x)  => JVM.Expr.Global(x, Nil)
      case Expr.IntLit(v)  => JVM.Expr.IntLit(v)
      case Expr.BoolLit(v) => JVM.Expr.BoolLit(v)

      case Expr.Lam(_, _) => throw new Exception("unexpected lambda")

      case app @ Expr.App(_, _) =>
        val (hd, args) = flattenApp(app)
        hd match
          case Expr.Global(x) =>
            JVM.Expr.Global(x, args.map(lift(_, lvl, false, jumps)))
          case Expr.Local(ix, _) =>
            val l = lvl - ix - 1
            if jumps.contains(l) then
              JVM.Expr.Jump(l, args.map(lift(_, lvl, false, jumps)))
            else throw new Exception("local in head position")
          case _ => throw new Exception("invalid fn in app")

      case Expr.Instr(opcode, args) =>
        JVM.Expr.Instr(opcode, args.map(lift(_, lvl, false, jumps)))

      case Expr.Let(ty, value, body)
          if tail && isUsedInTailOnly(0, body, true) =>
        JVM.Expr.Join(
          ty.params.map(toJVM),
          lift(removeLams(value), lvl + ty.params.size, false, jumps),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.Let(TypeDef(Nil, ty), value, body) =>
        JVM.Expr.Let(
          toJVM(ty),
          lift(value, lvl, false, jumps),
          lift(body, lvl + 1, tail, jumps)
        )

      case Expr.Let(ty, value, body) =>
        val newparams = value.free.toList
        val x = emitDef(x =>
          val ren = newparams.zipWithIndex
          val newvalue = ren.foldLeft(value) { case (v, ((ix, ty), newix)) =>
            v.subst(ix, Expr.Local(newix, ty))
          }
          JVM.Def.Function(
            x,
            newparams.map(p => toJVM(p._2.get)) ++ ty.params.map(toJVM),
            toJVM(ty.returnty),
            lift(
              removeLams(newvalue),
              ty.params.size + newparams.size,
              true,
              jumps
            )
          )
        )
        val call = newparams.foldLeft(Expr.Global(x)) { case (tm, (ix, ty)) =>
          Expr.App(tm, Expr.Local(ix, ty))
        }
        lift(body.beta(call), lvl, tail, jumps)

      case Expr.LetRec(ty, value, body)
          if tail && isUsedInTailOnly(0, value, true) &&
            isUsedInTailOnly(0, body, true) =>
        JVM.Expr.JoinRec(
          ty.params.map(toJVM),
          lift(removeLams(value), lvl + ty.params.size + 1, false, jumps + lvl),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.LetRec(ty, value, body) =>
        val newparams = value.free.removed(0).toList.map((k, v) => (k - 1, v))
        inline def call(x: Name): Expr = newparams.foldLeft(Expr.Global(x)) {
          case (tm, (ix, ty)) =>
            Expr.App(tm, Expr.Local(ix, ty))
        }
        val x = emitDef(x =>
          val body = value.beta(call(x))
          val ren = newparams.zipWithIndex
          val newbody = ren.foldLeft(body) { case (v, ((ix, ty), newix)) =>
            v.subst(ix, Expr.Local(newix, ty))
          }
          JVM.Def.Function(
            x,
            newparams.map(p => toJVM(p._2.get)) ++ ty.params.map(toJVM),
            toJVM(ty.returnty),
            lift(
              removeLams(newbody),
              ty.params.size + newparams.size,
              true,
              jumps
            )
          )
        )
        lift(body.beta(call(x)), lvl, tail, jumps)

      case Expr.If(TypeDef(Nil, _), s, t, f) =>
        JVM.Expr.If(
          lift(s, lvl, false, jumps),
          lift(t, lvl, tail, jumps),
          lift(f, lvl, tail, jumps)
        )
      case Expr.If(_, _, _, _) => throw new Exception("non-lifted if")

  @tailrec
  private def removeLams(expr: Expr): Expr = expr match
    case Expr.Lam(_, body) => removeLams(body)
    case expr              => expr

  private def flattenApp(expr: Expr): (Expr, List[Expr]) = expr match
    case Expr.App(fn, arg) =>
      val (hd, args) = flattenApp(fn)
      (hd, args :+ arg)
    case expr => (expr, Nil)

  private def isUsedInTailOnly(ix: Int, expr: Expr, tail: Boolean): Boolean =
    expr match
      case Expr.Local(j, _) if j == ix => tail
      case Expr.Local(_, _)            => true

      case Expr.Global(_)  => true
      case Expr.IntLit(_)  => true
      case Expr.BoolLit(_) => true

      case expr @ Expr.App(_, _) =>
        val (fn, args) = flattenApp(expr)
        val safeInArgs = args.forall(isUsedInTailOnly(ix, _, false))
        fn match
          case Expr.Local(j, _) if j == ix => tail && safeInArgs
          case expr => safeInArgs && isUsedInTailOnly(ix, expr, tail)

      case Expr.Instr(_, args) => args.forall(isUsedInTailOnly(ix, _, false))

      case Expr.If(_, s, t, f) =>
        isUsedInTailOnly(ix, s, false) &&
        isUsedInTailOnly(ix, t, tail) &&
        isUsedInTailOnly(ix, f, tail)

      case Expr.Lam(_, body)        => isUsedInTailOnly(ix + 1, body, tail)
      case Expr.Let(_, value, body) =>
        isUsedInTailOnly(ix, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
      case Expr.LetRec(_, value, body) =>
        isUsedInTailOnly(ix + 1, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
