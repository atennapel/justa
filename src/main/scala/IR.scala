import scala.annotation.tailrec
import scala.collection.mutable

import Common.*

object IR:
  type Name = String
  type Ix = Int

  final case class MName(module: Name, name: Name):
    override def toString: String = s"$module.$name"
    def toJvm: JvmName.MName = JvmName(module, name)

  final case class Module(name: Name, defs: List[Def])

  final case class Constructor(
      name: Name,
      parameters: List[(Option[Name], Type)]
  )

  enum Def:
    case Value(name: Name, ty: TypeDef, value: Expr)
    case Data(name: Name, constructors: List[Constructor])
    case Record(name: Name, fields: List[(Option[Name], Type)])
    case Finite(name: Name, amount: Int)

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double
    case Data(name: MName)
    case Record(name: MName)
    case Finite(name: MName)
    case Jvm(qualifiedName: String)
    case Array(ty: Type)

  final case class TypeDef(params: List[Type], io: Boolean, returnty: Type):
    def head: Type = params.head
    def tail: TypeDef = TypeDef(params.tail, io, returnty)
    def get: Type =
      if params.isEmpty && !io then returnty
      else err("expected non-function type")

  object TypeDef:
    def apply(ty: Type): TypeDef = TypeDef(Nil, false, ty)

  private type Occ = Map[Ix, (TypeDef, Int)]

  enum Expr:
    case Local(ix: Ix, ty: TypeDef)
    case Global(name: MName)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case App(fn: Expr, arg: Expr)
    case Lam(ty: Type, body: Expr)

    case Let(noinline: Boolean, ty: TypeDef, value: Expr, body: Expr)
    case LetRec(noinline: Boolean, ty: TypeDef, value: Expr, body: Expr)

    case If(ty: TypeDef, scrut: Expr, ifTrue: Expr, ifFalse: Expr)

    case Instr(
        instr: String,
        types: List[Type],
        returnty: Type,
        args: List[Expr]
    )

    case FiniteCon(name: MName, ix: Int)
    case FiniteCase(
        ty: TypeDef,
        dataname: MName,
        scrut: Expr,
        cases: List[(Int, Expr)],
        otherwise: Option[Expr]
    )

    case RecordCon(name: MName, args: List[Expr])
    case Field(name: MName, scrut: Expr, ix: Int)

    case Con(datatype: MName, name: Name, args: List[Expr])
    case DataField(dataname: MName, conname: Name, scrut: Expr, ix: Int)
    case Case(
        ty: TypeDef,
        dataname: MName,
        scrut: Expr,
        cases: List[(Name, Expr)],
        otherwise: Option[Expr]
    )

    override def toString: String = this match
      case Expr.Local(i, _)    => s"'$i"
      case Expr.Global(name)   => name.toString
      case Expr.IntLit(value)  => value.toString
      case Expr.BoolLit(value) => if value then "True" else "False"
      case Expr.App(fn, arg)   => s"($fn $arg)"
      case Expr.Lam(_, body)   => s"(\\$body)"
      case Expr.Let(noinline, _, value, body) =>
        s"(let${if noinline then " noinline" else ""} $value; $body)"
      case Expr.LetRec(noinline, _, value, body) =>
        s"(letrec${if noinline then " noinline" else ""} $value; $body)"
      case Expr.If(_, s, t, f)            => s"(if $s then $t else $f)"
      case Expr.Instr(opcode, _, _, args) =>
        s"(instr $opcode ${args.mkString(" ")})"
      case Expr.FiniteCon(x, i)         => s"($x $i)"
      case Expr.Con(d, c, args)         => s"($d $c ${args.mkString(" ")})"
      case Expr.RecordCon(d, args)      => s"($d ${args.mkString(" ")})"
      case Expr.Field(x, s, i)          => s"(field $x $s $i)"
      case Expr.DataField(dx, cx, s, i) => s"(field $dx $cx $s $i)"
      case Expr.Case(_, dx, s, cs, o)   =>
        s"(case $dx $s (${cs.map((cx, b) => s"$cx => $b").mkString("; ")}${o
            .map(o => s"; _ => $o")
            .getOrElse("")}))"
      case Expr.FiniteCase(_, dx, s, cs, o) =>
        s"(fincase $dx $s (${cs.map((cx, b) => s"$cx => $b").mkString("; ")}${o
            .map(o => s"; _ => $o")
            .getOrElse("")}))"

    def shift(c: Int, d: Int): Expr = this match
      case l @ Expr.Local(i, ty) => if i < c then l else Expr.Local(i + d, ty)
      case g @ Expr.Global(_)    => g
      case i @ Expr.IntLit(_)    => i
      case b @ Expr.BoolLit(_)   => b
      case f @ Expr.FiniteCon(_, _) => f
      case Expr.App(fn, arg)        => Expr.App(fn.shift(c, d), arg.shift(c, d))
      case Expr.Lam(ty, body)       => Expr.Lam(ty, body.shift(c + 1, d))
      case Expr.Let(ni, ty, value, body) =>
        Expr.Let(ni, ty, value.shift(c, d), body.shift(c + 1, d))
      case Expr.LetRec(ni, ty, value, body) =>
        Expr.LetRec(ni, ty, value.shift(c + 1, d), body.shift(c + 1, d))
      case Expr.If(ty, s, t, f) =>
        Expr.If(ty, s.shift(c, d), t.shift(c, d), f.shift(c, d))
      case Expr.Instr(opcode, ts, rt, args) =>
        Expr.Instr(opcode, ts, rt, args.map(_.shift(c, d)))
      case Expr.Con(dx, cx, args) =>
        Expr.Con(dx, cx, args.map(_.shift(c, d)))
      case Expr.RecordCon(dx, args) =>
        Expr.RecordCon(dx, args.map(_.shift(c, d)))
      case Expr.Field(x, s, i)          => Expr.Field(x, s.shift(c, d), i)
      case Expr.DataField(dx, cx, s, i) =>
        Expr.DataField(dx, cx, s.shift(c, d), i)
      case Expr.Case(ty, dx, scrut, cs, o) =>
        Expr.Case(
          ty,
          dx,
          scrut.shift(c, d),
          cs.map((cx, b) => (cx, b.shift(c + 1, d))),
          o.map(_.shift(c, d))
        )
      case Expr.FiniteCase(ty, dx, scrut, cs, o) =>
        Expr.FiniteCase(
          ty,
          dx,
          scrut.shift(c, d),
          cs.map((cx, b) => (cx, b.shift(c, d))),
          o.map(_.shift(c, d))
        )

    def subst(i: Ix, v: Expr): Expr = this match
      case loc @ Expr.Local(j, _)   => if j == i then v else loc
      case g @ Expr.Global(_)       => g
      case i @ Expr.IntLit(_)       => i
      case b @ Expr.BoolLit(_)      => b
      case f @ Expr.FiniteCon(_, _) => f
      case Expr.App(fn, arg)        => Expr.App(fn.subst(i, v), arg.subst(i, v))
      case Expr.Lam(ty, body)       =>
        Expr.Lam(ty, body.subst(i + 1, v.shift(0, 1)))
      case Expr.Let(ni, ty, value, body) =>
        Expr.Let(
          ni,
          ty,
          value.subst(i, v),
          body.subst(i + 1, v.shift(0, 1))
        )
      case Expr.LetRec(ni, ty, value, body) =>
        Expr.LetRec(
          ni,
          ty,
          value.subst(i + 1, v.shift(0, 1)),
          body.subst(i + 1, v.shift(0, 1))
        )
      case Expr.If(ty, s, t, f) =>
        Expr.If(ty, s.subst(i, v), t.subst(i, v), f.subst(i, v))
      case Expr.Instr(opcode, ts, rt, args) =>
        Expr.Instr(opcode, ts, rt, args.map(_.subst(i, v)))
      case Expr.Con(dx, cx, args) =>
        Expr.Con(dx, cx, args.map(_.subst(i, v)))
      case Expr.RecordCon(dx, args) =>
        Expr.RecordCon(dx, args.map(_.subst(i, v)))
      case Expr.Field(x, s, j)          => Expr.Field(x, s.subst(i, v), j)
      case Expr.DataField(dx, cx, s, j) =>
        Expr.DataField(dx, cx, s.subst(i, v), j)
      case Expr.Case(ty, dx, scrut, cs, o) =>
        Expr.Case(
          ty,
          dx,
          scrut.subst(i, v),
          cs.map((cx, b) => (cx, b.subst(i + 1, v.shift(0, 1)))),
          o.map(_.subst(i, v))
        )
      case Expr.FiniteCase(ty, dx, scrut, cs, o) =>
        Expr.FiniteCase(
          ty,
          dx,
          scrut.subst(i, v),
          cs.map((cx, b) => (cx, b.subst(i, v))),
          o.map(_.subst(i, v))
        )

    def beta(arg: Expr): Expr =
      subst(0, arg.shift(0, 1)).shift(0, -1)

    def free: Occ = {
      this match
        case Expr.Local(ix, ty)                 => Map(ix -> (ty, 1))
        case Expr.Global(_)                     => Map.empty
        case Expr.IntLit(_)                     => Map.empty
        case Expr.BoolLit(_)                    => Map.empty
        case Expr.FiniteCon(_, _)               => Map.empty
        case Expr.App(fn, arg)                  => merge(fn.free, arg.free)
        case Expr.If(_, scrut, ifTrue, ifFalse) =>
          merge(scrut.free, merge(ifTrue.free, ifFalse.free))
        case Expr.Instr(_, _, _, args) =>
          args.map(_.free).fold(Map.empty)(merge)
        case Expr.Con(_, _, args)    => args.map(_.free).fold(Map.empty)(merge)
        case Expr.RecordCon(_, args) => args.map(_.free).fold(Map.empty)(merge)
        case Expr.Field(_, s, _)     => s.free
        case Expr.DataField(_, _, s, _)  => s.free
        case Expr.Lam(_, body)           => leave(body.free)
        case Expr.Let(_, _, value, body) => merge(value.free, leave(body.free))
        case Expr.LetRec(_, _, value, body) =>
          merge(leave(value.free), leave(body.free))
        case Expr.Case(_, _, s, cs, o) =>
          merge(
            s.free,
            merge(
              cs.map((_, b) => leave(b.free)).fold(Map.empty)(merge),
              o.map(_.free).getOrElse(Map.empty)
            )
          )
        case Expr.FiniteCase(_, _, s, cs, o) =>
          merge(
            s.free,
            merge(
              cs.map((_, b) => b.free).fold(Map.empty)(merge),
              o.map(_.free).getOrElse(Map.empty)
            )
          )
    }

  // to JVM IR
  def toJvm(modules: List[Module]): List[Jvm.Module] = modules.map(toJvm)

  private def toJvm(module: Module): Jvm.Module =
    val newdefs = module.defs.flatMap(toJvm(module.name, _))
    Jvm.Module(JvmName(module.name), newdefs)

  private type EmitDef = (MName => Jvm.Def) => MName

  private def toJvm(mod: Name, defn: Def): List[Jvm.Def] = defn match
    case Def.Data(x, cs) =>
      List(
        Jvm.Def.Data(
          JvmName(x),
          cs.map(c =>
            Jvm.Constructor(
              JvmName(c.name),
              c.parameters.map((x, t) => (x.map(JvmName.apply), toJvm(t)))
            )
          )
        )
      )
    case Def.Record(x, fields) =>
      List(
        Jvm.Def.Record(
          JvmName(x),
          fields.map((x, t) => (x.map(JvmName.apply), toJvm(t)))
        )
      )
    case Def.Finite(x, amount) =>
      List(Jvm.Def.Finite(JvmName(x), amount))
    case Def.Value(name, ty, value) =>
      // println(s"===simplify $name===")
      val simplified = simplifyTopLevelUntilDone(eta(ty, value))
      val liftedDefs: mutable.ArrayBuffer[Jvm.Def] = mutable.ArrayBuffer.empty
      given emitDef: EmitDef = k => {
        val x = s"${name}_lifted_${liftedDefs.size}"
        val mx = MName(mod, x)
        liftedDefs += k(mx)
        mx
      }
      // println(simplified)
      // println(s"===lift $name===")
      val lifted = lift(removeLams(simplified), ty.params.size, true, Set.empty)
      // println(lifted)
      val defn =
        if ty.params.isEmpty && !ty.io then
          Jvm.Def.Value(JvmName(name), toJvm(ty.returnty), lifted)
        else
          Jvm.Def.Function(
            JvmName(name),
            ty.params.map(toJvm),
            toJvm(ty.returnty),
            lifted
          )
      defn :: liftedDefs.toList

  private def toJvm(ty: Type): Jvm.Type = ty match
    case Type.Boolean   => Jvm.Type.Boolean
    case Type.Byte      => Jvm.Type.Byte
    case Type.Char      => Jvm.Type.Char
    case Type.Short     => Jvm.Type.Short
    case Type.Int       => Jvm.Type.Int
    case Type.Long      => Jvm.Type.Long
    case Type.Float     => Jvm.Type.Float
    case Type.Double    => Jvm.Type.Double
    case Type.Data(x)   => Jvm.Type.Data(x.toJvm)
    case Type.Record(x) => Jvm.Type.Record(x.toJvm)
    case Type.Finite(x) => Jvm.Type.Finite(x.toJvm)
    case Type.Jvm(x)    => Jvm.Type.Jvm(x)
    case Type.Array(ty) => Jvm.Type.Array(toJvm(ty))

  // simplification:
  // - remove dead lets
  // - inline once-used lets
  // - inline variables and literals
  // - eta-expand lets and discrimination constructs
  @tailrec
  private def simplifyTopLevelUntilDone(expr: Expr): Expr =
    simplify(expr) match
      case None       => expr
      case Some(expr) => simplifyTopLevelUntilDone(expr)

  private def simplify(expr: Expr): Option[Expr] =
    expr match
      case Expr.Local(_, _)     => None
      case Expr.Global(_)       => None
      case Expr.IntLit(_)       => None
      case Expr.BoolLit(_)      => None
      case Expr.FiniteCon(_, _) => None

      case Expr.App(Expr.Lam(ty, body), arg) =>
        Some(Expr.Let(false, TypeDef(ty), arg, body))
      case Expr.App(Expr.Let(ni, ty, value, body), arg) =>
        Some(Expr.Let(ni, ty, value, Expr.App(body, arg.shift(0, 1))))
      case Expr.App(Expr.LetRec(ni, ty, value, body), arg) =>
        Some(Expr.LetRec(ni, ty, value, Expr.App(body, arg.shift(0, 1))))
      case Expr.App(Expr.If(ty, c, t, f), arg) =>
        val argty = TypeDef(ty.head)
        val local = Expr.Local(0, argty)
        Some(
          Expr.Let(
            false,
            argty,
            arg,
            Expr.If(
              ty.tail,
              c.shift(0, 1),
              Expr.App(t.shift(0, 1), local),
              Expr.App(f.shift(0, 1), local)
            )
          )
        )
      case Expr.App(Expr.Case(ty, dx, s, cs, o), arg) =>
        val argty = TypeDef(ty.head)
        val local = Expr.Local(0, argty)
        Some(
          Expr.Let(
            false,
            argty,
            arg,
            Expr.Case(
              ty.tail,
              dx,
              s.shift(0, 1),
              cs.map((cx, b) =>
                (cx, Expr.App(b.shift(1, 1), local.shift(0, 1)))
              ),
              o.map(o => Expr.App(o.shift(0, 1), local))
            )
          )
        )
      case Expr.App(Expr.FiniteCase(ty, dx, s, cs, o), arg) =>
        val argty = TypeDef(ty.head)
        val local = Expr.Local(0, argty)
        Some(
          Expr.Let(
            false,
            argty,
            arg,
            Expr.FiniteCase(
              ty.tail,
              dx,
              s.shift(0, 1),
              cs.map((cx, b) => (cx, Expr.App(b.shift(0, 1), local))),
              o.map(o => Expr.App(o.shift(0, 1), local))
            )
          )
        )
      case Expr.App(fn, arg) =>
        simplify2(fn, arg).map((f, a) => Expr.App(f, a))

      case Expr.Instr(opcode, ts, rt, args) =>
        simplifyN(args).map(Expr.Instr(opcode, ts, rt, _))
      case Expr.Con(dx, cx, args) =>
        simplifyN(args).map(Expr.Con(dx, cx, _))
      case Expr.RecordCon(dx, args) =>
        simplifyN(args).map(Expr.RecordCon(dx, _))

      case Expr.Lam(ty, body) =>
        simplify(body).map(Expr.Lam(ty, _))

      case Expr.Let(ni, ty, value, body) =>
        simplify2(value, body) match
          case Some((value, body)) => Some(Expr.Let(ni, ty, value, body))
          case None                =>
            val (_, n) = body.free.getOrElse(0, (0, 0))
            if !ni && n == 0 then Some(body.shift(0, -1))
            else if !ni && (n == 1 || isSmall(value)) then
              Some(body.beta(value))
            else if !isEtaExpanded(ty.params.size, value) then
              Some(Expr.Let(ni, ty, eta(ty, value), body))
            else None
      case Expr.LetRec(ni, ty, value, body) =>
        simplify2(value, body) match
          case Some((value, body)) => Some(Expr.LetRec(ni, ty, value, body))
          case None                =>
            val (_, n) = body.free(0)
            if !ni && n == 0 then Some(body.shift(0, -1))
            else if !isEtaExpanded(ty.params.size, value) then
              Some(Expr.LetRec(ni, ty, eta(ty, value), body))
            else None

      case Expr.If(_, Expr.BoolLit(true), t, _)  => Some(t)
      case Expr.If(_, Expr.BoolLit(false), _, f) => Some(f)
      case Expr.If(ty, c, t, f)                  =>
        simplifyN(List(c, t, f)) match
          case Some(List(c, t, f)) => Some(Expr.If(ty, c, t, f))
          case _                   => None

      case Expr.Field(_, Expr.RecordCon(_, args), i) => Some(args(i))
      case Expr.Field(x, s, i)                       =>
        simplify(s) match
          case None    => None
          case Some(s) => Some(Expr.Field(x, s, i))

      case Expr.DataField(_, _, Expr.Con(_, _, args), i) => Some(args(i))
      case Expr.DataField(dx, cx, s, i)                  =>
        simplify(s) match
          case None    => None
          case Some(s) => Some(Expr.DataField(dx, cx, s, i))

      case Expr.Case(_, dx, s @ Expr.Con(_, cx2, _), cs, o) =>
        cs.find((cx, _) => cx == cx2) match
          case None         => Some(o.get)
          case Some((_, b)) =>
            Some(Expr.Let(false, TypeDef(Type.Data(dx)), s, b))
      case Expr.Case(ty, dx, s, c, o) =>
        inline def go(
            c: List[(Name, Expr)],
            nc: List[Expr]
        ): List[(Name, Expr)] =
          c.zip(nc).map { case ((cx, _), b) => (cx, b) }
        inline def goO(o: Option[Expr], no: Option[Expr]): Option[Expr] =
          no match
            case None => o
            case _    => no
        (simplify(s), simplifyN(c.map((_, b) => b)), o.map(simplify)) match
          case (None, None, None)       => None
          case (None, None, Some(None)) => None

          case (Some(s), None, None)  => Some(Expr.Case(ty, dx, s, c, o))
          case (None, Some(nc), None) =>
            Some(Expr.Case(ty, dx, s, go(c, nc), o))
          case (None, None, Some(no)) =>
            Some(Expr.Case(ty, dx, s, c, goO(o, no)))

          case (Some(s), Some(nc), None) =>
            Some(Expr.Case(ty, dx, s, go(c, nc), o))
          case (Some(s), None, Some(no)) =>
            Some(Expr.Case(ty, dx, s, c, goO(o, no)))
          case (None, Some(nc), Some(no)) =>
            Some(Expr.Case(ty, dx, s, go(c, nc), goO(o, no)))

          case (Some(s), Some(nc), Some(no)) =>
            Some(Expr.Case(ty, dx, s, go(c, nc), goO(o, no)))

      case Expr.FiniteCase(_, _, Expr.FiniteCon(_, cx2), cs, o) =>
        cs.find((cx, _) => cx == cx2) match
          case None         => Some(o.get)
          case Some((_, b)) => Some(b)
      case Expr.FiniteCase(ty, dx, s, c, o) =>
        inline def go(
            c: List[(Int, Expr)],
            nc: List[Expr]
        ): List[(Int, Expr)] =
          c.zip(nc).map { case ((cx, _), b) => (cx, b) }
        inline def goO(o: Option[Expr], no: Option[Expr]): Option[Expr] =
          no match
            case None => o
            case _    => no
        (simplify(s), simplifyN(c.map((_, b) => b)), o.map(simplify)) match
          case (None, None, None)       => None
          case (None, None, Some(None)) => None

          case (Some(s), None, None)  => Some(Expr.FiniteCase(ty, dx, s, c, o))
          case (None, Some(nc), None) =>
            Some(Expr.FiniteCase(ty, dx, s, go(c, nc), o))
          case (None, None, Some(no)) =>
            Some(Expr.FiniteCase(ty, dx, s, c, goO(o, no)))

          case (Some(s), Some(nc), None) =>
            Some(Expr.FiniteCase(ty, dx, s, go(c, nc), o))
          case (Some(s), None, Some(no)) =>
            Some(Expr.FiniteCase(ty, dx, s, c, goO(o, no)))
          case (None, Some(nc), Some(no)) =>
            Some(Expr.FiniteCase(ty, dx, s, go(c, nc), goO(o, no)))

          case (Some(s), Some(nc), Some(no)) =>
            Some(Expr.FiniteCase(ty, dx, s, go(c, nc), goO(o, no)))

  private def simplify2(a: Expr, b: Expr): Option[(Expr, Expr)] =
    (simplify(a), simplify(b)) match
      case (None, None)       => None
      case (Some(a), None)    => Some((a, b))
      case (None, Some(b))    => Some((a, b))
      case (Some(a), Some(b)) => Some((a, b))

  private def simplifyN(args: List[Expr]): Option[List[Expr]] =
    val results = args.map(simplify)
    if results.forall(_.isEmpty) then None
    else Some(results.zip(args).map((o, d) => o.getOrElse(d)))

  // Expression should require no evaluation and no side-effects to be considered small
  private def isSmall(expr: IR.Expr): Boolean = expr match
    case Expr.Local(_, _)       => true
    case Expr.Global(_)         => true
    case Expr.IntLit(_)         => true
    case Expr.BoolLit(_)        => true
    case Expr.Con(_, _, Nil)    => true
    case Expr.RecordCon(_, Nil) => true
    case Expr.FiniteCon(_, _)   => true
    case _                      => false

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
        .foldLeft(value.shift(0, ty.params.size))((f, a) => Expr.App(f, a))
    ty.params.foldRight(newvalue)(Expr.Lam.apply)

  private def merge(o1: Occ, o2: Occ): Occ =
    val map = mutable.Map.empty[Ix, (TypeDef, Int)]
    o1.foreach((k, v) => map(k) = v)
    o2.foreach { (k, v) =>
      map(k) = map.get(k) match
        case None           => v
        case Some((ty, v2)) => (ty, v._2 + v2)
    }
    map.toMap

  private def shift(d: Int, o: Occ): Occ =
    o.toList.map((k, v) => (k + d, v)).toMap

  // leave a scope
  private def leave(o: Occ): Occ = shift(-1, o.removed(0))

  // might be needed in the future
  // @tailrec
  // private def leaveN(n: Int, o: Occ): Occ =
  //  if n == 0 then o else leaveN(n - 1, leave(o))

  // lifting
  // - lift function lets to top-level
  // - create join points where possible
  // - translate to JVM IR
  private def lift(
      expr: Expr,
      lvl: Int,
      tail: Boolean,
      jumps: Set[Int]
  )(using emitDef: EmitDef): Jvm.Expr =
    expr match
      case Expr.Local(ix, _) =>
        val l = lvl - ix - 1
        if jumps.contains(l) then Jvm.Expr.Jump(l, Nil)
        else Jvm.Expr.Local(l)
      case Expr.Global(x)       => Jvm.Expr.Global(x.toJvm, Nil)
      case Expr.IntLit(v)       => Jvm.Expr.IntLit(v)
      case Expr.BoolLit(v)      => Jvm.Expr.BoolLit(v)
      case Expr.FiniteCon(x, i) => Jvm.Expr.FiniteCon(x.toJvm, i)

      case Expr.Lam(_, _) => err("unexpected lambda")

      case app @ Expr.App(_, _) =>
        val (hd, args) = flattenApp(app)
        hd match
          case Expr.Global(x) =>
            Jvm.Expr.Global(x.toJvm, args.map(lift(_, lvl, false, jumps)))
          case Expr.Local(ix, _) =>
            val l = lvl - ix - 1
            if jumps.contains(l) then
              Jvm.Expr.Jump(l, args.map(lift(_, lvl, false, jumps)))
            else err("local in head position")
          case _ => err("invalid fn in app")

      case Expr.Instr(opcode, ts, rt, args) =>
        Jvm.Expr.Instr(
          opcode,
          ts.map(toJvm),
          toJvm(rt),
          args.map(lift(_, lvl, false, jumps))
        )
      case Expr.Con(dx, cx, args) =>
        Jvm.Expr.Con(
          dx.toJvm,
          JvmName(cx),
          args.map(lift(_, lvl, false, jumps))
        )
      case Expr.RecordCon(dx, args) =>
        Jvm.Expr.RecordCon(dx.toJvm, args.map(lift(_, lvl, false, jumps)))

      case Expr.Let(false, ty, value, body)
          if tail && isUsedInTailOnly(0, body, true) =>
        Jvm.Expr.Join(
          ty.params.map(toJvm),
          lift(removeLams(value), lvl + ty.params.size, false, jumps),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.Let(_, TypeDef(Nil, _, ty), value, body) =>
        Jvm.Expr.Let(
          toJvm(ty),
          lift(value, lvl, false, jumps),
          lift(body, lvl + 1, tail, jumps)
        )

      case Expr.Let(_, ty, value, body) =>
        val newparams = value.free.toList
        val x = emitDef { x =>
          val ren = newparams.zipWithIndex
          val newvalue =
            ren.foldLeft(value) { case (v, ((ix, (ty, _)), newix)) =>
              v.subst(ix, Expr.Local(newix, ty))
            }
          Jvm.Def.Function(
            JvmName(x.name),
            newparams.map(p => toJvm(p._2._1.get)) ++ ty.params.map(toJvm),
            toJvm(ty.returnty),
            lift(
              removeLams(newvalue),
              ty.params.size + newparams.size,
              true,
              jumps
            )
          )
        }
        val call = newparams.foldLeft(Expr.Global(x)) {
          case (tm, (ix, (ty, _))) =>
            Expr.App(tm, Expr.Local(ix, ty))
        }
        lift(body.beta(call), lvl, tail, jumps)

      case Expr.LetRec(_, ty, value, body)
          if tail && isUsedInTailOnly(0, value, true) &&
            isUsedInTailOnly(0, body, true) =>
        Jvm.Expr.JoinRec(
          ty.params.map(toJvm),
          lift(removeLams(value), lvl + ty.params.size + 1, false, jumps + lvl),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.LetRec(_, ty, value, body) =>
        val newparams = value.free.removed(0).toList.map((k, v) => (k - 1, v))
        inline def call(x: MName): Expr =
          newparams.foldLeft(Expr.Global(x)) { case (tm, (ix, (ty, _))) =>
            Expr.App(tm, Expr.Local(ix, ty))
          }
        val x = emitDef { x =>
          val body = value.beta(call(x))
          val ren = newparams.zipWithIndex
          val newbody = ren.foldLeft(body) { case (v, ((ix, (ty, _)), newix)) =>
            v.subst(ix, Expr.Local(newix, ty))
          }
          Jvm.Def.Function(
            JvmName(x.name),
            newparams.map(p => toJvm(p._2._1.get)) ++ ty.params.map(toJvm),
            toJvm(ty.returnty),
            lift(
              removeLams(newbody),
              ty.params.size + newparams.size,
              true,
              jumps
            )
          )
        }
        lift(body.beta(call(x)), lvl, tail, jumps)

      case Expr.If(_, s, t, f) =>
        Jvm.Expr.If(
          lift(s, lvl, false, jumps),
          lift(t, lvl, tail, jumps),
          lift(f, lvl, tail, jumps)
        )

      case Expr.Field(x, s, i) =>
        Jvm.Expr.Field(x.toJvm, lift(s, lvl, false, jumps), i)
      case Expr.DataField(dx, cx, s, i) =>
        Jvm.Expr.DataField(
          dx.toJvm,
          JvmName(cx),
          lift(s, lvl, false, jumps),
          i
        )

      case Expr.Case(_, dx, s, cs, o) =>
        Jvm.Expr.Case(
          dx.toJvm,
          lift(s, lvl, false, jumps),
          cs.map((cx, b) =>
            (JvmName(cx), b.free.contains(0), lift(b, lvl + 1, tail, jumps))
          ),
          o.map(lift(_, lvl, tail, jumps))
        )
      case Expr.FiniteCase(_, dx, s, cs, o) =>
        Jvm.Expr.FiniteCase(
          dx.toJvm,
          lift(s, lvl, false, jumps),
          cs.map((cx, b) => (cx, lift(b, lvl, tail, jumps))),
          o.map(lift(_, lvl, tail, jumps))
        )

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

      case Expr.Global(_)       => true
      case Expr.IntLit(_)       => true
      case Expr.BoolLit(_)      => true
      case Expr.FiniteCon(_, _) => true

      case expr @ Expr.App(_, _) =>
        val (fn, args) = flattenApp(expr)
        val safeInArgs = args.forall(isUsedInTailOnly(ix, _, false))
        fn match
          case Expr.Local(j, _) if j == ix => tail && safeInArgs
          case expr => safeInArgs && isUsedInTailOnly(ix, expr, tail)

      case Expr.Instr(_, _, _, args) =>
        args.forall(isUsedInTailOnly(ix, _, false))
      case Expr.Con(_, _, args) => args.forall(isUsedInTailOnly(ix, _, false))
      case Expr.RecordCon(_, args) =>
        args.forall(isUsedInTailOnly(ix, _, false))

      case Expr.If(_, s, t, f) =>
        isUsedInTailOnly(ix, s, false) &&
        isUsedInTailOnly(ix, t, tail) &&
        isUsedInTailOnly(ix, f, tail)

      case Expr.Field(_, s, _)        => isUsedInTailOnly(ix, s, false)
      case Expr.DataField(_, _, s, _) => isUsedInTailOnly(ix, s, false)

      case Expr.Case(_, _, s, cs, o) =>
        isUsedInTailOnly(ix, s, false) &&
        cs.forall((_, b) => isUsedInTailOnly(ix + 1, b, tail)) &&
        o.forall(isUsedInTailOnly(ix, _, tail))
      case Expr.FiniteCase(_, _, s, cs, o) =>
        isUsedInTailOnly(ix, s, false) &&
        cs.forall((_, b) => isUsedInTailOnly(ix, b, tail)) &&
        o.forall(isUsedInTailOnly(ix, _, tail))

      case Expr.Lam(_, body)           => isUsedInTailOnly(ix + 1, body, tail)
      case Expr.Let(_, _, value, body) =>
        isUsedInTailOnly(ix, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
      case Expr.LetRec(_, _, value, body) =>
        isUsedInTailOnly(ix + 1, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
