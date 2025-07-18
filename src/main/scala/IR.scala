import scala.annotation.tailrec
import scala.collection.mutable

object IR:
  type Name = String
  type Ix = Int

  final case class Module(name: Name, defs: List[Def])

  final case class Constructor(
      name: Name,
      parameters: List[(Option[Name], Type)]
  )

  enum Def:
    case Value(name: Name, ty: TypeDef, value: Expr)
    case Data(name: Name, constructors: List[Constructor])
    case Record(name: Name, fields: List[(Option[Name], Type)])

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double
    case Data(name: Name)
    case Record(name: Name)

  final case class TypeDef(params: List[Type], returnty: Type):
    def head: Type = params.head
    def tail: TypeDef = TypeDef(params.tail, returnty)
    def get: Type =
      if params.isEmpty then returnty
      else throw new Exception("expected non-function type")

  object TypeDef:
    def apply(ty: Type): TypeDef = TypeDef(Nil, ty)

  private type Occ = Map[Ix, (TypeDef, Int)]

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

    case RecordCon(name: Name, args: List[Expr])
    case Field(name: Name, scrut: Expr, ix: Int)

    case Con(datatype: Name, name: Name, args: List[Expr])
    case CaseVoid(scrut: Expr)
    case Case(
        ty: TypeDef,
        dataname: Name,
        conname: Name,
        scrut: Expr,
        body: Expr,
        other: Expr
    )
    case DataField(dataname: Name, conname: Name, scrut: Expr, ix: Int)

    override def toString: String = this match
      case Expr.Local(i, _)            => s"'$i"
      case Expr.Global(name)           => name
      case Expr.IntLit(value)          => value.toString
      case Expr.BoolLit(value)         => if value then "True" else "False"
      case Expr.App(fn, arg)           => s"($fn $arg)"
      case Expr.Lam(_, body)           => s"(\\$body)"
      case Expr.Let(_, value, body)    => s"(let $value; $body)"
      case Expr.LetRec(_, value, body) => s"(letrec $value; $body)"
      case Expr.If(_, s, t, f)         => s"(if $s then $t else $f)"
      case Expr.Instr(opcode, args) => s"(instr $opcode ${args.mkString(" ")})"
      case Expr.Con(d, c, args)     => s"($d $c ${args.mkString(" ")})"
      case Expr.RecordCon(d, args)  => s"($d ${args.mkString(" ")})"
      case Expr.Field(x, s, i)      => s"(field $x $s $i)"
      case Expr.DataField(dx, cx, s, i)  => s"(field $dx $cx $s $i)"
      case Expr.CaseVoid(s)              => s"(case $s)"
      case Expr.Case(_, dx, cx, s, b, o) =>
        s"(case $dx $cx $s $b $o)"

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
      case Expr.Con(dx, cx, args) =>
        Expr.Con(dx, cx, args.map(_.shift(c, d)))
      case Expr.RecordCon(dx, args) =>
        Expr.RecordCon(dx, args.map(_.shift(c, d)))
      case Expr.Field(x, s, i)          => Expr.Field(x, s.shift(c, d), i)
      case Expr.DataField(dx, cx, s, i) =>
        Expr.DataField(dx, cx, s.shift(c, d), i)
      case Expr.CaseVoid(s)               => Expr.CaseVoid(s.shift(c, d))
      case Expr.Case(ty, dx, cx, s, b, o) =>
        Expr.Case(
          ty,
          dx,
          cx,
          s.shift(c, d),
          b.shift(c + 1, d),
          o.shift(c + 1, d)
        )

    def subst(i: Ix, v: Expr): Expr = this match
      case loc @ Expr.Local(j, _) => if j == i then v else loc
      case g @ Expr.Global(_)     => g
      case i @ Expr.IntLit(_)     => i
      case b @ Expr.BoolLit(_)    => b
      case Expr.App(fn, arg)      => Expr.App(fn.subst(i, v), arg.subst(i, v))
      case Expr.Lam(ty, body)     =>
        Expr.Lam(ty, body.subst(i + 1, v.shift(0, 1)))
      case Expr.Let(ty, value, body) =>
        Expr.Let(
          ty,
          value.subst(i + 1, v),
          body.subst(i + 1, v.shift(0, 1))
        )
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
      case Expr.Con(dx, cx, args) =>
        Expr.Con(dx, cx, args.map(_.subst(i, v)))
      case Expr.RecordCon(dx, args) =>
        Expr.RecordCon(dx, args.map(_.subst(i, v)))
      case Expr.Field(x, s, j)          => Expr.Field(x, s.subst(i, v), j)
      case Expr.DataField(dx, cx, s, j) =>
        Expr.DataField(dx, cx, s.subst(i, v), j)
      case Expr.CaseVoid(s)               => Expr.CaseVoid(s.subst(i, v))
      case Expr.Case(ty, dx, cx, s, b, o) =>
        Expr.Case(
          ty,
          dx,
          cx,
          s.subst(i, v),
          b.subst(i + 1, v.shift(0, 1)),
          o.subst(i + 1, v.shift(0, 1))
        )

    def beta(arg: Expr): Expr =
      subst(0, arg.shift(0, 1)).shift(0, -1)

    def free: Occ = {
      this match
        case Expr.Local(ix, ty)                 => Map(ix -> (ty, 1))
        case Expr.Global(_)                     => Map.empty
        case Expr.IntLit(_)                     => Map.empty
        case Expr.BoolLit(_)                    => Map.empty
        case Expr.App(fn, arg)                  => merge(fn.free, arg.free)
        case Expr.If(_, scrut, ifTrue, ifFalse) =>
          merge(scrut.free, merge(ifTrue.free, ifFalse.free))
        case Expr.Instr(_, args)     => args.map(_.free).fold(Map.empty)(merge)
        case Expr.Con(_, _, args)    => args.map(_.free).fold(Map.empty)(merge)
        case Expr.RecordCon(_, args) => args.map(_.free).fold(Map.empty)(merge)
        case Expr.Field(_, s, _)     => s.free
        case Expr.DataField(_, _, s, _)  => s.free
        case Expr.Lam(_, body)           => leave(body.free)
        case Expr.Let(_, value, body)    => merge(value.free, leave(body.free))
        case Expr.LetRec(_, value, body) =>
          merge(leave(value.free), leave(body.free))
        case Expr.CaseVoid(s)            => s.free
        case Expr.Case(_, _, _, s, b, o) =>
          merge(s.free, merge(leave(b.free), leave(o.free)))
    }

  // to JVM IR
  final case class Ctx(
      datatypes: Map[String, Map[String, List[Type]]]
  )

  def toJvm(module: Module): Jvm.Module =
    given ctx: Ctx = createCtx(module.defs)
    val newdefs = module.defs.flatMap(toJvm)
    Jvm.Module(JvmName(module.name), newdefs)

  private def createCtx(defs: List[IR.Def]): Ctx =
    Ctx(defs.flatMap {
      case Def.Data(x, cs) =>
        Some(x -> cs.map(c => c.name -> c.parameters.map(_._2)).toMap)
      case _ => None
    }.toMap)

  private type EmitDef = (Name => Jvm.Def) => Name

  private def toJvm(defn: Def)(using ctx: Ctx): List[Jvm.Def] = defn match
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
    case Def.Value(name, ty, value) =>
      // println(s"===simplify $name===")
      val simplified = simplifyTopLevelUntilDone(eta(ty, value))
      val liftedDefs: mutable.ArrayBuffer[Jvm.Def] = mutable.ArrayBuffer.empty
      given emitDef: EmitDef = k => {
        val x = s"${name}_lifted_${liftedDefs.size}"
        liftedDefs += k(x)
        x
      }
      // println(simplified)
      // println(s"===lift $name===")
      val lifted = lift(removeLams(simplified), ty.params.size, true, Set.empty)
      // println(lifted)
      val defn =
        if ty.params.isEmpty then
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
    case Type.Data(x)   => Jvm.Type.Data(JvmName(x))
    case Type.Record(x) => Jvm.Type.Record(JvmName(x))

  // simplification:
  // - remove dead lets
  // - inline once-used lets
  // - inline variables and literals
  // - eta-expand lets and discrimination constructs
  @tailrec
  private def simplifyTopLevelUntilDone(expr: Expr)(using ctx: Ctx): Expr =
    simplify(expr) match
      case None       => expr
      case Some(expr) => simplifyTopLevelUntilDone(expr)

  private def simplify(expr: Expr)(using ctx: Ctx): Option[Expr] =
    expr match
      case Expr.Local(_, _) => None
      case Expr.Global(_)   => None
      case Expr.IntLit(_)   => None
      case Expr.BoolLit(_)  => None

      case Expr.App(Expr.Lam(ty, body), arg) =>
        Some(Expr.Let(TypeDef(Nil, ty), arg, body))
      case Expr.App(Expr.Let(ty, value, body), arg) =>
        Some(Expr.Let(ty, value, Expr.App(body, arg.shift(0, 1))))
      case Expr.App(Expr.LetRec(ty, value, body), arg) =>
        Some(Expr.LetRec(ty, value, Expr.App(body, arg.shift(0, 1))))
      case Expr.App(Expr.If(ty, c, t, f), arg) =>
        val argty = TypeDef(ty.head)
        val local = Expr.Local(0, argty)
        Some(
          Expr.Let(
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
      case Expr.App(v @ Expr.CaseVoid(_), _) =>
        Some(v) // TODO: now the arg is not evaluated, is that a problem?
      case Expr.App(Expr.Case(ty, dx, cx, s, b, o), arg) =>
        val argty = TypeDef(ty.head)
        val local = Expr.Local(0, argty)
        Some(
          Expr.Let(
            argty,
            arg,
            Expr.Case(
              ty.tail,
              dx,
              cx,
              s.shift(0, 1),
              Expr.App(b.shift(1, 1), local.shift(0, 1)),
              Expr.App(o.shift(1, 1), local.shift(0, 1))
            )
          )
        )
      case Expr.App(fn, arg) =>
        simplify2(fn, arg).map(Expr.App.apply)

      case Expr.Instr(opcode, args) =>
        simplifyN(args).map(Expr.Instr(opcode, _))
      case Expr.Con(dx, cx, args) =>
        simplifyN(args).map(Expr.Con(dx, cx, _))
      case Expr.RecordCon(dx, args) =>
        simplifyN(args).map(Expr.RecordCon(dx, _))

      case Expr.Lam(ty, body) =>
        simplify(body).map(Expr.Lam(ty, _))

      case Expr.Let(ty, value, body) =>
        simplify2(value, body) match
          case Some((value, body)) => Some(Expr.Let(ty, value, body))
          case None                =>
            val (_, n) = body.free.get(0).getOrElse((0, 0))
            if n == 0 then Some(body.shift(0, -1))
            else if n == 1 || isSmall(value) then Some(body.beta(value))
            else if !isEtaExpanded(ty.params.size, value) then
              Some(Expr.Let(ty, eta(ty, value), body))
            else None
      case Expr.LetRec(ty, value, body) =>
        simplify2(value, body) match
          case Some((value, body)) => Some(Expr.LetRec(ty, value, body))
          case None                =>
            val (_, n) = body.free(0)
            if n == 0 then Some(body.shift(0, -1))
            else if !isEtaExpanded(ty.params.size, value) then
              Some(Expr.LetRec(ty, eta(ty, value), body))
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

      case Expr.Case(_, dx, cx, s @ Expr.Con(_, cx2, _), b, _) if cx == cx2 =>
        Some(Expr.Let(TypeDef(Type.Data(dx)), s, b))
      case Expr.Case(_, dx, _, s @ Expr.Con(_, _, _), _, o) =>
        Some(Expr.Let(TypeDef(Type.Data(dx)), s, o))
      case Expr.Case(ty, dx, cx, s, b, o) =>
        (simplify(s), simplify2(b, o)) match
          case (None, None)            => None
          case (Some(s), None)         => Some(Expr.Case(ty, dx, cx, s, b, o))
          case (None, Some((b, o)))    => Some(Expr.Case(ty, dx, cx, s, b, o))
          case (Some(s), Some((b, o))) => Some(Expr.Case(ty, dx, cx, s, b, o))

      case Expr.CaseVoid(s) => simplify(s).map(Expr.CaseVoid.apply)

  private def simplify2(a: Expr, b: Expr)(using
      ctx: Ctx
  ): Option[(Expr, Expr)] =
    (simplify(a), simplify(b)) match
      case (None, None)       => None
      case (Some(a), None)    => Some((a, b))
      case (None, Some(b))    => Some((a, b))
      case (Some(a), Some(b)) => Some((a, b))

  private def simplifyN(
      args: List[Expr]
  )(using ctx: Ctx): Option[List[Expr]] =
    val results = args.map(simplify)
    if results.forall(_.isEmpty) then None
    else Some(results.zip(args).map((o, d) => o.getOrElse(d)))

  private def isSmall(expr: IR.Expr): Boolean = expr match
    case Expr.Local(_, _)       => true
    case Expr.Global(_)         => true
    case Expr.IntLit(_)         => true
    case Expr.BoolLit(_)        => true
    case Expr.Con(_, _, Nil)    => true
    case Expr.RecordCon(_, Nil) => true
    case _                      => false

  @tailrec
  private def isEtaExpanded(n: Int, expr: IR.Expr): Boolean =
    n match
      case 0 => true
      case n =>
        expr match
          case Expr.Lam(_, body) => isEtaExpanded(n - 1, body)
          case _                 => false

  private def eta(ty: TypeDef, value: Expr)(using ctx: Ctx): Expr =
    val newvalue =
      ty.params.zipWithIndex.reverse
        .map((ty, ix) => Expr.Local(ix, TypeDef(ty)))
        .foldLeft(value.shift(0, ty.params.size))(Expr.App.apply)
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

  @tailrec
  private def leaveN(n: Int, o: Occ): Occ =
    if n == 0 then o else leaveN(n - 1, leave(o))

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
      emitDef: EmitDef,
      ctx: Ctx
  ): Jvm.Expr =
    expr match
      case Expr.Local(ix, _) =>
        val l = lvl - ix - 1
        if jumps.contains(l) then Jvm.Expr.Jump(l, Nil)
        else Jvm.Expr.Local(l)
      case Expr.Global(x)  => Jvm.Expr.Global(JvmName(x), Nil)
      case Expr.IntLit(v)  => Jvm.Expr.IntLit(v)
      case Expr.BoolLit(v) => Jvm.Expr.BoolLit(v)

      case Expr.Lam(_, _) => throw new Exception("unexpected lambda")

      case app @ Expr.App(_, _) =>
        val (hd, args) = flattenApp(app)
        hd match
          case Expr.Global(x) =>
            Jvm.Expr.Global(JvmName(x), args.map(lift(_, lvl, false, jumps)))
          case Expr.Local(ix, _) =>
            val l = lvl - ix - 1
            if jumps.contains(l) then
              Jvm.Expr.Jump(l, args.map(lift(_, lvl, false, jumps)))
            else throw new Exception("local in head position")
          case _ => throw new Exception("invalid fn in app")

      case Expr.Instr(opcode, args) =>
        Jvm.Expr.Instr(opcode, args.map(lift(_, lvl, false, jumps)))
      case Expr.Con(dx, cx, args) =>
        Jvm.Expr.Con(
          JvmName(dx),
          JvmName(cx),
          args.map(lift(_, lvl, false, jumps))
        )
      case Expr.RecordCon(dx, args) =>
        Jvm.Expr.RecordCon(JvmName(dx), args.map(lift(_, lvl, false, jumps)))

      case Expr.Let(ty, value, body)
          if tail && isUsedInTailOnly(0, body, true) =>
        Jvm.Expr.Join(
          ty.params.map(toJvm),
          lift(removeLams(value), lvl + ty.params.size, false, jumps),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.Let(TypeDef(Nil, ty), value, body) =>
        Jvm.Expr.Let(
          toJvm(ty),
          lift(value, lvl, false, jumps),
          lift(body, lvl + 1, tail, jumps)
        )

      case Expr.Let(ty, value, body) =>
        val newparams = value.free.toList
        val x = emitDef(x =>
          val ren = newparams.zipWithIndex
          val newvalue =
            ren.foldLeft(value) { case (v, ((ix, (ty, _)), newix)) =>
              v.subst(ix, Expr.Local(newix, ty))
            }
          Jvm.Def.Function(
            JvmName(x),
            newparams.map(p => toJvm(p._2._1.get)) ++ ty.params.map(toJvm),
            toJvm(ty.returnty),
            lift(
              removeLams(newvalue),
              ty.params.size + newparams.size,
              true,
              jumps
            )
          )
        )
        val call = newparams.foldLeft(Expr.Global(x)) {
          case (tm, (ix, (ty, _))) =>
            Expr.App(tm, Expr.Local(ix, ty))
        }
        lift(body.beta(call), lvl, tail, jumps)

      case Expr.LetRec(ty, value, body)
          if tail && isUsedInTailOnly(0, value, true) &&
            isUsedInTailOnly(0, body, true) =>
        Jvm.Expr.JoinRec(
          ty.params.map(toJvm),
          lift(removeLams(value), lvl + ty.params.size + 1, false, jumps + lvl),
          lift(body, lvl + 1, tail, jumps + lvl)
        )

      case Expr.LetRec(ty, value, body) =>
        val newparams = value.free.removed(0).toList.map((k, v) => (k - 1, v))
        inline def call(x: Name): Expr = newparams.foldLeft(Expr.Global(x)) {
          case (tm, (ix, (ty, _))) =>
            Expr.App(tm, Expr.Local(ix, ty))
        }
        val x = emitDef(x =>
          val body = value.beta(call(x))
          val ren = newparams.zipWithIndex
          val newbody = ren.foldLeft(body) { case (v, ((ix, (ty, _)), newix)) =>
            v.subst(ix, Expr.Local(newix, ty))
          }
          Jvm.Def.Function(
            JvmName(x),
            newparams.map(p => toJvm(p._2._1.get)) ++ ty.params.map(toJvm),
            toJvm(ty.returnty),
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
        Jvm.Expr.If(
          lift(s, lvl, false, jumps),
          lift(t, lvl, tail, jumps),
          lift(f, lvl, tail, jumps)
        )
      case Expr.If(_, _, _, _) => throw new Exception("non-lifted if")

      case Expr.Field(x, s, i) =>
        Jvm.Expr.Field(JvmName(x), lift(s, lvl, false, jumps), i)
      case Expr.DataField(dx, cx, s, i) =>
        Jvm.Expr.DataField(
          JvmName(dx),
          JvmName(cx),
          lift(s, lvl, false, jumps),
          i
        )

      case Expr.CaseVoid(s) => Jvm.Expr.CaseVoid(lift(s, lvl, false, jumps))

      case Expr.Case(_, dx, cx, s, b, o) =>
        Jvm.Expr.Case(
          JvmName(dx),
          JvmName(cx),
          lift(s, lvl, false, jumps),
          lift(b, lvl + 1, tail, jumps),
          lift(o, lvl + 1, tail, jumps)
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

      case Expr.Global(_)  => true
      case Expr.IntLit(_)  => true
      case Expr.BoolLit(_) => true

      case expr @ Expr.App(_, _) =>
        val (fn, args) = flattenApp(expr)
        val safeInArgs = args.forall(isUsedInTailOnly(ix, _, false))
        fn match
          case Expr.Local(j, _) if j == ix => tail && safeInArgs
          case expr => safeInArgs && isUsedInTailOnly(ix, expr, tail)

      case Expr.Instr(_, args)  => args.forall(isUsedInTailOnly(ix, _, false))
      case Expr.Con(_, _, args) => args.forall(isUsedInTailOnly(ix, _, false))
      case Expr.RecordCon(_, args) =>
        args.forall(isUsedInTailOnly(ix, _, false))

      case Expr.If(_, s, t, f) =>
        isUsedInTailOnly(ix, s, false) &&
        isUsedInTailOnly(ix, t, tail) &&
        isUsedInTailOnly(ix, f, tail)
      case Expr.Field(_, s, _)        => isUsedInTailOnly(ix, s, false)
      case Expr.DataField(_, _, s, _) => isUsedInTailOnly(ix, s, false)

      case Expr.CaseVoid(s)            => isUsedInTailOnly(ix, s, false)
      case Expr.Case(_, _, _, s, b, o) =>
        isUsedInTailOnly(ix, s, false) && isUsedInTailOnly(ix + 1, b, tail)
        && isUsedInTailOnly(ix + 1, o, tail)

      case Expr.Lam(_, body)        => isUsedInTailOnly(ix + 1, body, tail)
      case Expr.Let(_, value, body) =>
        isUsedInTailOnly(ix, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
      case Expr.LetRec(_, value, body) =>
        isUsedInTailOnly(ix + 1, value, false) &&
        isUsedInTailOnly(ix + 1, body, tail)
