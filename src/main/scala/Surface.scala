import scala.collection.mutable

object Surface:
  type Name = String

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double

  final case class TypeDef(params: List[Type], rty: Type)

  enum Expr:
    case Var(name: Name)
    case Lam(name: Name, body: Expr)
    case App(fn: Expr, arg: Expr)
    case Let(name: Name, ty: Option[TypeDef], value: Expr, body: Expr)
    case LetRec(name: Name, ty: TypeDef, value: Expr, body: Expr)

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case If(scrut: Expr, ifTrue: Expr, ifFalse: Expr)

    case Instr(opcode: Int, args: List[Expr])

  enum Def:
    case Value(name: Name, ty: Option[TypeDef], value: Expr)

  final case class Module(name: Name, defs: List[Def])

  // elaboration
  private final case class Ctx(
      globals: Map[Name, IR.TypeDef],
      env: List[(Name, IR.TypeDef)]
  ):
    def bindGlobal(x: Name, ty: IR.TypeDef): Ctx = Ctx(globals + (x -> ty), env)
    def bind(x: Name, ty: IR.TypeDef): Ctx = Ctx(globals, (x, ty) :: env)
  private object Ctx:
    def empty: Ctx = Ctx(Map.empty, Nil)

  def elaborate(mod: Module): IR.Module =
    var globalCtx: Ctx = Ctx.empty
    val ds = mod.defs.map { d =>
      val (ctx, ed) = elaborate(globalCtx, d)
      globalCtx = ctx
      ed
    }
    IR.Module(mod.name, ds)

  private def elaborate(ctx: Ctx, defn: Def): (Ctx, IR.Def) =
    defn match
      case Def.Value(x, ty, value) =>
        given localCtx: Ctx = ctx
        val (evalue, ety) = inferValue(ty, value)
        (ctx.bindGlobal(x, ety), IR.Def.Value(x, ety, evalue))

  private def elaborate(ty: TypeDef): IR.TypeDef =
    IR.TypeDef(ty.params.map(elaborate), elaborate(ty.rty))

  private def elaborate(ty: Type): IR.Type =
    ty match
      case Type.Boolean => IR.Type.Boolean
      case Type.Byte    => IR.Type.Byte
      case Type.Char    => IR.Type.Char
      case Type.Short   => IR.Type.Short
      case Type.Int     => IR.Type.Int
      case Type.Long    => IR.Type.Long
      case Type.Float   => IR.Type.Float
      case Type.Double  => IR.Type.Double

  private def inferValue(ty: Option[TypeDef], value: Expr)(using
      ctx: Ctx
  ): (IR.Expr, IR.TypeDef) =
    ty match
      case None     => infer(value)
      case Some(ty) =>
        val ety = elaborate(ty)
        (check(value, ety), ety)

  private def check(expr: Expr, exty: IR.TypeDef)(using ctx: Ctx): IR.Expr =
    expr match
      case Expr.Lam(x, body) =>
        exty match
          case IR.TypeDef(pty :: _, _) =>
            val ebody =
              check(body, exty.tail)(using ctx.bind(x, IR.TypeDef(pty)))
            IR.Expr.Lam(pty, ebody)
          case _ => throw new Exception(s"cannot check lambda against $exty")

      case Expr.Let(x, ty, value, body) =>
        val (evalue, ety) = inferValue(ty, value)
        val ebody = check(body, exty)(using ctx.bind(x, ety))
        IR.Expr.Let(ety, evalue, ebody)
      case Expr.LetRec(x, ty, value, body) =>
        val ety = elaborate(ty)
        val evalue = check(value, ety)(using ctx.bind(x, ety))
        val ebody = check(body, exty)(using ctx.bind(x, ety))
        IR.Expr.LetRec(ety, evalue, ebody)

      case Expr.If(c, t, f) =>
        val ec = check(c, IR.TypeDef(Nil, IR.Type.Boolean))
        val et = check(t, exty)
        val ef = check(f, exty)
        IR.Expr.If(exty, ec, et, ef)

      case Expr.Instr(op, args) =>
        val eargs = args.map(a => infer(a)._1)
        IR.Expr.Instr(op, eargs)

      case expr =>
        val (ie, ity) = infer(expr)
        if ity == exty then ie
        else throw new Exception(s"type mismatch: expected $exty, but got $ity")

  private def infer(expr: Expr)(using ctx: Ctx): (IR.Expr, IR.TypeDef) =
    expr match
      case Expr.Var(x) =>
        ctx.env.zipWithIndex.find { case ((y, _), _) => x == y } match
          case None =>
            ctx.globals.get(x) match
              case None     => throw new Exception(s"undefined variable $x")
              case Some(ty) => (IR.Expr.Global(x), ty)
          case Some(((_, ty), ix)) => (IR.Expr.Local(ix, ty), ty)
      case Expr.Lam(_, _)    => throw new Exception("cannot infer lambda")
      case Expr.App(fn, arg) =>
        val (efn, ty) = infer(fn)
        ty match
          case IR.TypeDef(pty :: _, _) =>
            val earg = check(arg, IR.TypeDef(pty))
            (IR.Expr.App(efn, earg), ty.tail)
          case _ =>
            throw new Exception(
              s"expected function type in application but got $ty"
            )
      case Expr.Let(x, ty, value, body) =>
        val (evalue, ety) = inferValue(ty, value)
        val (ebody, rty) = infer(body)(using ctx.bind(x, ety))
        (IR.Expr.Let(ety, evalue, ebody), rty)
      case Expr.LetRec(x, ty, value, body) =>
        val ety = elaborate(ty)
        val evalue = check(value, ety)(using ctx.bind(x, ety))
        val (ebody, rty) = infer(body)(using ctx.bind(x, ety))
        (IR.Expr.LetRec(ety, evalue, ebody), rty)

      case Expr.IntLit(value) =>
        (IR.Expr.IntLit(value), IR.TypeDef(IR.Type.Int))
      case Expr.BoolLit(value) =>
        (IR.Expr.BoolLit(value), IR.TypeDef(IR.Type.Boolean))

      case Expr.If(c, t, f) =>
        val ec = check(c, IR.TypeDef(Nil, IR.Type.Boolean))
        val (et, ety) = infer(t)
        val ef = check(f, ety)
        (IR.Expr.If(ety, ec, et, ef), ety)

      case Expr.Instr(n, _) =>
        throw new Exception(s"cannot infer instruction $n")

  // parsing
  private enum S:
    case Call(items: List[S])
    case Atom(value: String)

  def parse(name: Name, s: String): Module =
    val sexprs = parseS(s)
    val defs = parseDefs(sexprs)
    Module(name, defs)

  private def parseDefs(s: List[S]): List[Def] =
    s.map {
      case S.Call(List(S.Atom("def"), S.Atom(x), value)) =>
        Def.Value(x, None, parseExpr(value))
      case S.Call(List(S.Atom("def"), S.Atom(x), ty, value)) =>
        Def.Value(x, Some(parseTypeDef(ty)), parseExpr(value))
      case _ => throw new Exception("failed to parse def")
    }

  private def parseTypeDef(s: S): TypeDef =
    s match
      case S.Call(S.Atom("->") :: hd :: tl) =>
        val ts = (hd :: tl).map(parseType)
        TypeDef(ts.init, ts.last)
      case s => TypeDef(Nil, parseType(s))

  private def parseType(s: S): Type =
    s match
      case S.Atom("Boolean") => Type.Boolean
      case S.Atom("Byte")    => Type.Byte
      case S.Atom("Char")    => Type.Char
      case S.Atom("Short")   => Type.Short
      case S.Atom("Int")     => Type.Int
      case S.Atom("Long")    => Type.Long
      case S.Atom("Float")   => Type.Float
      case S.Atom("Double")  => Type.Double
      case _                 => throw new Exception("failed to parse type")

  private def parseExpr(s: S): Expr =
    s match
      case S.Atom("True")  => Expr.BoolLit(true)
      case S.Atom("False") => Expr.BoolLit(false)
      case S.Atom(x)       =>
        x.toIntOption match
          case Some(value) => Expr.IntLit(value)
          case None        => Expr.Var(x)
      case S.Call(List(S.Atom("fn"), S.Call(params), body)) =>
        val ps = params.map {
          case S.Atom(x) => x
          case _         =>
            throw new Exception(
              "failed to parse lambda with multiple parameters"
            )
        }
        ps.foldRight(parseExpr(body))(Expr.Lam.apply)
      case S.Call(List(S.Atom("fn"), S.Atom(x), body)) =>
        Expr.Lam(x, parseExpr(body))
      case S.Call(List(S.Atom("if"), cond, ifTrue, ifFalse)) =>
        Expr.If(parseExpr(cond), parseExpr(ifTrue), parseExpr(ifFalse))
      case S.Call(List(S.Atom("let"), S.Atom(x), value, body)) =>
        Expr.Let(x, None, parseExpr(value), parseExpr(body))
      case S.Call(List(S.Atom("let"), S.Atom(x), ty, value, body)) =>
        Expr.Let(x, Some(parseTypeDef(ty)), parseExpr(value), parseExpr(body))
      case S.Call(List(S.Atom("letrec"), S.Atom(x), ty, value, body)) =>
        Expr.LetRec(x, parseTypeDef(ty), parseExpr(value), parseExpr(body))
      case S.Call(S.Atom("instr") :: S.Atom(op) :: args) =>
        op.toIntOption match
          case None     => throw new Exception(s"invalid instruction $op")
          case Some(op) => Expr.Instr(op, args.map(parseExpr))
      case S.Call(List(hd)) => parseExpr(hd)
      case S.Call(hd :: tl) =>
        (hd :: tl).map(parseExpr).reduceLeft(Expr.App.apply)
      case _ => throw new Exception("failed to parse expression")

  private def parseS(s: String): List[S] =
    var i = 0
    var acc = ""
    var buf = mutable.ArrayBuffer.empty[S]
    val stack = mutable.ArrayBuffer.empty[mutable.ArrayBuffer[S]]
    inline def checkAcc(): Unit =
      if acc.nonEmpty then
        buf += S.Atom(acc)
        acc = ""
    while i < s.length do
      val c = s(i)
      i += 1
      if c.isWhitespace then checkAcc()
      else if c == '(' then
        checkAcc()
        stack += buf
        buf = mutable.ArrayBuffer.empty[S]
      else if c == ')' then
        checkAcc()
        if stack.isEmpty then throw new Exception(") without matching (")
        else
          val s = S.Call(buf.toList)
          buf = stack.last
          buf += s
          stack.remove(stack.length - 1)
      else acc += c
    if stack.nonEmpty then throw new Exception("unclosed (")
    checkAcc()
    buf.toList
