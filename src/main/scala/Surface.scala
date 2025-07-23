import scala.collection.mutable

object Surface:
  type Name = String

  final case class Type(name: Name)

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

    case Con(datatype: Option[Name], name: Name, args: List[Expr])
    case RecordCon(dx: Option[Name], args: List[Expr])

    case Field(scrut: Expr, ix: Either[Name, Int])
    case Case(scrut: Expr, cases: List[(Option[Name], List[Name], Expr)])

    case FiniteCon(datatype: Option[Name], name: Name)
    case FiniteCase(scrut: Expr, cases: List[(Option[Name], Expr)])

  final case class Constructor(
      name: Name,
      parameters: List[(Option[Name], Type)]
  )

  enum Def:
    case Value(name: Name, ty: Option[TypeDef], value: Expr)
    case Data(name: Name, constructors: List[Constructor])
    case Record(name: Name, fields: List[(Option[Name], Type)])
    case Finite(name: Name, constructors: List[Name])

  final case class Module(name: Name, defs: List[Def])

  // elaboration
  private enum DataKind:
    case ADT
    case Record
    case Finite

  private final case class Ctx(
      globals: Map[Name, IR.TypeDef],
      env: List[(Name, IR.TypeDef)],
      types: Map[Name, DataKind],
      recordparams: Map[Name, List[(Option[Name], IR.Type)]],
      dataparams: Map[Name, Map[Name, List[IR.Type]]],
      finiteparams: Map[Name, List[Name]]
  ):
    def bindGlobal(x: Name, ty: IR.TypeDef): Ctx =
      copy(globals = globals + (x -> ty))
    def bind(x: Name, ty: IR.TypeDef): Ctx = copy(env = (x, ty) :: env)
    def bindType(x: Name, kind: DataKind): Ctx =
      copy(types = types + (x -> kind))
    def setRecordParams(x: Name, ps: List[(Option[Name], IR.Type)]): Ctx =
      copy(recordparams = recordparams + (x -> ps))
    def setDataParams(x: Name, ps: Map[Name, List[IR.Type]]): Ctx =
      copy(dataparams = dataparams + (x -> ps))
    def setFiniteParams(x: Name, ps: List[Name]): Ctx =
      copy(finiteparams = finiteparams + (x -> ps))
  private object Ctx:
    def empty: Ctx =
      Ctx(Map.empty, Nil, Map.empty, Map.empty, Map.empty, Map.empty)

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
      case Def.Data(x, cons) =>
        given localCtx: Ctx = ctx.bindType(x, DataKind.ADT)
        val econs = cons.map { case Constructor(x, params) =>
          IR.Constructor(x, params.map((x, t) => (x, elaborate(t))))
        }
        (
          localCtx.setDataParams(
            x,
            econs.map(c => (c.name, c.parameters.map(_._2))).toMap
          ),
          IR.Def.Data(x, econs)
        )
      case Def.Record(x, fields) =>
        given localCtx: Ctx = ctx.bindType(x, DataKind.Record)
        val efields = fields.map((x, t) => (x, elaborate(t)))
        (
          localCtx.setRecordParams(x, efields),
          IR.Def.Record(x, efields)
        )
      case Def.Finite(x, cs) =>
        given localCtx: Ctx = ctx.bindType(x, DataKind.Finite)
        (
          localCtx.setFiniteParams(x, cs),
          IR.Def.Finite(x, cs.size)
        )

  private def elaborate(ty: TypeDef)(using ctx: Ctx): IR.TypeDef =
    IR.TypeDef(ty.params.map(elaborate), elaborate(ty.rty))

  private def elaborate(ty: Type)(using ctx: Ctx): IR.Type =
    val x = ty.name
    ctx.types.get(x) match
      case Some(DataKind.ADT)    => IR.Type.Data(x)
      case Some(DataKind.Record) => IR.Type.Record(x)
      case Some(DataKind.Finite) => IR.Type.Finite(x)
      case None                  =>
        x match
          case "Boolean" => IR.Type.Boolean
          case "Byte"    => IR.Type.Byte
          case "Char"    => IR.Type.Char
          case "Short"   => IR.Type.Short
          case "Int"     => IR.Type.Int
          case "Long"    => IR.Type.Long
          case "Float"   => IR.Type.Float
          case "Double"  => IR.Type.Double
          case x         => throw new Exception(s"undefined type $x")

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

      case Expr.Con(None, cx, args) =>
        exty match
          case IR.TypeDef(Nil, IR.Type.Data(dx)) => inferCon(dx, cx, args)
          case _                                 =>
            throw new Exception(
              s"cannot check data constructor against $exty"
            )
      case Expr.RecordCon(None, args) =>
        exty match
          case IR.TypeDef(Nil, IR.Type.Record(x)) => inferRecordCon(x, args)
          case _                                  =>
            throw new Exception(
              s"cannot check record constructor against $exty"
            )
      case Expr.FiniteCon(None, cx) =>
        exty match
          case IR.TypeDef(Nil, IR.Type.Finite(dx)) =>
            ctx.finiteparams(dx).zipWithIndex.find((cx2, _) => cx == cx2) match
              case None =>
                throw new Exception(s"undefined finite constructor $cx in $dx")
              case Some((_, i)) => IR.Expr.FiniteCon(dx, i)
          case _ =>
            throw new Exception(
              s"cannot check finite constructor against $exty"
            )

      case Expr.Case(scrut, cases) => inferCase(scrut, cases, Some(exty))._1
      case Expr.FiniteCase(scrut, cases) =>
        inferFinCase(scrut, cases, Some(exty))._1

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

      case Expr.Con(None, cx, _) =>
        throw new Exception(s"cannot infer con $cx without datatype")
      case Expr.Con(Some(dx), cx, args) =>
        (inferCon(dx, cx, args), IR.TypeDef(IR.Type.Data(dx)))

      case Expr.RecordCon(None, _) =>
        throw new Exception(
          "cannot infer record constructor without record type"
        )
      case Expr.RecordCon(Some(x), args) =>
        (inferRecordCon(x, args), IR.TypeDef(IR.Type.Record(x)))

      case Expr.FiniteCon(None, cx) =>
        throw new Exception(s"cannot infer finite con $cx without datatype")
      case Expr.FiniteCon(Some(dx), _) if !ctx.finiteparams.contains(dx) =>
        throw new Exception(s"undefined finite type $dx")
      case Expr.FiniteCon(Some(dx), cx) =>
        ctx.finiteparams(dx).zipWithIndex.find((cx2, _) => cx == cx2) match
          case None =>
            throw new Exception(s"undefined finite constructor $cx in $dx")
          case Some((_, i)) =>
            (IR.Expr.FiniteCon(dx, i), IR.TypeDef(IR.Type.Finite(dx)))

      case Expr.Field(scrut, ix) =>
        val (escrut, scrutty) = infer(scrut)
        scrutty match
          case IR.TypeDef(Nil, IR.Type.Record(x)) =>
            val ps = ctx.recordparams(x)
            val i = ix match
              case Left(px) =>
                ps.zipWithIndex.find {
                  case ((Some(y), _), _) if px == y => true
                  case _                            => false
                } match
                  case Some((_, i)) => i
                  case None => throw new Exception(s"field $px not found in $x")
              case Right(i) =>
                if i < 0 || i > ps.size then
                  throw new Exception(s"field index out of range: $i")
                else i
            (IR.Expr.Field(x, escrut, i), IR.TypeDef(ps(i)._2))
          case _ =>
            throw new Exception(
              s"expected record type in field but got $scrutty"
            )

      case Expr.Case(scrut, cases)       => inferCase(scrut, cases, None)
      case Expr.FiniteCase(scrut, cases) => inferFinCase(scrut, cases, None)

  private def inferRecordCon(x: Name, args: List[Expr])(using
      ctx: Ctx
  ): IR.Expr =
    ctx.recordparams.get(x) match
      case None     => throw new Exception(s"undefined record $x")
      case Some(ps) =>
        val eargs =
          args.zip(ps).map { case (e, (_, t)) => check(e, IR.TypeDef(t)) }
        IR.Expr.RecordCon(x, eargs)

  private def inferCon(dx: Name, cx: Name, args: List[Expr])(using
      ctx: Ctx
  ): IR.Expr =
    ctx.dataparams.get(dx) match
      case None     => throw new Exception(s"undefined data type $dx")
      case Some(cs) =>
        cs.get(cx) match
          case None =>
            throw new Exception(
              s"undefined constructor $cx in data type $dx"
            )
          case Some(ps) =>
            val eargs = args.zip(ps).map((e, t) => check(e, IR.TypeDef(t)))
            IR.Expr.Con(dx, cx, eargs)

  private def inferCase(
      scrut: Expr,
      cases: List[(Option[Name], List[Name], Expr)],
      exty: Option[IR.TypeDef]
  )(using ctx: Ctx): (IR.Expr, IR.TypeDef) =
    val (escrut, scrutty) = infer(scrut)
    scrutty match
      case IR.TypeDef(Nil, IR.Type.Data(dx)) =>
        val datactx = ctx.dataparams(dx)
        var rty: Option[IR.TypeDef] = exty
        val left = mutable.Set.from(datactx.keySet)
        val seen: mutable.Set[Name] = mutable.Set.empty
        val ecases = cases.zipWithIndex.map { case ((cx, ps, b), i) =>
          val last = i == cases.size - 1
          cx match
            case Some(cx) if seen.contains(cx) =>
              throw new Exception(s"duplicate case $cx")
            case Some(cx) if !left.contains(cx) =>
              throw new Exception(s"invalid case $cx for type $dx")
            case Some(cx) if last && (left.toSet - cx).nonEmpty =>
              throw new Exception(
                s"non-exhaustive case: ${(left.toSet - cx).mkString(", ")}"
              )
            case None if left.isEmpty =>
              throw new Exception(s"otherwise case matches against nothing")
            case None if !last =>
              throw new Exception(s"otherwise case should be last")

            case scx @ Some(cx) =>
              seen += cx
              left -= cx
              val types = datactx(cx)
              if types.size != ps.size then
                throw new Exception("parameter size mismatch in case")
              val localctx =
                ps.zip(types).foldLeft(ctx) { case (ctx, (x, ty)) =>
                  ctx.bind(x, IR.TypeDef(ty))
                }
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)(using localctx)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)(using localctx)
              val wrappedBody =
                types.zipWithIndex.foldRight(ebody.shift(types.size, 1)) {
                  case ((t, i), b) =>
                    val s = IR.Expr.Local(i, IR.TypeDef(IR.Type.Data(dx)))
                    IR.Expr.Let(
                      IR.TypeDef(t),
                      IR.Expr.DataField(dx, cx, s, i),
                      b
                    )
                }
              (scx, wrappedBody)

            case None =>
              if ps.nonEmpty then
                throw new Exception("otherwise case cannot have parameters")
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)
              (None, ebody)
        }
        rty match
          case None =>
            throw new Exception("could not figure out return type of case")
          case Some(rty) =>
            val (ecs, other) = ecases.last match
              case (None, b) => (ecases.init, Some(b))
              case _         => (ecases, None)
            (
              IR.Expr.Case(
                rty,
                dx,
                escrut,
                ecs.map((x, b) => (x.get, b)),
                other
              ),
              rty
            )
      case _ =>
        throw new Exception(
          s"expected data type in case but got $scrutty"
        )

  private def inferFinCase(
      scrut: Expr,
      cases: List[(Option[Name], Expr)],
      exty: Option[IR.TypeDef]
  )(using ctx: Ctx): (IR.Expr, IR.TypeDef) = ???

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
      case S.Call(S.Atom("data") :: S.Atom(x) :: consS) =>
        val cons = consS.map(parseConstructor)
        Def.Data(x, cons)
      case S.Call(S.Atom("record") :: S.Atom(x) :: fieldsS) =>
        val fields = fieldsS.map(parseTypeField)
        Def.Record(x, fields)
      case S.Call(S.Atom("finite") :: S.Atom(x) :: csS) =>
        val cs = csS.map {
          case S.Atom(x) => x
          case _         =>
            throw new Exception(s"unexpected name in finite type definition $x")
        }
        Def.Finite(x, cs)
      case _ => throw new Exception("failed to parse def")
    }

  private def parseConstructor(s: S): Constructor =
    s match
      case S.Atom(x)               => Constructor(x, Nil)
      case S.Call(S.Atom(x) :: ts) => Constructor(x, ts.map(parseTypeField))
      case _ => throw new Exception("failed to parse data constructor")

  private def parseTypeField(s: S): (Option[Name], Type) =
    s match
      case a @ S.Atom(_)               => (None, parseType(a))
      case S.Call(List(S.Atom(x), ty)) => (Some(x), parseType(ty))
      case _ => throw new Exception("failed to parse type field")

  private def parseTypeDef(s: S): TypeDef =
    s match
      case S.Call(S.Atom("->") :: hd :: tl) =>
        val ts = (hd :: tl).map(parseType)
        TypeDef(ts.init, ts.last)
      case s => TypeDef(Nil, parseType(s))

  private def parseType(s: S): Type =
    s match
      case S.Atom(x)   => Type(x)
      case S.Call(Nil) => Type("Unit")
      case _           => throw new Exception("failed to parse type")

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
      case S.Call(S.Atom("rec") :: S.Atom(x) :: args) =>
        Expr.RecordCon(Some(x), args.map(parseExpr))
      case S.Call(S.Atom("rec_") :: args) =>
        Expr.RecordCon(None, args.map(parseExpr))
      case S.Call(S.Atom("con") :: S.Atom(dx) :: S.Atom(cx) :: args) =>
        Expr.Con(Some(dx), cx, args.map(parseExpr))
      case S.Call(S.Atom("con_") :: S.Atom(cx) :: args) =>
        Expr.Con(None, cx, args.map(parseExpr))
      case S.Call(List(S.Atom("fin"), S.Atom(dx), S.Atom(cx))) =>
        Expr.FiniteCon(Some(dx), cx)
      case S.Call(List(S.Atom("fin_"), S.Atom(cx))) =>
        Expr.FiniteCon(None, cx)
      case S.Call(List(S.Atom("field"), S.Atom(x), scrut)) =>
        x.toIntOption match
          case None    => Expr.Field(parseExpr(scrut), Left(x))
          case Some(i) => Expr.Field(parseExpr(scrut), Right(i))
      case S.Call(S.Atom("case") :: scrut :: cases) =>
        Expr.Case(parseExpr(scrut), cases.map(parseCase))
      case S.Call(S.Atom("fincase") :: scrut :: cases) =>
        Expr.FiniteCase(parseExpr(scrut), cases.map(parseFinCase))
      case S.Call(List(hd)) => parseExpr(hd)
      case S.Call(hd :: tl) =>
        (hd :: tl).map(parseExpr).reduceLeft(Expr.App.apply)
      case S.Call(Nil) => Expr.RecordCon(None, Nil)
      case _           => throw new Exception("failed to parse expression")

  private def parseCase(s: S): (Option[Name], List[Name], Expr) =
    inline def name(x: String): Option[Name] =
      if x == "_" then None else Some(x)
    def params(ps: List[S]) = ps.map {
      case S.Atom(x) => x
      case _         => throw new Exception("failed to parse case parameters")
    }
    s match
      case S.Call(List(S.Atom(x), body)) => (name(x), Nil, parseExpr(body))
      case S.Call(List(S.Atom(x), S.Call(ps), body)) =>
        (name(x), params(ps), parseExpr(body))
      case _ => throw new Exception("failed to parse case")

  private def parseFinCase(s: S): (Option[Name], Expr) =
    inline def name(x: String): Option[Name] =
      if x == "_" then None else Some(x)
    s match
      case S.Call(List(S.Atom(x), body)) => (name(x), parseExpr(body))
      case _ => throw new Exception("failed to parse finite case")

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
