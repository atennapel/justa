package surface

import common.Common.*
import common.Common.Icit.*
import common.Common.Bind.*
import common.Debug.debug
import Surface.*

import scala.collection.mutable

object Parser:
  // tokenization
  private enum Token:
    case Identifier(name: String, posInfo: PosInfo)
    case Keyword(name: String, posInfo: PosInfo)
    case Symbol(name: String, posInfo: PosInfo)
    case Number(value: Int, posInfo: PosInfo)

    override def toString: String = this match
      case Identifier(x, _) => x
      case Keyword(x, _)    => x
      case Symbol(x, _)     => x
      case Number(x, _)     => x.toString

    def pos: PosInfo = this match
      case Token.Identifier(_, pos) => pos
      case Token.Keyword(_, pos)    => pos
      case Token.Symbol(_, pos)     => pos
      case Token.Number(_, pos)     => pos

  private val keywords: Set[String] =
    Set(
      "module",
      "import",
      "pub",
      "def",
      "primitive",
      "data",
      "record",
      "finite",
      "let",
      "rec",
      "instr",
      "match",
      "if",
      "then",
      "else"
    )
  private val symbols1: Set[Char] =
    Set(':', ';', '=', '\\', ',', '(', ')', '{', '}', '^', '`', '$', '|')
  private val symbols2: Map[Char, Set[Char]] =
    Map(':' -> Set('='), '-' -> Set('>'), '=' -> Set('>'))

  private def tokenize(s: String): Array[Token] =
    var i = 0
    val acc = mutable.ArrayBuffer.empty[Char]
    var inComment = false
    val tokens = mutable.ArrayBuffer.empty[Token]
    var col = 1
    var line = 1
    inline def pos: PosInfo = PosInfo(line, col)
    inline def handleAcc(): Unit =
      if acc.nonEmpty then
        tokens += tokenizeAcc(acc.mkString, pos)
        acc.clear()
    while i < s.length do
      val c = s(i)
      val next = if i + 1 < s.length then s(i + 1) else '\u0000'
      if inComment then
        if c == '\n' then inComment = false
      else if c == '-' && next == '-' then
        handleAcc()
        inComment = true
        i += 1
      else if symbol2Match(c, next) then
        handleAcc()
        tokens += Token.Symbol(s"$c$next", pos.subCol(1))
        i += 1
      else if symbols1.contains(c) then
        handleAcc()
        tokens += Token.Symbol(c.toString, pos)
      else if c.isWhitespace then handleAcc()
      else acc += c
      i += 1
      if c == '\n' then
        col = 1
        line += 1
      else col += 1
    handleAcc()
    tokens.toArray

  private def symbol2Match(a: Char, b: Char): Boolean =
    symbols2.get(a) match
      case None         => false
      case Some(follow) => follow.contains(b)

  private def tokenizeAcc(s: String, posAfter: PosInfo): Token = {
    val pos = posAfter.subCol(s.length)
    s.toIntOption match
      case Some(n)                      => Token.Number(n, pos)
      case None if keywords.contains(s) => Token.Keyword(s, pos)
      case None if s.length == 1 && symbols1.contains(s(0)) =>
        Token.Symbol(s, pos)
      case None if s.length == 2 && symbol2Match(s(0), s(1)) =>
        Token.Symbol(s, pos)
      case None => Token.Identifier(s, pos)
  }

  // parsing
  private final case class Ctx(
      var pos: PosInfo,
      var tokens: mutable.Buffer[Token]
  ):
    override def toString: String = s"Ctx($pos, [${tokens.mkString(" ")}])"

  class ParseError(val pos: PosInfo, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"parse error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ParseError(ctx.pos, msg)

  def parse(mod: String, s: String): Module =
    val tokens = tokenize(s)
    val buffer = tokens.toBuffer
    given ctx: Ctx = Ctx(PosInfo.start, buffer)
    val result = parseModule(mod)
    if ctx.tokens.nonEmpty then err(s"unparsed input at end of file")
    result

  // modules and imports
  private def parseModule(mod: String)(using ctx: Ctx): Module =
    keyword("module")
    val x = name()
    if x.expose != mod then
      err(s"module name does not match filename, expected $mod but got $x")
    val deps = mutable.Set.empty[Name]
    val imports =
      mutable.Map.empty[Name, (PosInfo, PosInfo, Name, Option[Name])]
    val moduleAliases = mutable.Map.empty[Name, Name]
    while tryKeyword("import") do
      val pos = ctx.pos
      val m = name()
      val xr = if trySymbol("=>") then Some(name()) else None
      moduleAliases += m -> xr.getOrElse(m)
      deps += m
      if trySymbol("(") then
        parseImports().foreach { (pos2, x, r) =>
          imports += x -> (pos, pos2, m, r)
        }
    val defs = parseDefs()
    Module(
      x,
      deps.toSet,
      imports.toMap,
      moduleAliases.toMap,
      defs
    )

  private def parseImports()(using
      ctx: Ctx
  ): List[(PosInfo, Name, Option[Name])] =
    if trySymbol(")") then Nil
    else
      val x = name()
      val pos = ctx.pos
      val r = if trySymbol("=>") then Some(name()) else None
      if trySymbol(",") then (pos, x, r) :: parseImports()
      else
        symbol(")")
        List((pos, x, r))

  // definitions
  private def parseDefs()(using ctx: Ctx): Defs =
    Defs(list(parseDef))

  private type DefParam = (PosInfo, ArgInfo, List[Bind], Option[Ty])
  private def hole(using ctx: Ctx) = Tm.Hole(ctx.pos, None)

  private def parseDef()(using ctx: Ctx): Option[Def] =
    val pub = tryKeyword("pub")
    if tryKeyword("def") then
      val (pos, isMeta, x, ty, body) = parseDefPart()
      if isMeta then Some(Def.D1(pos, pub, x, ty, body))
      else Some(Def.D0(pos, pub, x, ty, body))
    else if tryKeyword("primitive") then
      val pos = ctx.pos
      val x = name()
      val ps = parseParams()
      symbol(":")
      val rty = parseExpr()
      val ty = createPi(ps, rty, true)
      Some(Def.Primitive(pos, pub, x, ty))
    else if tryKeyword("data") then Some(parseDataDef(pub, DataKind.Data))
    else if tryKeyword("record") then Some(parseDataDef(pub, DataKind.Record))
    else if tryKeyword("finite") then Some(parseDataDef(pub, DataKind.Finite))
    else None

  private def createPi(ps: List[DefParam], rty: Ty, isMeta: Boolean)(using
      ctx: Ctx
  ): Tm =
    ps.foldRight(rty) { case ((p, ai, xs, opty), rty) =>
      val i = ai match
        case ArgInfo.Named(_) =>
          err(
            "named parameter not allowed for lets or top-level definitions"
          )
        case ArgInfo.Icit(i) => i
      val pty = opty.getOrElse(hole)
      xs.foldRight(rty) { (x, rty) =>
        val px = if isMeta then x else DontBind
        Tm.Pi(p, px, i, pty, rty)
      }
    }

  private def parseDefPart()(using
      ctx: Ctx
  ): (PosInfo, Boolean, Name, Option[Tm], Tm) =
    val pos = ctx.pos
    val x = name()
    val ps = parseParams()
    val prety = if trySymbol(":") then Some(parseExpr()) else None
    val isMeta =
      if trySymbol(":=") then false
      else
        symbol("=")
        true
    val prebody = parseExpr()
    val (ty, body) = prety match
      case None =>
        val body = ps.foldRight(prebody) { case ((p, i, xs, ty), b) =>
          xs.foldRight(b)((x, b) => Tm.Lam(p, x, i, ty, b))
        }
        (None, body)
      case Some(rty) =>
        val ty = createPi(ps, rty, isMeta)
        val body = ps.foldRight(prebody) { case ((p, i, xs, _), b) =>
          xs.foldRight(b)((x, b) => Tm.Lam(p, x, i, None, b))
        }
        (Some(ty), body)
    (pos, isMeta, x, ty, body)

  private def parseParams()(using ctx: Ctx): List[DefParam] = list(parseParam)

  private def parseGrouping()(using ctx: Ctx): (List[Bind], Option[Ty]) =
    val x = bind()
    val xs = list(tryBind)
    val ty = if trySymbol(":") then Some(parseExpr()) else None
    (x :: xs, ty)

  private def parseParam()(using ctx: Ctx): Option[DefParam] =
    if trySymbol("(") then
      val pos = ctx.pos
      val (xs, ty) = parseGrouping()
      symbol(")")
      Some((pos, ArgInfo.Icit(Expl), xs, ty))
    else if trySymbol("{") then
      val pos = ctx.pos
      val (xs, ty) = parseGrouping()
      val named = if trySymbol("=") then Some(name()) else None
      symbol("}")
      val arginfo = named.map(ArgInfo.Named.apply).getOrElse(ArgInfo.Icit(Impl))
      Some((pos, arginfo, xs, ty))
    else tryBind().map(x => (ctx.pos, ArgInfo.Icit(Expl), List(x), None))

  private def parseDataDef(pub: Boolean, kind: DataKind)(using
      ctx: Ctx
  ): Def =
    val pos = ctx.pos
    val dx = name()
    val continue = if trySymbol("=") then { trySymbol("|"); true }
    else trySymbol("|")
    val cons = if continue then
      val hd = parseDataCon(pub)
      val tl = mutable.ArrayBuffer.empty[Constructor]
      while trySymbol("|") do tl += parseDataCon(pub)
      hd :: tl.toList
    else Nil
    Def.Data(pos, pub, dx, kind, cons)

  private def parseDataCon(pub: Boolean)(using ctx: Ctx): Constructor =
    val cx = name()
    val pos = ctx.pos
    val ps = list(parseDataParam).flatten
    Constructor(pos, pub, cx, ps)

  private def parseDataParam()(using
      ctx: Ctx
  ): Option[List[(Bind, Ty)]] =
    if trySymbol("(") then
      val x = bind()
      val xs = list(tryBind)
      symbol(":")
      val ty = parseExpr()
      symbol(")")
      Some((x :: xs).map(x => (x, ty)))
    else tryParseAtom().map(t => List((DontBind, t)))

  // expressions
  private def tryParseAtom()(using ctx: Ctx): Option[Tm] =
    tryIdentifier() match
      case Some(x) if x.startsWith("_") =>
        Some(
          Tm.Hole(ctx.pos, if x.length == 1 then None else Some(Name(x.tail)))
        )
      case Some(x) if x.contains('.') =>
        val spl = x.split('.')
        val m = spl.init.mkString(".")
        val y = spl.last
        Some(Tm.Var(ctx.pos, Some(Name(m)), Name(y)))
      case Some(x) => Some(Tm.Var(ctx.pos, None, Name(x)))
      case None    =>
        if trySymbol("(") then
          val pos = ctx.pos
          if trySymbol(")") then Some(Tm.Unit(pos))
          else
            val expr = parseExpr()
            symbol(")")
            Some(expr)
        else if trySymbol("^") then Some(Tm.Lift(ctx.pos, parseAtom()))
        else if trySymbol("`") then Some(Tm.Quote(ctx.pos, parseAtom()))
        else if trySymbol("$") then Some(Tm.Splice(ctx.pos, parseAtom()))
        else
          tryNumber() match
            case None    => None
            case Some(v) => Some(Tm.IntLit(ctx.pos, v))

  private def parseAtom()(using ctx: Ctx): Tm =
    debug(s"parseAtom: $ctx")
    tryParseAtom().getOrElse(err("expected an expression"))

  private def parseExpr()(using ctx: Ctx): Tm =
    debug(s"parseExpr: $ctx")
    if tryKeyword("let") then
      val rec = tryKeyword("rec")
      parseLet(rec)
    else if trySymbol("\\") then parseLam()
    else if tryKeyword("match") then parseMatch()
    else if tryKeyword("if") then
      val pos = ctx.pos
      val c = parseExpr()
      keyword("then")
      val a = parseExpr()
      keyword("else")
      val b = parseExpr()
      Tm.If(pos, c, a, b)
    else if tryKeyword("instr") then
      val pos = ctx.pos
      val op = tryIdentifier() match
        case Some(x) => x
        case None    => number().toString
      val args = list(tryParseAtom)
      val instr = Tm.Instr(pos, op, args)
      if trySymbol("->") then
        val rest = apps()
        Tm.Pi(pos, DontBind, Expl, instr, rest)
      else instr
    else
      backtrack(piParam()) match
        case None    => apps()
        case Some(p) =>
          val ps = list(piParam)
          symbol("->")
          val rt = parseExpr()
          (p :: ps).foldRight(rt) { case ((pos, i, xs, ty), rt) =>
            xs.foldRight(rt)((x, rt) => Tm.Pi(pos, x, i, ty, rt))
          }

  private def piParam()(using
      ctx: Ctx
  ): Option[(PosInfo, Icit, List[Bind], Ty)] =
    if trySymbol("(") then
      if trySymbol(")") then None
      else
        val pos = ctx.pos
        val x = bind()
        val xs = list(tryBind)
        if trySymbol(":") then
          val ty = parseExpr()
          symbol(")")
          Some((pos, Expl, x :: xs, ty))
        else None
    else if trySymbol("{") then
      val pos = ctx.pos
      val (xs, prety) = parseGrouping()
      val ty = prety.getOrElse(hole)
      symbol("}")
      Some((pos, Impl, xs, ty))
    else None

  private def apps()(using ctx: Ctx): Tm =
    debug(s"apps: $ctx")
    val pos = ctx.pos
    val hd = parseAtom()
    val tl = list(parseArg)
    val optLam =
      if trySymbol("\\") then List((parseLam(), ArgInfo.Icit(Expl)))
      else if tryKeyword("match") then List((parseMatch(), ArgInfo.Icit(Expl)))
      else Nil
    val expr = (tl ++ optLam).foldLeft(hd) { case (f, (a, i)) =>
      Tm.App(a.pos, f, a, i)
    }
    if trySymbol("->") then
      val rt = parseExpr()
      Tm.Pi(pos, DontBind, Expl, expr, rt)
    else expr

  private def parseLet(rec: Boolean)(using ctx: Ctx): Tm =
    val (pos, isMeta, x, ty, value) = parseDefPart()
    symbol(";")
    val body = parseExpr()
    if isMeta then
      if rec then err("a meta let definition cannot be recursive")
      else Tm.Let1(pos, x, ty, value, body)
    else if rec then Tm.LetRec(pos, x, ty, value, body)
    else Tm.Let0(pos, x, ty, value, body)

  private def parseLam()(using ctx: Ctx): Tm =
    val ps = parseParams()
    symbol("=>")
    val body = parseExpr()
    ps.foldRight(body) { case ((p, a, xs, ty), b) =>
      xs.foldRight(b)((x, b) => Tm.Lam(p, x, a, ty, b))
    }

  private def parseMatch()(using ctx: Ctx): Tm =
    val pos = ctx.pos
    val scrut =
      if trySymbol("{") then None
      else
        val scrut = parseAtom()
        symbol("{")
        Some(scrut)
    val (cs, o) =
      if trySymbol("}") then (Nil, None)
      else
        trySymbol("|")
        parseCase() match
          case Left(c)   => (Nil, Some(c))
          case Right(hd) =>
            val tl = mutable.ArrayBuffer.empty[(PosInfo, Name, List[Bind], Tm)]
            var otherwiseFound: Option[(PosInfo, Tm)] = None
            while otherwiseFound.isEmpty && trySymbol("|") do
              parseCase() match
                case Left(o)  => otherwiseFound = Some(o)
                case Right(c) => tl += c
            (hd :: tl.toList, otherwiseFound)
    symbol("}")
    Tm.Match(pos, scrut, cs, o)

  private def parseCase()(using
      ctx: Ctx
  ): Either[(PosInfo, Tm), (PosInfo, Name, List[Bind], Tm)] =
    val cx = identifier()
    val pos = ctx.pos
    if cx == "_" then
      symbol("=>")
      val b = parseExpr()
      Left((pos, b))
    else
      val ps = list(tryBind)
      symbol("=>")
      val b = parseExpr()
      Right((pos, Name(cx), ps, b))

  private def parseArg()(using ctx: Ctx): Option[(Tm, ArgInfo)] =
    if trySymbol("{") then
      def next(arginfo: ArgInfo): Option[(Tm, ArgInfo)] =
        val a = parseExpr()
        symbol("}")
        Some((a, arginfo))
      backtrack {
        tryName() match
          case None    => Some(next(ArgInfo.Icit(Impl)))
          case Some(x) =>
            if trySymbol("=") then Some(next(ArgInfo.Named(x)))
            else None
      }.getOrElse(next(ArgInfo.Icit(Impl)))
    else tryParseAtom().map(a => (a, ArgInfo.Icit(Expl)))

  // parsers
  private def keyword(kw: String)(using ctx: Ctx): Unit =
    consumeMatch(s"keyword '$kw'"):
      case Token.Keyword(kw2, _) if kw == kw2 => Some(())
      case _                                  => None

  private def symbol(s: String)(using ctx: Ctx): Unit =
    consumeMatch(s"symbol '$s'"):
      case Token.Symbol(s2, _) if s == s2 => Some(())
      case _                              => None

  private def identifier()(using ctx: Ctx): String =
    consumeMatch("identifier"):
      case Token.Identifier(id, _) => Some(id)
      case _                       => None

  private def number()(using ctx: Ctx): Int =
    consumeMatch("number"):
      case Token.Number(n, _) => Some(n)
      case _                  => None

  private def tryKeyword(kw: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Keyword(kw2, _) if kw == kw2 => true
      case _                                  => false

  private def trySymbol(s: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Symbol(s2, _) if s == s2 => true
      case _                              => false

  private def tryIdentifier()(using ctx: Ctx): Option[String] =
    tryConsumeMatch:
      case Token.Identifier(x, _) => Some(x)
      case _                      => None

  private def tryNumber()(using ctx: Ctx): Option[Int] =
    tryConsumeMatch:
      case Token.Number(v, _) => Some(v)
      case _                  => None

  private def name()(using ctx: Ctx): Name = Name(identifier())
  private def tryName()(using ctx: Ctx): Option[Name] =
    tryIdentifier().map(Name.apply)
  private def bind()(using ctx: Ctx): Bind = fromString(identifier())
  private def tryBind()(using ctx: Ctx): Option[Bind] =
    tryIdentifier().map(fromString)

  // util
  private def consume()(using ctx: Ctx): Option[Token] =
    val tokens = ctx.tokens
    if tokens.isEmpty then None
    else
      val token = tokens.head
      val ret = Some(token)
      tokens.dropInPlace(1)
      ctx.pos = token.pos
      ret

  private def peek(using ctx: Ctx): Option[Token] = ctx.tokens.headOption

  private inline def consumeMatch[A](msg: String)(
      inline matcher: Token => Option[A]
  )(using ctx: Ctx): A =
    consume() match
      case Some(t) =>
        matcher(t) match
          case None    => err(s"expected $msg but got '$t'")
          case Some(v) => v
      case None => err(s"expected $msg but got end of input")

  private inline def tryConsumeMatch[A](inline matcher: Token => Option[A])(
      using ctx: Ctx
  ): Option[A] =
    peek match
      case Some(t) =>
        matcher(t) match
          case None => None
          case s    =>
            consume()
            s
      case _ => None

  private inline def tryConsumeMatchBool(inline matcher: Token => Boolean)(using
      ctx: Ctx
  ): Boolean =
    tryConsumeMatch(t => if matcher(t) then Some(()) else None).isDefined

  private def list[A](p: () => Option[A]): List[A] =
    p() match
      case None    => Nil
      case Some(x) => x :: list(p)

  private def mark()(using ctx: Ctx): Ctx =
    Ctx(ctx.pos, ctx.tokens.clone())

  private def restore(markedCtx: Ctx)(using ctx: Ctx): Unit =
    ctx.pos = markedCtx.pos
    ctx.tokens = markedCtx.tokens

  private def backtrack[A](action: => Option[A])(using
      ctx: Ctx
  ): Option[A] =
    val m = mark()
    action match
      case None => restore(m); None
      case s    => s
