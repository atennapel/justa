import java.text.ParseException
import scala.collection.mutable

object Parser:
  // tokenization
  private enum Token:
    case Identifier(name: String, index: Int)
    case Keyword(name: String, index: Int)
    case Symbol(name: String, index: Int)
    case Number(value: Int, index: Int)

    case Parens(tokens: Array[Token], index: Int)
    case Brackets(tokens: Array[Token], index: Int)
    case Braces(tokens: Array[Token], index: Int)

    override def toString: String = this match
      case Identifier(x, _) => x
      case Keyword(x, _)    => x
      case Symbol(x, _)     => x
      case Number(x, _)     => x.toString
      case Parens(ts, _)    => ts.mkString("(", " ", ")")
      case Brackets(ts, _)  => ts.mkString("[", " ", "]")
      case Braces(ts, _)    => ts.mkString("{", " ", "}")

    def getIndex: Int = this match
      case Identifier(_, i) => i
      case Keyword(_, i)    => i
      case Symbol(_, i)     => i
      case Number(_, i)     => i
      case Parens(_, i)     => i
      case Brackets(_, i)   => i
      case Braces(_, i)     => i

  private val keywords: Set[String] =
    Set(
      "module",
      "import",
      "def",
      "finite",
      "record",
      "data",
      "if",
      "then",
      "else",
      "let",
      "rec",
      "true",
      "false",
      "instr",
      "con",
      "rec",
      "fin",
      "IO",
      "returnIO",
      "bindIO",
      "field",
      "finmatch",
      "match",
      "case"
    )
  private val symbols1: Set[Char] = Set(':', ';', '=', '\\', '|')
  private val symbols2: Map[Char, Set[Char]] =
    Map(':' -> Set('='), '-' -> Set('>'), '=' -> Set('>'))
  private val openingBrackets: Map[Char, Char] =
    Map('(' -> ')', '[' -> ']', '{' -> '}')
  private val closingBrackets: Map[Char, Char] =
    Map(')' -> '(', ']' -> '[', '}' -> '{')

  private def tokenize(s: String): Array[Token] =
    if s.isEmpty then Array.empty
    else
      var i = 0
      val acc = mutable.ArrayBuffer.empty[Char]
      var inComment = false
      val brackets = mutable.ArrayBuffer.empty[(Char, Int)]
      val stack = mutable.ArrayBuffer.empty[mutable.ArrayBuffer[Token]]
      var tokens = mutable.ArrayBuffer.empty[Token]
      inline def handleAcc()(using index: Int): Unit =
        if acc.nonEmpty then
          tokens += tokenizeAcc(acc.mkString)
          acc.clear()
      while i < s.length do
        given index: Int = i
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
          tokens += Token.Symbol(s"$c$next", i)
          i += 1
        else if symbols1.contains(c) then
          handleAcc()
          tokens += Token.Symbol(c.toString, i)
        else if c.isWhitespace then handleAcc()
        else if openingBrackets.contains(c) then
          handleAcc()
          brackets += ((c, i))
          stack += tokens
          tokens = mutable.ArrayBuffer.empty[Token]
        else if closingBrackets.contains(c) then
          val ex = closingBrackets(c)
          if brackets.isEmpty then
            err(s"Closing bracket '$c' without matching opening bracket '$ex'")
          else
            val (last, _) = brackets.last
            brackets.dropRightInPlace(1)
            if last == ex then
              handleAcc()
              val token = handleBracket(ex, tokens.toArray)
              tokens = stack.last
              stack.dropRightInPlace(1)
              tokens += token
            else err(s"Mismatching brackets, expected '$ex' but got '$last'")
        else acc += c
        i += 1
      handleAcc()(using s.length - 1)
      if brackets.nonEmpty then
        val (c, i) = brackets.last
        err(s"Unclosed bracket '$c'")(using i)
      tokens.toArray

  private def handleBracket(c: Char, tokens: Array[Token])(using
      index: Int
  ): Token =
    c match
      case '(' => Token.Parens(tokens, index)
      case '[' => Token.Brackets(tokens, index)
      case '{' => Token.Braces(tokens, index)
      case _   => err(s"Invalid bracket '$c'")

  private def symbol2Match(a: Char, b: Char): Boolean =
    symbols2.get(a) match
      case None         => false
      case Some(follow) => follow.contains(b)

  private def tokenizeAcc(s: String)(using index: Int): Token =
    s.toIntOption match
      case Some(n)                      => Token.Number(n, index)
      case None if keywords.contains(s) => Token.Keyword(s, index)
      case None if s.length == 1 && symbols1.contains(s(0)) =>
        Token.Symbol(s, index)
      case None if s.length == 2 && symbol2Match(s(0), s(1)) =>
        Token.Symbol(s, index)
      case None => Token.Identifier(s, index)

  // parsing
  private final case class Ctx(tokens: mutable.Buffer[Token])

  def parse(mod: String, s: String): Surface.Module =
    val tokens = tokenize(s)
    parseNestedUntilEnd(tokens) { parseModule(mod) }

  private def parseModule(mod: String)(using ctx: Ctx): Surface.Module =
    expectKeyword("module")
    val x = expectIdentifier()
    if x != mod then
      err(s"Module name does not match filename, expected $mod but got $x")(
        using -1
      )
    val imports = mutable.Set.empty[String]
    while maybeKeyword("import") do
      dropToken()
      imports += expectIdentifier()
    val defs = parseDefs()
    Surface.Module(x, imports.toSet, defs)

  private def parseDefs()(using ctx: Ctx): List[Surface.Def] =
    parseDef() match
      case None    => Nil
      case Some(d) => d :: parseDefs()

  private def parseDef()(using ctx: Ctx): Option[Surface.Def] =
    if maybeKeyword("def") then
      dropToken()
      val x = expectIdentifier()
      val ty = if maybeSymbol(":") then
        dropToken()
        Some(parseTypeDef())
      else None
      expectSymbol("=")
      val body = parseExprBody()
      Some(Surface.Def.Value(x, ty, body))
    else if maybeKeyword("finite") then
      dropToken()
      val x = expectIdentifier()
      val cs =
        if maybeSymbol("=") then
          dropToken()
          expectIdentifier() :: parseFiniteNames()
        else Nil
      Some(Surface.Def.Finite(x, cs))
    else if maybeKeyword("record") then
      dropToken()
      val x = expectIdentifier()
      val ps = parseDataParams()
      Some(Surface.Def.Record(x, ps))
    else if maybeKeyword("data") then
      dropToken()
      val x = expectIdentifier()
      val cs =
        if maybeSymbol("=") then
          dropToken()
          parseDataCon() :: parseDataCons()
        else Nil
      Some(Surface.Def.Data(x, cs))
    else None

  private def parseFiniteNames()(using ctx: Ctx): List[String] =
    if maybeSymbol("|") then
      dropToken()
      expectIdentifier() :: parseFiniteNames()
    else Nil

  private def parseDataParams()(using
      ctx: Ctx
  ): List[(Option[String], Surface.Type)] =
    parseDataParam() match
      case None        => Nil
      case Some(param) => param :: parseDataParams()

  private def parseDataParam()(using
      ctx: Ctx
  ): Option[(Option[String], Surface.Type)] =
    parseType() match
      case Some(ty) => Some((None, ty))
      case None     =>
        nextToken(true) match
          case Some(Token.Parens(ts, ix)) =>
            dropToken()
            parseNestedUntilEnd(ts) {
              val x = expectIdentifier()
              expectSymbol(":")
              parseType() match
                case None =>
                  err(s"Failed to parse type in data parameter $x")(using ix)
                case Some(ty) =>
                  Some((if x == "_" then None else Some(x), ty))
            }
          case _ => None

  private def parseDataCons()(using ctx: Ctx): List[Surface.Constructor] =
    if maybeSymbol("|") then
      dropToken()
      parseDataCon() :: parseDataCons()
    else Nil

  private def parseDataCon()(using ctx: Ctx): Surface.Constructor =
    val x = expectIdentifier()
    val ps = parseDataParams()
    Surface.Constructor(x, ps)

  private def parseTypeDef()(using ctx: Ctx): Surface.TypeDef = {
    if maybeKeyword("IO") then
      val ix = dropToken().getIndex
      parseType() match
        case Some(ty) =>
          Surface.TypeDef(Nil, true, ty)
        case _ => err("Failed to parse type")(using ix)
    else
      parseType() match
        case Some(ty) =>
          val (io, rest) = parseTypes()
          val ts = ty :: rest
          Surface.TypeDef(ts.init, io, ts.last)
        case _ => err("Failed to parse type")(using -1)
  }

  private def parseTypes()(using ctx: Ctx): (Boolean, List[Surface.Type]) =
    if maybeSymbol("->") then
      val index = dropToken().getIndex
      val io = if maybeKeyword("IO") then
        dropToken()
        true
      else false
      parseType() match
        case Some(ty) if io => (true, List(ty))
        case Some(ty)       =>
          val (io, rest) = parseTypes()
          (io, ty :: rest)
        case None => err("Failed to parse type")(using index)
    else (false, Nil)

  private def parseType()(using ctx: Ctx): Option[Surface.Type] =
    nextToken(true) match
      case Some(Token.Identifier(x, _)) =>
        dropToken()
        if x.startsWith("&") then Some(Surface.Type.Jvm(x.tail))
        else Some(Surface.Type.Type(parseMName(x)))
      case _ => None

  private def parseMName(x: String): Surface.MName =
    if x.contains('.') then
      val spl = x.split('.')
      Surface.MName(Some(spl.init.mkString(".")), spl.last)
    else Surface.MName(None, x)

  private def parseExpr()(using ctx: Ctx): Surface.Expr =
    tryParseExpr() match
      case Left((msg, ix)) => err(msg)(using ix)
      case Right(expr)     => expr

  private def tryParseExpr()(using
      ctx: Ctx
  ): Either[(String, Int), Surface.Expr] =
    nextToken(true) match
      case Some(Token.Number(n, _)) =>
        dropToken()
        Right(Surface.Expr.IntLit(n))
      case Some(Token.Keyword("true", _)) =>
        dropToken()
        Right(Surface.Expr.BoolLit(true))
      case Some(Token.Keyword("false", _)) =>
        dropToken()
        Right(Surface.Expr.BoolLit(false))
      case Some(Token.Identifier(x, _)) =>
        dropToken()
        Right(Surface.Expr.Var(parseMName(x)))
      case Some(Token.Symbol("\\", _)) =>
        dropToken()
        val xs = parseIdents()
        expectSymbol("=>")
        val body = parseExprBody()
        Right(xs.foldRight(body)(Surface.Expr.Lam.apply))
      case Some(Token.Keyword("let", ix)) =>
        dropToken()
        val rec = if maybeKeyword("rec") then
          dropToken()
          true
        else false
        val x = expectIdentifier()
        val ty = if maybeSymbol(":") then
          dropToken()
          Some(parseTypeDef())
        else None
        expectSymbol("=")
        val value = parseExprBody()
        expectSymbol(";")
        val body = parseExprBody()
        if rec then
          ty match
            case None =>
              err("Let rec expression requires type annotation")(using ix)
            case Some(ty) => Right(Surface.Expr.LetRec(x, ty, value, body))
        else Right(Surface.Expr.Let(x, ty, value, body))
      case Some(Token.Keyword("if", _)) =>
        dropToken()
        val cond = parseExprBody()
        expectKeyword("then")
        val ifTrue = parseExprBody()
        expectKeyword("else")
        val ifFalse = parseExprBody()
        Right(Surface.Expr.If(cond, ifTrue, ifFalse))
      case Some(Token.Keyword("instr", _)) =>
        dropToken()
        val op = expectNumber()
        val args = parseExprs()
        Right(Surface.Expr.Instr(op, args))
      case Some(Token.Keyword("con", _)) =>
        dropToken()
        val cx = expectIdentifier()
        val args = parseExprs()
        Right(Surface.Expr.Con(None, cx, args))
      case Some(Token.Keyword("rec", _)) =>
        dropToken()
        val args = parseExprs()
        Right(Surface.Expr.RecordCon(None, args))
      case Some(Token.Keyword("fin", _)) =>
        dropToken()
        val cx = expectIdentifier()
        Right(Surface.Expr.FiniteCon(None, cx))
      case Some(Token.Keyword("returnIO", _)) =>
        dropToken()
        val expr = parseExpr()
        Right(Surface.Expr.ReturnIO(expr))
      case Some(Token.Keyword("bindIO", _)) =>
        dropToken()
        val x = expectIdentifier()
        expectSymbol("=")
        val value = parseExprBody()
        expectSymbol(";")
        val body = parseExprBody()
        Right(Surface.Expr.BindIO(x, value, body))
      case Some(Token.Keyword("field", ix)) =>
        dropToken()
        val scrut = parseExpr()
        val fix = nextToken() match
          case Some(Token.Number(fix, i)) =>
            if ix < 0 then
              err(s"Field index must be non-negative but got $fix")(using i)
            Right(fix)
          case Some(Token.Identifier(x, _)) => Left(x)
          case Some(t) => err(s"Invalid field index: $t")(using t.getIndex)
          case None    => err(s"Invalid field index, got nothing")(using ix)
        Right(Surface.Expr.Field(scrut, fix))
      case Some(Token.Keyword("match", ix)) =>
        dropToken()
        val scrut = parseExpr()
        val cs = nextToken() match
          case Some(Token.Braces(tokens, _)) =>
            parseNestedUntilEnd(tokens) { parseCases() }
          case Some(t) =>
            err(s"Expected '{' after match but got $t")(using t.getIndex)
          case None =>
            err(s"Expected '{' after match but got nothing")(using ix)
        Right(Surface.Expr.Case(scrut, cs))
      case Some(Token.Keyword("finmatch", ix)) =>
        dropToken()
        val scrut = parseExpr()
        val cs = nextToken() match
          case Some(Token.Braces(tokens, _)) =>
            parseNestedUntilEnd(tokens) {
              parseCases()
            }
          case Some(t) =>
            err(s"Expected '{' after finmatch but got $t")(using t.getIndex)
          case None =>
            err(s"Expected '{' after finmatch but got nothing")(using ix)
        val fcs = cs.map { case (x, ps, body) =>
          if ps.nonEmpty then
            err(s"Finite case cannot have parameters")(using ix)
          (x, body)
        }
        Right(Surface.Expr.FiniteCase(scrut, fcs))
      case Some(Token.Parens(ts, _)) =>
        dropToken()
        parseNestedUntilEnd(ts) { tryParseExprBody() }
      case Some(t) =>
        Left((s"Unexpected token while parsing expression: $t", t.getIndex))
      case None =>
        Left((s"Unexpected end of input while parsing expression", -1))

  private def parseExprs()(using ctx: Ctx): List[Surface.Expr] =
    tryParseExpr() match
      case Left(_)  => Nil
      case Right(e) => e :: parseExprs()

  private def tryParseExprBody()(using
      ctx: Ctx
  ): Either[(String, Int), Surface.Expr] =
    parseExprs() match
      case Nil => Left(("Expected expression but got nothing", -1))
      case xs  => Right(xs.reduceLeft(Surface.Expr.App.apply))

  private def parseExprBody()(using ctx: Ctx): Surface.Expr =
    tryParseExprBody() match
      case Left((msg, i)) => err(msg)(using i)
      case Right(e)       => e

  private def parseIdents()(using ctx: Ctx): List[String] =
    nextToken(true) match
      case Some(Token.Identifier(x, _)) =>
        dropToken()
        x :: parseIdents()
      case _ => Nil

  private def parseCases()(using ctx: Ctx): List[Surface.CaseItem] =
    if maybeKeyword("case") then
      dropToken()
      val con = expectIdentifier()
      val ps = parseIdents()
      expectSymbol("=>")
      val body = parseExprBody()
      (if con == "_" then None else Some(con), ps, body) :: parseCases()
    else Nil

  // parsing utils
  private def expectKeyword(kw: String)(using ctx: Ctx): Unit =
    nextToken() match
      case Some(Token.Keyword(kw2, _)) if kw == kw2 => ()
      case Some(token)                              =>
        err(s"Expected keyword '$kw' but got $token")(using token.getIndex)
      case None => err(s"Expected keyword '$kw' but got nothing")(using -1)

  private def maybeKeyword(kw: String)(using ctx: Ctx): Boolean =
    nextToken(true) match
      case Some(Token.Keyword(kw2, _)) if kw == kw2 => true
      case _                                        => false

  private def expectIdentifier()(using ctx: Ctx): String =
    nextToken() match
      case Some(Token.Identifier(id, _)) => id
      case Some(token)                   =>
        err(s"Expected identifier but got $token")(using token.getIndex)
      case None => err(s"Expected identifier but got nothing")(using -1)

  private def maybeIdentifier()(using ctx: Ctx): Option[String] =
    nextToken(true) match
      case Some(Token.Identifier(x, _)) => Some(x)
      case _                            => None

  private def expectNumber()(using ctx: Ctx): Int =
    nextToken() match
      case Some(Token.Number(n, _)) => n
      case Some(token)              =>
        err(s"Expected number but got $token")(using token.getIndex)
      case None => err(s"Expected number but got nothing")(using -1)

  private def expectSymbol(s: String)(using ctx: Ctx): Unit =
    nextToken() match
      case Some(Token.Symbol(s2, _)) if s == s2 => ()
      case Some(token)                          =>
        err(s"Expected symbol '$s' but got $token")(using token.getIndex)
      case None => err(s"Expected symbol '$s' but got nothing")(using -1)

  private def maybeSymbol(s: String)(using ctx: Ctx): Boolean =
    nextToken(true) match
      case Some(Token.Symbol(s2, _)) if s == s2 => true
      case _                                    => false

  private def nextToken(keepToken: Boolean = false)(using
      ctx: Ctx
  ): Option[Token] =
    val tokens = ctx.tokens
    if tokens.isEmpty then None
    else
      val ret = Some(tokens.head)
      if (!keepToken) tokens.dropInPlace(1)
      ret

  private def dropToken()(using ctx: Ctx): Token =
    val t = ctx.tokens.head
    ctx.tokens.dropInPlace(1)
    t

  private inline def parseNestedUntilEnd[A](ts: Array[Token])(
      inline p: Ctx ?=> A
  ): A =
    val buffer = ts.toBuffer
    given ctx: Ctx = Ctx(buffer)
    val result = p(using ctx)
    if buffer.nonEmpty then {
      println(buffer.mkString(" "))
      err("Unparsed input at end of parsing")(using buffer.head.getIndex)
    }
    result

  // util
  private def err(msg: String)(using index: Int): Nothing =
    throw new ParseException(msg, index)
