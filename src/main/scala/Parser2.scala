import Common.*

import scala.collection.mutable

object Parser2:
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
    Set("module", "import", "pub", "def", "let", "rec")
  private val symbols1: Set[Char] =
    Set(':', ';', '=', '\\', ',', '(', ')', '{', '}')
  private val symbols2: Map[Char, Set[Char]] =
    Map(':' -> Set('='), '-' -> Set('>'), '=' -> Set('>'))

  private def tokenize(s: String): Array[Token] =
    var i = 0
    val acc = mutable.ArrayBuffer.empty[Char]
    var inComment = false
    var tokens = mutable.ArrayBuffer.empty[Token]
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
        tokens += Token.Symbol(s"$c$next", pos)
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

  private def tokenizeAcc(s: String, pos: PosInfo): Token =
    s.toIntOption match
      case Some(n)                      => Token.Number(n, pos)
      case None if keywords.contains(s) => Token.Keyword(s, pos)
      case None if s.length == 1 && symbols1.contains(s(0)) =>
        Token.Symbol(s, pos)
      case None if s.length == 2 && symbol2Match(s(0), s(1)) =>
        Token.Symbol(s, pos)
      case None => Token.Identifier(s, pos)

  // parsing
  private final case class Ctx(var pos: PosInfo, tokens: mutable.Buffer[Token])

  class ParseError(val pos: PosInfo, val msg: String)
      extends RuntimeException(msg):
    override def toString: String = s"parse error at $pos: $msg"
  private inline def err(msg: String)(using ctx: Ctx): Nothing =
    throw new ParseError(ctx.pos, msg)

  def parse(mod: String, s: String): Surface2.Module =
    val tokens = tokenize(s)
    val buffer = tokens.toBuffer
    given ctx: Ctx = Ctx(PosInfo.start, buffer)
    val result = parseModule(mod)
    if buffer.nonEmpty then err(s"unparsed input at end of file")
    result

  private def parseModule(mod: String)(using ctx: Ctx): Surface2.Module =
    keyword("module")
    val x = identifier()
    if x.expose != mod then
      err(s"module name does not match filename, expected $mod but got $x")
    val deps = mutable.Set.empty[Name]
    val imports = mutable.Map.empty[Name, (Name, Option[Name])]
    val moduleAliases = mutable.Map.empty[Name, Name]
    while tryKeyword("import") do
      val m = identifier()
      val xr = if trySymbol("=>") then Some(identifier()) else None
      moduleAliases += m -> xr.getOrElse(m)
      deps += m
      if trySymbol("(") then
        parseImports().foreach { (x, r) => imports += x -> (m, r) }
    val defs = parseDefs()
    Surface2.Module(
      x,
      deps.toSet,
      imports.toMap,
      moduleAliases.toMap,
      defs
    )

  private def parseImports()(using ctx: Ctx): List[(Name, Option[Name])] =
    if trySymbol(")") then Nil
    else
      val x = identifier()
      val r = if trySymbol("=>") then Some(identifier()) else None
      if trySymbol(",") then (x, r) :: parseImports()
      else
        symbol(")")
        List((x, r))

  private def parseDefs()(using ctx: Ctx): Surface2.Defs =
    Surface2.Defs(list(parseDef))

  private type DefParam = (Icit, Name, Option[Surface2.Ty])

  private def parseDef()(using ctx: Ctx): Option[Surface2.Def] =
    val pub = tryKeyword("pub")
    if tryKeyword("def") then {
      /*
        def x a b ... = e
        def x a b ... : t = e
        def x a b ... := e
        def x a b ... : t := e
        def x (a : t) b ... = e
        def x a b ... : t = e
       */
      ???
    } else None

  private def parseParams()(using ctx: Ctx): List[DefParam] = list(parseParam)

  private def parseParam()(using ctx: Ctx): Option[DefParam] =
    if trySymbol("(") then ???
    else if trySymbol("{") then ???
    else
      tryIdentifier() match
        case None    => None
        case Some(x) => ???

  private def parseAtom()(using ctx: Ctx): Surface2.Tm = ???

  private def parseExpr()(using ctx: Ctx): Surface2.Tm = ???

  // parsers
  private def keyword(kw: String)(using ctx: Ctx): Unit =
    consumeMatch(s"keyword '$kw'"):
      case Token.Keyword(kw2, _) if kw == kw2 => Some(())
      case _                                  => None

  private def symbol(s: String)(using ctx: Ctx): Unit =
    consumeMatch(s"symbol '$s'"):
      case Token.Symbol(s2, _) if s == s2 => Some(())
      case _                              => None

  private def identifier()(using ctx: Ctx): Name =
    consumeMatch(s"identifier"):
      case Token.Identifier(id, _) => Some(Name(id))
      case _                       => None

  private def tryKeyword(kw: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Keyword(kw2, _) if kw == kw2 => true
      case _                                  => false

  private def trySymbol(s: String)(using ctx: Ctx): Boolean =
    tryConsumeMatchBool:
      case Token.Symbol(s2, _) if s == s2 => true
      case _                              => false

  private def tryIdentifier()(using ctx: Ctx): Option[Name] =
    tryConsumeMatch:
      case Token.Identifier(x, _) => Some(Name(x))
      case _                      => None

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

  private inline def tryConsumeMatchBool[A](inline matcher: Token => Boolean)(
      using ctx: Ctx
  ): Boolean =
    tryConsumeMatch(t => if matcher(t) then Some(()) else None).isDefined

  private def list[A](p: () => Option[A]): List[A] =
    p() match
      case None    => Nil
      case Some(x) => x :: list(p)
