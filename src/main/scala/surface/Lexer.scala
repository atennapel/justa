package surface

import scala.collection.mutable
import scala.annotation.tailrec

object Lexer:
  class LexerError(msg: String) extends RuntimeException(msg)
  private inline def err(msg: String): Nothing =
    throw new LexerError(msg)

  // Always returns a non-empty array, ending in with EOF.
  def tokenize(text: String): mutable.ArrayBuffer[Token] =
    val state = new State(text)
    state.tokenize()
    state.tokens

  enum Symbol:
    case L_PAREN
    case R_PAREN
    case COLON
    case SEMICOLON
    case EQUALS
    case COLON_EQUALS

    def pretty: String =
      this match
        case L_PAREN      => "("
        case R_PAREN      => ")"
        case COLON        => ":"
        case SEMICOLON    => ";"
        case EQUALS       => "="
        case COLON_EQUALS => ":="

  object Symbol:
    def parseImmediate(symbol: String): Symbol | Null =
      symbol match
        case "(" => L_PAREN
        case ")" => R_PAREN
        case _   => null
    def parse(symbol: String): Symbol | Null =
      symbol match
        case "("  => L_PAREN
        case ")"  => R_PAREN
        case ":"  => COLON
        case ";"  => SEMICOLON
        case "="  => EQUALS
        case ":=" => COLON_EQUALS
        case _    => null

  enum Keyword:
    case LET

    def pretty: String =
      this match
        case LET => "let"

  object Keyword:
    def parse(keyword: String): Keyword | Null =
      keyword match
        case "let" => LET
        case _     => null

  enum Token:
    case EOF
    case KEYWORD(keyword: Keyword)
    case SYMBOL(symbol: Symbol)
    case IDENT(name: String)
    case OP(name: String)

    def pretty: String =
      this match
        case EOF         => "eof"
        case KEYWORD(kw) => kw.pretty
        case SYMBOL(s)   => s.pretty
        case IDENT(x)    => x
        case OP(op)      => op
  import Token.*

  object Token:
    val identHead = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    val identTail = s"${identHead}0123456789_"
    val opHead = "`~!@#$%^&*-+=\\|:;,<.>?/"
    val opTail = opHead

  private enum LexState:
    case Start
    case Ident
    case Op

  private final class State(
      text: String,
      var ix: Int = 0,
      var state: LexState = LexState.Start,
      val tokens: mutable.ArrayBuffer[Token] = new mutable.ArrayBuffer(),
      acc: mutable.StringBuilder = new mutable.StringBuilder()
  ):
    private inline def take: Char | Null =
      if ix >= text.length then null
      else text(ix)

    private inline def skip(): Unit = ix += 1

    private inline def keep(c: Char): Unit = acc += c

    private inline def use(c: Char): Unit =
      keep(c)
      skip()

    private inline def add(token: Token): Unit =
      tokens += token

    private inline def to(newState: LexState): Unit =
      state = newState

    @tailrec
    def tokenize(): Unit =
      state match
        case LexState.Start =>
          take match
            case null    => add(EOF)
            case c: Char =>
              Symbol.parseImmediate(c.toString) match
                case sym: Symbol => add(SYMBOL(sym)); skip(); tokenize()
                case null        =>
                  c match
                    case c: Char if Token.identHead.contains(c) =>
                      use(c)
                      to(LexState.Ident)
                      tokenize()
                    case c: Char if Token.opHead.contains(c) =>
                      use(c)
                      to(LexState.Op)
                      tokenize()
                    case c: Char if c.isWhitespace => skip(); tokenize()
                    case c => err(s"unexpected character: $c")
        case LexState.Ident =>
          take match
            case c: Char if Token.identTail.contains(c) => use(c); tokenize()
            case _                                      =>
              if acc.nonEmpty then
                val id = acc.result()
                acc.clear()
                Keyword.parse(id) match
                  case kw: Keyword => add(KEYWORD(kw))
                  case null        => add(IDENT(id))
              to(LexState.Start)
              tokenize()
        case LexState.Op =>
          take match
            case c: Char if Token.opTail.contains(c) => use(c); tokenize()
            case _                                   =>
              if acc.nonEmpty then
                val id = acc.result()
                acc.clear()
                Symbol.parse(id) match
                  case sym: Symbol => add(SYMBOL(sym))
                  case null        => add(OP(id))
              to(LexState.Start)
              tokenize()
