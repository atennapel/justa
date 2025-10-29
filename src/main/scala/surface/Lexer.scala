package surface

import common.Common.PosInfo

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
    case L_BRACE
    case R_BRACE
    case COLON
    case SEMICOLON
    case EQUALS
    case COLON_EQUALS
    case BACKSLASH
    case ARROW
    case DOUBLE_ARROW
    case UNDERSCORE
    case COMMA

    def pretty: String =
      this match
        case L_PAREN      => "("
        case R_PAREN      => ")"
        case L_BRACE      => "{"
        case R_BRACE      => "}"
        case COLON        => ":"
        case SEMICOLON    => ";"
        case EQUALS       => "="
        case COLON_EQUALS => ":="
        case BACKSLASH    => "\\"
        case ARROW        => "->"
        case DOUBLE_ARROW => "=>"
        case UNDERSCORE   => "_"
        case COMMA        => ","

  object Symbol:
    def parseImmediate(symbol: String): Symbol | Null =
      symbol match
        case "(" => L_PAREN
        case ")" => R_PAREN
        case "{" => L_BRACE
        case "}" => R_BRACE
        case _   => null
    def parse(symbol: String): Symbol | Null =
      symbol match
        case "("  => L_PAREN
        case ")"  => R_PAREN
        case "{"  => L_BRACE
        case "}"  => R_BRACE
        case ":"  => COLON
        case ";"  => SEMICOLON
        case "="  => EQUALS
        case ":=" => COLON_EQUALS
        case "\\" => BACKSLASH
        case "->" => ARROW
        case "=>" => DOUBLE_ARROW
        case "_"  => UNDERSCORE
        case ","  => COMMA
        case _    => null

  enum Keyword:
    case MODULE
    case IMPORT
    case LET

    def pretty: String =
      this match
        case MODULE => "module"
        case IMPORT => "import"
        case LET    => "let"

  object Keyword:
    def parse(keyword: String): Keyword | Null =
      keyword match
        case "module" => MODULE
        case "import" => IMPORT
        case "let"    => LET
        case _        => null

  enum Token:
    case EOF(_pos: PosInfo)
    case KEYWORD(keyword: Keyword, _pos: PosInfo)
    case SYMBOL(symbol: Symbol, _pos: PosInfo)
    case IDENT(name: String, _pos: PosInfo)
    case OP(name: String, _pos: PosInfo)

    def pretty: String =
      this match
        case EOF(_)         => "eof"
        case KEYWORD(kw, _) => kw.pretty
        case SYMBOL(s, _)   => s.pretty
        case IDENT(x, _)    => x
        case OP(op, _)      => op

    def pos: PosInfo = this match
      case Token.EOF(p)        => p
      case Token.KEYWORD(_, p) => p
      case Token.SYMBOL(_, p)  => p
      case Token.IDENT(_, p)   => p
      case Token.OP(_, p)      => p
  import Token.*

  object Token:
    private[surface] val identHead =
      "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    private[surface] val identTail = s"${identHead}0123456789_"
    private[surface] val opHead = "`~!@#$%^&*-+=\\|:;,<.>?/"
    private[surface] val opTail = opHead

  private enum LexState:
    case Start
    case Comment
    case BlockComment1
    case BlockComment2
    case Ident
    case Op

  private final class State(
      text: String,
      var ix: Int = 0,
      var line: Int = 1,
      var col: Int = 1,
      var state: LexState = LexState.Start,
      val tokens: mutable.ArrayBuffer[Token] = mutable.ArrayBuffer.empty,
      acc: mutable.StringBuilder = new mutable.StringBuilder()
  ):
    private inline def take: Char | Null =
      if ix >= text.length then null
      else text(ix)

    private inline def skip(isNewline: Boolean = false): Unit = {
      ix += 1
      if isNewline then
        col = 1
        line += 1
      else col += 1
    }

    private inline def keep(c: Char): Unit = acc += c

    private inline def use(c: Char): Unit =
      keep(c)
      skip()

    private inline def add(token: Token): Unit =
      tokens += token

    private inline def to(newState: LexState): Unit =
      state = newState

    private inline def pos: PosInfo = PosInfo(line, col)

    @tailrec
    def tokenize(): Unit =
      state match
        case LexState.Comment =>
          take match
            case null => add(EOF(pos))
            case '\n' => skip(); to(LexState.Start); tokenize()
            case _    => skip(); tokenize()
        case LexState.BlockComment1 =>
          take match
            case null => add(EOF(pos))
            case '-'  => skip(); to(LexState.BlockComment2); tokenize()
            case _    => skip(); tokenize()
        case LexState.BlockComment2 =>
          take match
            case null => add(EOF(pos))
            case '}'  => skip(); to(LexState.Start); tokenize()
            case '-'  => skip(); tokenize()
            case _    => skip(); to(LexState.BlockComment1); tokenize()
        case LexState.Start =>
          take match
            case null => add(EOF(pos))
            case c    =>
              Symbol.parseImmediate(c.toString) match
                case null =>
                  c match
                    case c: Char if Token.identHead.contains(c) =>
                      use(c)
                      to(LexState.Ident)
                      tokenize()
                    case c: Char if Token.opHead.contains(c) =>
                      use(c)
                      to(LexState.Op)
                      tokenize()
                    case c: Char if c.isWhitespace =>
                      skip(c == '\n')
                      tokenize()
                    case c => err(s"unexpected character: $c")
                case sym @ Symbol.L_BRACE =>
                  val p = pos
                  skip()
                  take match
                    case '-' => skip(); to(LexState.BlockComment1)
                    case _   => add(SYMBOL(sym, p))
                  tokenize()
                case sym => add(SYMBOL(sym, pos)); skip(); tokenize()
        case LexState.Ident =>
          take match
            case c: Char if Token.identTail.contains(c) => use(c); tokenize()
            case _                                      =>
              if acc.nonEmpty then
                val id = acc.result()
                acc.clear()
                Keyword.parse(id) match
                  case null => add(IDENT(id, pos))
                  case kw   => add(KEYWORD(kw, pos))
              to(LexState.Start)
              tokenize()
        case LexState.Op =>
          take match
            case c: Char if Token.opTail.contains(c) =>
              use(c)
              if acc.result() == "--" then
                acc.clear()
                to(LexState.Comment)
              tokenize()
            case _ =>
              if acc.nonEmpty then
                val id = acc.result()
                acc.clear()
                Symbol.parse(id) match
                  case null => add(OP(id, pos))
                  case sym  => add(SYMBOL(sym, pos))
              to(LexState.Start)
              tokenize()
