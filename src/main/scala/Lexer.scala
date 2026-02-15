import Common.PosInfo

import scala.collection.mutable
import scala.annotation.tailrec

object Lexer:
  class LexerError(val pos: PosInfo, msg: String) extends RuntimeException(msg)
  private inline def err(pos: PosInfo, msg: String): Nothing =
    throw new LexerError(pos, msg)

  // Always returns a non-empty array, ending in with EOF.
  def tokenize(text: String): mutable.ArrayBuffer[Token] =
    val state = new State(text)
    state.tokenize()
    state.tokens

  enum Symbol derives CanEqual:
    case L_PAREN
    case R_PAREN
    case L_BRACE
    case R_BRACE
    case L_BRACKET
    case R_BRACKET
    case COLON
    case SEMICOLON
    case EQUALS
    case COLON_EQUALS
    case BACKSLASH
    case ARROW
    case DOUBLE_ARROW
    case UNDERSCORE
    case COMMA
    case PIPE
    case CARET
    case GRAVE
    case DOLLAR
    case PERIOD

    def pretty: String =
      this match
        case L_PAREN      => "("
        case R_PAREN      => ")"
        case L_BRACE      => "{"
        case R_BRACE      => "}"
        case L_BRACKET    => "["
        case R_BRACKET    => "]"
        case COLON        => ":"
        case SEMICOLON    => ";"
        case EQUALS       => "="
        case COLON_EQUALS => ":="
        case BACKSLASH    => "\\"
        case ARROW        => "->"
        case DOUBLE_ARROW => "=>"
        case UNDERSCORE   => "_"
        case COMMA        => ","
        case PIPE         => "|"
        case CARET        => "^"
        case GRAVE        => "`"
        case DOLLAR       => "$"
        case PERIOD       => "."

  object Symbol:
    def parseImmediate(symbol: String): Symbol | Null =
      symbol match
        case "(" => L_PAREN
        case ")" => R_PAREN
        case "{" => L_BRACE
        case "}" => R_BRACE
        case "[" => L_BRACKET
        case "]" => R_BRACKET
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
        case "|"  => PIPE
        case "^"  => CARET
        case "`"  => GRAVE
        case "$"  => DOLLAR
        case "."  => PERIOD
        case _    => null

  enum Keyword derives CanEqual:
    case MODULE
    case IMPORT
    case DEF
    case DECLARE
    case DATA
    case PUB
    case PRIV
    case LET
    case REC
    case IF
    case THEN
    case ELSE
    case MATCH
    case DEFAULT
    case AUTO

    case META
    case TYPE
    case CV
    case VAL
    case COMP
    case BOOL
    case TRUE
    case FALSE
    case INT
    case LT
    case ADD
    case SUB
    case MUL
    case IO
    case RETURNIO
    case BINDIO
    case ID
    case REFL
    case ELIMID
    case FIXIX
    case LABEL
    case CLASS
    case UNSAFE
    case UNSAFEIO
    case ARRAY
    case VOID
    case UNSAFERUNIO
    case VARIABLE

    def pretty: String =
      this match
        case MODULE      => "module"
        case IMPORT      => "import"
        case DEF         => "def"
        case DECLARE     => "declare"
        case DATA        => "data"
        case PUB         => "pub"
        case PRIV        => "priv"
        case LET         => "let"
        case REC         => "rec"
        case IF          => "if"
        case THEN        => "then"
        case ELSE        => "else"
        case MATCH       => "match"
        case DEFAULT     => "default"
        case AUTO        => "auto"
        case META        => "meta"
        case TYPE        => "type"
        case CV          => "cv"
        case VAL         => "val"
        case COMP        => "comp"
        case BOOL        => "Bool"
        case TRUE        => "True"
        case FALSE       => "False"
        case INT         => "Int"
        case LT          => "lt"
        case ADD         => "add"
        case SUB         => "sub"
        case MUL         => "mul"
        case IO          => "IO"
        case RETURNIO    => "returnIO"
        case BINDIO      => "bindIO"
        case ID          => "Id"
        case REFL        => "refl"
        case ELIMID      => "elimId"
        case FIXIX       => "fixIx"
        case LABEL       => "label"
        case CLASS       => "class"
        case UNSAFE      => "unsafe"
        case UNSAFEIO    => "unsafeIO"
        case ARRAY       => "Array"
        case VOID        => "Void"
        case UNSAFERUNIO => "unsafeRunIO"
        case VARIABLE    => "variable"

  object Keyword:
    val Primitives: Array[Keyword] = Array(
      META,
      TYPE,
      CV,
      VAL,
      COMP,
      BOOL,
      TRUE,
      FALSE,
      INT,
      LT,
      ADD,
      SUB,
      MUL,
      IO,
      RETURNIO,
      BINDIO,
      ID,
      REFL,
      ELIMID,
      FIXIX,
      LABEL,
      CLASS,
      ARRAY,
      VOID,
      UNSAFERUNIO
    )

    def parse(keyword: String): Keyword | Null =
      keyword match
        case "module"      => MODULE
        case "import"      => IMPORT
        case "def"         => DEF
        case "declare"     => DECLARE
        case "data"        => DATA
        case "pub"         => PUB
        case "priv"        => PRIV
        case "let"         => LET
        case "rec"         => REC
        case "if"          => IF
        case "then"        => THEN
        case "else"        => ELSE
        case "match"       => MATCH
        case "default"     => DEFAULT
        case "auto"        => AUTO
        case "meta"        => META
        case "type"        => TYPE
        case "cv"          => CV
        case "val"         => VAL
        case "comp"        => COMP
        case "Bool"        => BOOL
        case "True"        => TRUE
        case "False"       => FALSE
        case "Int"         => INT
        case "lt"          => LT
        case "add"         => ADD
        case "sub"         => SUB
        case "mul"         => MUL
        case "IO"          => IO
        case "returnIO"    => RETURNIO
        case "bindIO"      => BINDIO
        case "Id"          => ID
        case "refl"        => REFL
        case "elimId"      => ELIMID
        case "fixIx"       => FIXIX
        case "label"       => LABEL
        case "class"       => CLASS
        case "unsafe"      => UNSAFE
        case "unsafeIO"    => UNSAFEIO
        case "Array"       => ARRAY
        case "Void"        => VOID
        case "unsafeRunIO" => UNSAFERUNIO
        case "variable"    => VARIABLE
        case _             => null

  enum Token:
    case EOF(_pos: PosInfo)
    case KEYWORD(keyword: Keyword, _pos: PosInfo)
    case SYMBOL(symbol: Symbol, _pos: PosInfo)
    case NUMBER(number: String, _pos: PosInfo)
    case IDENT(name: String, _pos: PosInfo)
    case OP(name: String, _pos: PosInfo)
    case STRING(value: String, _pos: PosInfo)

    def pretty: String =
      this match
        case EOF(_)         => "eof"
        case KEYWORD(kw, _) => kw.pretty
        case SYMBOL(s, _)   => s.pretty
        case NUMBER(n, _)   => n
        case IDENT(x, _)    => x
        case OP(op, _)      => op
        case STRING(v, _)   => s"\"$v\""

    def pos: PosInfo = this match
      case EOF(p)        => p
      case KEYWORD(_, p) => p
      case SYMBOL(_, p)  => p
      case NUMBER(_, p)  => p
      case IDENT(_, p)   => p
      case OP(_, p)      => p
      case STRING(_, p)  => p
  import Token.*

  object Token:
    val identHead =
      "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"
    val identTail = s"${identHead}0123456789"
    val opHead = "`~!@#$%^&*-+=\\|:;,<.>?/"
    val opTail = opHead

  private enum LexState derives CanEqual:
    case Start
    case Comment
    case BlockComment1
    case BlockComment2
    case Ident
    case Number
    case Op
    case String

  private final class State(
      text: String,
      var ix: Int = 0,
      var line: Int = 1,
      var col: Int = 1,
      var state: LexState = LexState.Start,
      val tokens: mutable.ArrayBuffer[Token] = mutable.ArrayBuffer.empty,
      acc: mutable.StringBuilder = new mutable.StringBuilder()
  ):
    private inline def take: Char =
      if ix >= text.length then '\u0000'
      else text(ix)

    private inline def takeSkip: Char =
      if ix + 1 >= text.length then '\u0000'
      else text(ix + 1)

    private inline def skip(isNewline: Boolean = false): Unit =
      ix += 1
      if isNewline then
        col = 1
        line += 1
      else col += 1

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
            case '\u0000' => add(EOF(pos))
            case '\n'     => skip(); to(LexState.Start); tokenize()
            case _        => skip(); tokenize()
        case LexState.BlockComment1 =>
          take match
            case '\u0000' => add(EOF(pos))
            case '-'      => skip(); to(LexState.BlockComment2); tokenize()
            case _        => skip(); tokenize()
        case LexState.BlockComment2 =>
          take match
            case '\u0000' => add(EOF(pos))
            case '}'      => skip(); to(LexState.Start); tokenize()
            case '-'      => skip(); tokenize()
            case _        => skip(); to(LexState.BlockComment1); tokenize()
        case LexState.Start =>
          take match
            case '\u0000' =>
              add(EOF(pos))
            case '#' if tokens.isEmpty && takeSkip == '!' =>
              skip(); skip(); to(LexState.Comment); tokenize()
            case '"' =>
              skip(); to(LexState.String); tokenize()
            case c =>
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
                    case c: Char if c.isDigit =>
                      use(c)
                      to(LexState.Number)
                      tokenize()
                    case c: Char if c.isWhitespace =>
                      skip(c == '\n')
                      tokenize()
                    case c => err(pos, s"unexpected character: $c")
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
            case _ =>
              if acc.nonEmpty then
                val id = acc.result()
                acc.clear()
                if id == "_" then add(SYMBOL(Symbol.UNDERSCORE, pos))
                else
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
        case LexState.Number =>
          take match
            case c: Char if c.isDigit =>
              use(c)
              tokenize()
            case _ =>
              if acc.nonEmpty then
                val n = acc.result()
                acc.clear()
                add(NUMBER(n, pos))
              to(LexState.Start)
              tokenize()
        case LexState.String =>
          take match
            case '"' =>
              skip()
              val v = acc.result()
              // TODO: handle escapes
              // TODO: correct position
              add(STRING(v, pos))
              acc.clear()
              to(LexState.Start)
              tokenize()
            case c =>
              use(c)
              tokenize()
