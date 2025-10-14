package surface

import Lexer.{Symbol, Keyword, Token}
import Lexer.Symbol.*
import Lexer.Keyword.*
import Lexer.Token.*
import Surface.*

import scala.collection.mutable
import scala.reflect.ClassTag

object Parser:
  class ParseError(msg: String) extends RuntimeException(msg)
  private inline def err(msg: String): Nothing =
    throw new ParseError(msg)

  def parse(text: String): Tm =
    val tokens = Lexer.tokenize(text)
    val state = new State(tokens)
    state.expr()

  // Implementation
  private final class State(
      var tokens: mutable.ArrayBuffer[Token],
      var ix: Int = 0
  ):
    private inline def peek: Token = tokens(ix)
    private inline def skip(): Unit = ix += 1
    private inline def pop(): Token =
      val token = peek
      skip()
      token

    private inline def copy: State = new State(tokens.clone(), ix)
    private inline def restore(state: State): Unit =
      this.tokens = state.tokens
      this.ix = state.ix
    private inline def backtrack[A](action: A | Null): A | Null =
      val c = copy
      action match
        case null => restore(c); null
        case v    => v

    private inline def list[A: ClassTag](
        inline test: A | Null
    ): mutable.ArrayBuffer[A] =
      val result: mutable.ArrayBuffer[A] = new mutable.ArrayBuffer()
      var go = true
      while go do
        test match
          case null => go = false
          case v: A => result += v
      result

    private inline def tryConsume[A](inline test: Token => A | Null): A | Null =
      test(peek) match
        case null => null
        case v    => skip(); v
    private inline def tryConsumeBool(inline test: Token => Boolean): Boolean =
      if test(peek) then { skip(); true }
      else false
    private inline def consume[A](ty: String)(
        inline test: Token => A | Null
    ): A =
      val token = pop()
      test(token) match
        case null => err(s"expected $ty but got ${token.pretty}")
        case v: A => v
    private inline def consumeBool(ty: String)(
        inline test: Token => Boolean
    ): Unit =
      val token = pop()
      if test(token) then () else err(s"expected $ty but got ${token.pretty}")

    private inline def matchIdent(token: Token): String | Null =
      token match
        case IDENT(x) => x
        case _        => null
    private def tryIdent(): String | Null = tryConsume(matchIdent)
    private def ident(): String = consume("identifier")(matchIdent)

    private inline def matchOp(token: Token): String | Null =
      token match
        case OP(x) => x
        case _     => null
    private def tryOp(): String | Null = tryConsume(matchOp)
    private def op(): String = consume("operator")(matchOp)

    private inline def matchSymbol(s: Symbol)(token: Token): Boolean =
      token match
        case SYMBOL(s2) if s2 == s => true
        case _                     => false
    private def trySymbol(s: Symbol): Boolean = tryConsumeBool(matchSymbol(s))
    private def symbol(s: Symbol): Unit = consumeBool(s.pretty)(matchSymbol(s))

    private inline def matchKeyword(s: Keyword)(token: Token): Boolean =
      token match
        case KEYWORD(s2) if s2 == s => true
        case _                      => false
    private def tryKeyword(s: Keyword): Boolean =
      tryConsumeBool(matchKeyword(s))
    private def keyword(s: Keyword): Unit =
      consumeBool(s.pretty)(matchKeyword(s))

    // Language parsing
    def tryAtom(): Tm | Null =
      tryIdent() match
        case x: String => Tm.Var(x)
        case null      =>
          if trySymbol(L_PAREN) then
            val e = expr()
            symbol(R_PAREN)
            e
          else null

    def atom(): Tm =
      tryAtom() match
        case a: Tm => a
        case null  => err("expected an expression")

    def expr(): Tm =
      if tryKeyword(LET) then
        val x = ident()
        val t =
          if trySymbol(COLON) then Some(expr())
          else None
        symbol(EQUALS)
        val v = expr()
        symbol(SEMICOLON)
        val b = expr()
        Tm.Let(x, t, v, b)
      else atom()
