package surface

import Lexer.{Symbol, Keyword, Token}
import Lexer.Symbol.*
import Lexer.Keyword.*
import Lexer.Token.*
import Surface.*

import scala.collection.mutable
import scala.reflect.ClassTag
import scala.annotation.tailrec

object Parser:
  class ParseError(msg: String) extends RuntimeException(msg)
  private inline def err(msg: String): Nothing =
    throw new ParseError(msg)

  def parse(text: String): Tm =
    val tokens = Lexer.tokenize(text)
    val state = new State(tokens)
    state.expr()

  // Implementation
  private enum AppState:
    case START
    case PREFIX
    case INFIX
  import AppState.*

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
          case null            => go = false
          case v: A @unchecked => result += v
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
        case null            => err(s"expected $ty but got ${token.pretty}")
        case v: A @unchecked => v
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

    // operators
    // precendence rules taken from Scala for now
    private def prec(op: String): Int =
      op.head match
        case '*' | '/' | '%' => 90
        case '+' | '-'       => 80
        case ':'             => 70
        case '<' | '>'       => 60
        case '=' | '!'       => 50
        case '&'             => 40
        case '^'             => 30
        case '|'             => 20
        case '$' | '_'       => 10
        case c if c.isLetter => 10
        case _               => 100

    // operators can either be left or right associative
    // also taken from Scala
    private def rassoc(op: String): Boolean = op.last == ':'

    // Language parsing
    private def tryAtom(): Tm | Null =
      tryIdent() match
        case null =>
          if trySymbol(L_PAREN) then
            val e = expr()
            symbol(R_PAREN)
            e
          else null
        case x => Tm.Var(x)

    private def atom(): Tm =
      tryAtom() match
        case null => err("expected an expression")
        case a    => a

    private def apps(): Tm =
      val hd = appOrOp()
      val tl = list(tryAppOrOp())
      // Dijkstra shunting yard to handle operators
      val stack: mutable.ArrayStack[Tm] = new mutable.ArrayStack()
      val opstack: mutable.ArrayStack[String] = new mutable.ArrayStack()
      inline def handleOp(op: String): Unit =
        // TODO: operator sections and prefix operators
        println(s"handleOp $op | $stack | $opstack")
        val x = Tm.Var(op)
        val r = stack.pop()
        val l = stack.pop()
        val tm = Tm.App(Tm.App(x, l, ArgInfo.Expl), r, ArgInfo.Expl)
        stack.push(tm)
      hd match
        case op: String        => opstack.push(op)
        case tm: Tm @unchecked => stack.push(tm)
      var i = 0
      val l = tl.length
      while i < l do
        println(s"$i | ${tl(i)} | $stack | $opstack")
        tl(i) match
          case tm: Tm                => stack.push(tm)
          case op: String @unchecked =>
            val p = prec(op)
            val l = !rassoc(op)
            var run = true
            while opstack.nonEmpty && run do
              val top = opstack.last
              val ptop = prec(top)
              if p < ptop || (p == ptop && !l) then
                opstack.pop(); handleOp(top)
              else run = false
            opstack.push(op)
        i += 1
      i = opstack.length - 1
      while i >= 0 do
        handleOp(opstack(i))
        i -= 1
      if stack.length != 1 then err("failed to parse application")
      stack.pop()

    @tailrec
    private def apps2(
        state: AppState = START,
        stack: mutable.ArrayStack[String] = new mutable.ArrayStack(),
        result: mutable.ArrayBuffer[Tm | String] = new mutable.ArrayBuffer()
    ): mutable.ArrayBuffer[Tm | String] =
      state match
        case START =>
          tryOp() match
            case null => ???
            case op   =>
              stack.push(op)
              apps2(PREFIX, stack, result)
        case PREFIX =>
          tryOp() match
            case null =>
              val arg = atom()
              result += stack.foldRight(arg)((op, a) =>
                Tm.App(Tm.Var(op), a, ArgInfo.Expl)
              )
              stack.clear()
              apps2(INFIX, stack, result)
            case op =>
              stack.push(op)
              apps2(PREFIX, stack, result)
        case INFIX => ???

    private def appOrOp(): Tm | String =
      tryAppOrOp() match
        case null => err("expected an expression or an operator")
        case a    => a

    private def tryAppOrOp(): Tm | String | Null =
      tryOp() match
        case null => tryApp()
        case op   => op

    private def tryApp(): Tm | Null =
      tryAtom() match
        case null => null
        case hd   =>
          val tl = list(tryArg())
          tl.foldLeft(hd) { case (f, (a, i)) => Tm.App(f, a, i) }

    private def tryArg(): (Tm, ArgInfo) | Null =
      if trySymbol(L_BRACE) then
        inline def next(i: ArgInfo): (Tm, ArgInfo) | Null =
          val a = expr()
          symbol(R_BRACE)
          (a, i)
        backtrack {
          tryIdent() match
            case null => next(ArgInfo.Impl)
            case x    =>
              if trySymbol(EQUALS) then next(ArgInfo.Named(x))
              else null
        } match
          case null => next(ArgInfo.Impl)
          case res  => res
      else
        tryAtom() match
          case null => null
          case a    => (a, ArgInfo.Expl)

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
      else if trySymbol(BACKSLASH) then
        val xs = list(tryIdent())
        symbol(DOUBLE_ARROW)
        val b = expr()
        xs.foldRight(b)((x, b) => Tm.Lam(x, ArgInfo.Expl, None, b))
      else apps()
