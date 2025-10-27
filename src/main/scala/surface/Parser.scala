package surface

import common.Common.*
import common.Util.time
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

  def parse(mod: String, text: String): Module =
    val tokens = time("lexer")(Lexer.tokenize(text))
    val state = new State(tokens)
    val m = time("parser")(state.module(mod))
    if state.isDone then m
    else err(s"expected EOF but got ${state.peek.pretty}")

  // Implementation
  private type DefParam = (ArgInfo, mutable.ArrayBuffer[Bind], Tm | Null)
  private final class State(
      var tokens: mutable.ArrayBuffer[Token],
      var ix: Int = 0
  ):
    inline def isDone: Boolean = ix == tokens.length - 1

    inline def peek: Token = tokens(ix)
    private inline def pos: PosInfo = peek.pos
    private inline def skip(): Unit = ix += 1
    private inline def pop(): Token =
      val token = peek
      skip()
      token

    private inline def backtrack[A](inline action: A | Null): A | Null =
      val c = new State(tokens.clone(), ix)
      action match
        case null =>
          tokens = c.tokens
          ix = c.ix
          null
        case v => v

    private inline def list[A: ClassTag](
        inline test: A | Null
    ): mutable.ArrayBuffer[A] =
      val result: mutable.ArrayBuffer[A] = mutable.ArrayBuffer.empty
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
        case IDENT(x, _) => x
        case _           => null
    private def tryIdent(): String | Null = tryConsume(matchIdent)
    private def ident(): String = consume("identifier")(matchIdent)

    private inline def matchOp(token: Token): String | Null =
      token match
        case OP(x, _) => x
        case _        => null
    private def tryOp(): String | Null = tryConsume(matchOp)
    private def op(): String = consume("operator")(matchOp)

    private inline def matchSymbol(s: Symbol)(token: Token): Boolean =
      token match
        case SYMBOL(s2, _) if s2 == s => true
        case _                        => false
    private def trySymbol(s: Symbol): Boolean = tryConsumeBool(matchSymbol(s))
    private def symbol(s: Symbol): Unit = consumeBool(s.pretty)(matchSymbol(s))

    private inline def matchKeyword(s: Keyword)(token: Token): Boolean =
      token match
        case KEYWORD(s2, _) if s2 == s => true
        case _                         => false
    private def tryKeyword(s: Keyword): Boolean =
      tryConsumeBool(matchKeyword(s))
    private def keyword(s: Keyword): Unit =
      consumeBool(s.pretty)(matchKeyword(s))

    // names and binds
    private def tryName(): Name | Null =
      tryIdent() match
        case null => null
        case x    => Name(x)
    private def name(): Name = Name(ident())

    private def nameOrOp(): Name =
      if trySymbol(L_PAREN) then
        val x = op()
        symbol(R_PAREN)
        Name.op(x)
      else name()

    private def bind(): Bind =
      if trySymbol(UNDERSCORE) then Bind.Dont
      else Bind.Do(nameOrOp())

    private def tryBind(): Bind | Null =
      if trySymbol(UNDERSCORE) then Bind.Dont
      else if trySymbol(L_PAREN) then
        val x = op()
        symbol(R_PAREN)
        Bind.Do(Name.op(x))
      else
        tryName() match
          case null => null
          case x    => Bind.Do(x)

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
      tryName() match
        case null =>
          if trySymbol(L_PAREN) then
            tryOp() match
              case null =>
                val e = expr()
                symbol(R_PAREN)
                e
              case op =>
                if trySymbol(R_PAREN) then Tm.Var(Name.op(op))
                else
                  val arg = apps() // TODO: support trailing lambda here?
                  symbol(R_PAREN)
                  // operator section
                  // (op arg) ~> \x => x op arg
                  // TODO: (arg op) ~> ((op) arg)
                  val x = Name("x") // TODO: name shadowing issues!!!
                  Tm.Lam(
                    Bind.Do(x),
                    ArgInfo.Expl,
                    None,
                    Tm.App(
                      Tm.App(Tm.Var(Name.op(op)), Tm.Var(x), ArgInfo.Expl),
                      arg,
                      ArgInfo.Expl
                    )
                  )
          else null
        case x => Tm.Var(x)

    private def atom(): Tm =
      tryAtom() match
        case null => err("expected an expression")
        case a    => a

    @tailrec
    private def apps(
        res: mutable.ArrayBuffer[Tm | String] = mutable.ArrayBuffer.empty
    ): Tm =
      val hd = atom()
      val tl = list(tryArg())
      if trySymbol(BACKSLASH) then tl += ((lam(), ArgInfo.Expl))
      val tm = tl.foldLeft(hd) { case (f, (a, i)) => Tm.App(f, a, i) }
      res += tm
      inline def finalize() =
        val tm = shunting(res)
        if trySymbol(ARROW) then
          val rt = expr()
          Tm.Pi(Bind.Dont, Icit.Expl, tm, rt)
        else tm
      tryOp() match
        case null => finalize()
        case op   =>
          res += op
          if trySymbol(BACKSLASH) then
            res += lam()
            finalize()
          else apps(res)

    private def shunting(sp: mutable.ArrayBuffer[Tm | String]): Tm =
      // Dijkstra shunting yard to handle operators
      val stack: mutable.Stack[Tm] = mutable.Stack.empty
      val opstack: mutable.Stack[String] = mutable.Stack.empty
      inline def handleOp(op: String): Unit =
        // TODO: prefix operators
        val x = Tm.Var(Name.op(op))
        val r = stack.pop()
        val l = stack.pop()
        val tm = Tm.App(Tm.App(x, l, ArgInfo.Expl), r, ArgInfo.Expl)
        stack.push(tm)
      var i = 0
      val l = sp.length
      while i < l do
        sp(i) match
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
              if trySymbol(EQUALS) then next(ArgInfo.Named(Name(x)))
              else null
        } match
          case null => next(ArgInfo.Impl)
          case res  => res
      else
        tryAtom() match
          case null => null
          case a    => (a, ArgInfo.Expl)

    private def grouping(): (mutable.ArrayBuffer[Bind], Tm | Null) =
      val x = bind()
      val xs = list(tryBind())
      xs.insert(0, x)
      val ty = if trySymbol(COLON) then expr() else null
      (xs, ty)

    private def tryPiParam(): (Icit, mutable.ArrayBuffer[Bind], Tm) | Null =
      if trySymbol(L_PAREN) then
        if trySymbol(R_PAREN) then null
        else
          val x = bind()
          val xs = list(tryBind())
          xs.insert(0, x)
          if trySymbol(COLON) then
            val ty = expr()
            symbol(R_PAREN)
            (Icit.Expl, xs, ty)
          else null
      else if trySymbol(L_BRACE) then
        val (xs, prety) = grouping()
        val ty = prety match
          case null => Tm.Hole
          case ty   => ty
        symbol(R_BRACE)
        (Icit.Impl, xs, ty)
      else null

    private def lam(): Tm =
      val ps = list(tryParam())
      symbol(DOUBLE_ARROW)
      val b = expr()
      ps.foldRight(b) { case ((a, xs, ty), b) =>
        xs.foldRight(b)((x, b) => Tm.Lam(x, a, Option(ty), b))
      }

    private def tryParam(): DefParam | Null =
      if trySymbol(L_PAREN) then
        val (xs, ty) = grouping()
        symbol(R_PAREN)
        (ArgInfo.Expl, xs, ty)
      else if trySymbol(L_BRACE) then
        val (xs, ty) = grouping()
        val named = if trySymbol(EQUALS) then nameOrOp() else null
        symbol(R_BRACE)
        val arginfo = named match
          case null => ArgInfo.Impl
          case x    => ArgInfo.Named(x)
        (arginfo, xs, ty)
      else
        tryBind() match
          case null => null
          case x    => (ArgInfo.Expl, mutable.ArrayBuffer(x), null)

    private def defn(): (Boolean, Name, Tm | Null, Tm) =
      val x = nameOrOp()
      val ps = list(tryParam())
      val prety = if trySymbol(COLON) then expr() else null
      val meta =
        if trySymbol(COLON_EQUALS) then false else { symbol(EQUALS); true }
      val prebody = expr()
      val (ty, body) = prety match
        case null =>
          val body = ps.foldRight(prebody) { case ((i, xs, ty), b) =>
            xs.foldRight(b)((x, b) => Tm.Lam(x, i, Option(ty), b))
          }
          (null, body)
        case rty =>
          val ty = mkPi(ps, rty, meta)
          val body = ps.foldRight(prebody) { case ((i, xs, _), b) =>
            xs.foldRight(b)((x, b) => Tm.Lam(x, i, None, b))
          }
          (ty, body)
      (meta, x, ty, body)

    private def mkPi(
        ps: mutable.ArrayBuffer[DefParam],
        rty: Tm,
        meta: Boolean
    ): Tm =
      ps.foldRight(rty) { case ((ai, xs, opty), rty) =>
        val i = ai match
          case ArgInfo.Named(_) =>
            err(
              "named parameter not allowed for lets or top-level definitions"
            )
          case ArgInfo.Icit(i) => i
        val pty = opty match
          case null => Tm.Hole
          case ty   => ty
        xs.foldRight(rty) { (x, rty) =>
          val px = if meta then x else Bind.Dont
          Tm.Pi(px, i, pty, rty)
        }
      }

    private def expr(): Tm =
      if tryKeyword(LET) then
        val (meta, x, t, v) = defn()
        symbol(SEMICOLON)
        val b = expr()
        if meta then Tm.Let1(x, Option(t), v, b)
        else Tm.Let0(x, Option(t), v, b)
      else if trySymbol(BACKSLASH) then lam()
      else
        backtrack(tryPiParam()) match
          case null => apps()
          case p    =>
            val ps = list(tryPiParam())
            ps.insert(0, p)
            symbol(ARROW)
            val rt = expr()
            ps.foldRight(rt) { case ((i, xs, ty), rt) =>
              xs.foldRight(rt)((x, rt) => Tm.Pi(x, i, ty, rt))
            }

    @tailrec
    private def imports(
        res: mutable.ArrayBuffer[(Name, Option[Name])] =
          mutable.ArrayBuffer.empty
    ): mutable.ArrayBuffer[(Name, Option[Name])] =
      if trySymbol(R_PAREN) then res
      else
        val x = nameOrOp()
        val r = if trySymbol(DOUBLE_ARROW) then Some(nameOrOp()) else None
        res += ((x, r))
        if trySymbol(COMMA) then imports(res)
        else
          symbol(R_PAREN)
          res

    private def defs(): Defs = Defs(list(tryDef()).toSeq)

    private def tryDef(): Def | Null =
      if tryKeyword(LET) then
        val (meta, x, ty, body) = defn()
        if meta then Def.D1(x, Option(ty), body)
        else Def.D0(x, Option(ty), body)
      else null

    def module(mod: String): Module =
      keyword(MODULE)
      val x = name()
      if x.expose != mod then
        err(
          s"module name does not match file name or path, expected $mod but got $x"
        )
      val deps = mutable.Set.empty[Name]
      val imps = mutable.Map.empty[Name, (Name, Option[Name])]
      val moduleAliases = mutable.Map.empty[Name, Name]
      while tryKeyword(IMPORT) do
        val m = name()
        val xr = if trySymbol(DOUBLE_ARROW) then name() else m
        moduleAliases += m -> xr
        deps += m
        if trySymbol(L_PAREN) then imports().foreach(p => imps += x -> p)
      val ds = defs()
      Module(x, deps.toSet, imps.toMap, moduleAliases.toMap, ds)

// TODO: positions, block comments, allow empty file, accept shebang, prefix operators
