import Common.*
import Common.Icit.*
import Common.Bind.*
import Util.time
import Lexer.{Symbol, Keyword, Token}
import Lexer.Symbol.*
import Lexer.Keyword.*
import Lexer.Token.*
import Surface.*

import scala.collection.mutable
import scala.reflect.ClassTag
import scala.annotation.tailrec

// TODO: named holes, datatypes, primitives, lift, quote, splice, if, match, fix positions
object Parser2:
  class ParseError(val pos: PosInfo, msg: String) extends RuntimeException(msg)

  def parseModule(mod: String, text: String): Option[Module] =
    val tokens = time("lexer")(Lexer.tokenize(text))
    if tokens.length == 1 then
      // empty file
      None
    else
      val state = new State(tokens)
      val m = time("parser")(state.module(mod))
      if state.isDone then Some(m)
      else
        throw new ParseError(
          state.pos,
          s"expected EOF but got ${state.peek.pretty}"
        )

  // Implementation
  private type DefParam =
    (ArgInfo, mutable.ArrayBuffer[(PosInfo, Bind)], Tm | Null)
  private final class State(
      var tokens: mutable.ArrayBuffer[Token],
      var ix: Int = 0
  ):
    private inline def err(msg: String): Nothing =
      throw new ParseError(pos, msg)

    private inline def debug: String = ""
    // this.tokens.toSeq.map(_.pretty).mkString("[", " ", "]")

    inline def isDone: Boolean = ix == tokens.length - 1

    inline def peek: Token = tokens(ix)
    inline def pos: PosInfo = peek.pos
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

    private inline def matchNumber(token: Token): String | Null =
      token match
        case NUMBER(x, _) => x
        case _            => null
    private def tryNumber(): String | Null = tryConsume(matchNumber)
    private def number(): String = consume("number")(matchNumber)

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
      if trySymbol(UNDERSCORE) then DontBind
      else DoBind(nameOrOp())

    private def tryBind(): Bind | Null =
      if trySymbol(UNDERSCORE) then DontBind
      else if trySymbol(L_PAREN) then
        val x = op()
        symbol(R_PAREN)
        DoBind(Name.op(x))
      else
        tryName() match
          case null => null
          case x    => DoBind(x)

    private def tryBindPos(): (PosInfo, Bind) | Null =
      val p = pos
      tryBind() match
        case null => null
        case x    => (p, x)

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
      println(s"tryAtom $debug")
      val p = pos
      tryNumber() match
        case null =>
          tryName() match
            case null =>
              if trySymbol(L_PAREN) then
                val p2 = pos
                tryOp() match
                  case null =>
                    val e = expr()
                    symbol(R_PAREN)
                    e
                  case op =>
                    if trySymbol(R_PAREN) then Tm.Var(p2, Name.op(op))
                    else
                      val arg = apps()
                      symbol(R_PAREN)
                      // operator section
                      // (op arg) ~> \x => x op arg
                      // TODO: (arg op) ~> ((op) arg)
                      val x = Name("x") // TODO: name shadowing issues!!!
                      Tm.Lam(
                        p,
                        DoBind(x),
                        ArgInfo.Expl,
                        None,
                        Tm.App(
                          p,
                          Tm.App(
                            p,
                            Tm.Var(p2, Name.op(op)),
                            Tm.Var(p, x),
                            ArgInfo.Expl
                          ),
                          arg,
                          ArgInfo.Expl
                        )
                      )
              else null
            case x => Tm.Var(p, x)
        case n =>
          n.toIntOption match
            case Some(n) => Tm.IntLit(p, n)
            case None    => err(s"invalid number literal: $n")

    private def atom(): Tm =
      println(s"atom $debug")
      tryAtom() match
        case null => err("expected an expression")
        case a    => a

    @tailrec
    private def apps(
        res: mutable.ArrayBuffer[Tm | (PosInfo, String)] =
          mutable.ArrayBuffer.empty
    ): Tm =
      println(s"apps $debug")
      val hd = atom()
      val tl = list(tryArg())
      if trySymbol(BACKSLASH) then tl += ((lam(), ArgInfo.Expl))
      val tm = tl.foldLeft(hd) { case (f, (a, i)) => Tm.App(a.pos, f, a, i) }
      res += tm
      inline def finalize() =
        val tm = shunting(res)
        val p = pos
        if trySymbol(ARROW) then
          val rt = expr()
          Tm.Pi(p, DontBind, Expl, tm, rt)
        else tm
      val p = pos
      tryOp() match
        case null => finalize()
        case op =>
          res += ((p, op))
          if trySymbol(BACKSLASH) then
            res += lam()
            finalize()
          else apps(res)

    private def shunting(sp: mutable.ArrayBuffer[Tm | (PosInfo, String)]): Tm =
      // Dijkstra shunting yard to handle operators
      val stack: mutable.Stack[Tm] = mutable.Stack.empty
      val opstack: mutable.Stack[(PosInfo, String)] = mutable.Stack.empty
      inline def handleOp(op: (PosInfo, String)): Unit =
        // TODO: prefix operators
        val x = Tm.Var(op._1, Name.op(op._2))
        val r = stack.pop()
        val l = stack.pop()
        val tm =
          Tm.App(r.pos, Tm.App(l.pos, x, l, ArgInfo.Expl), r, ArgInfo.Expl)
        stack.push(tm)
      var i = 0
      val l = sp.length
      while i < l do
        sp(i) match
          case tm: Tm => stack.push(tm)
          case opp: (PosInfo, String) @unchecked =>
            val op = opp._2
            val p = prec(op)
            val l = !rassoc(op)
            var run = true
            while opstack.nonEmpty && run do
              val top = opstack.last
              val ptop = prec(top._2)
              if p < ptop || (p == ptop && !l) then
                opstack.pop(); handleOp(top)
              else run = false
            opstack.push(opp)
        i += 1
      i = opstack.length - 1
      while i >= 0 do
        handleOp(opstack(i))
        i -= 1
      if stack.length != 1 then err("failed to parse application")
      stack.pop()

    private def tryArg(): (Tm, ArgInfo) | Null =
      println(s"tryArg $debug")
      if trySymbol(L_BRACE) then
        inline def next(i: ArgInfo): (Tm, ArgInfo) | Null =
          val a = expr()
          symbol(R_BRACE)
          (a, i)
        backtrack {
          tryIdent() match
            case null => next(ArgInfo.Impl)
            case x =>
              if trySymbol(EQUALS) then next(ArgInfo.Named(Name(x)))
              else null
        } match
          case null => next(ArgInfo.Impl)
          case res  => res
      else
        tryAtom() match
          case null => null
          case a    => (a, ArgInfo.Expl)

    private def grouping(): (mutable.ArrayBuffer[(PosInfo, Bind)], Tm | Null) =
      println(s"grouping $debug")
      val p = pos
      val x = (p, bind())
      val xs = list(tryBindPos())
      xs.insert(0, x)
      val ty = if trySymbol(COLON) then expr() else null
      (xs, ty)

    private def tryPiParam(): (Icit, mutable.ArrayBuffer[(PosInfo, Bind)], Tm) |
      Null =
      println(s"tryPiParam $debug")
      if trySymbol(L_PAREN) then
        if trySymbol(R_PAREN) then null
        else
          val p = pos
          val x = (p, bind())
          val xs = list(tryBindPos())
          xs.insert(0, x)
          if trySymbol(COLON) then
            val ty = expr()
            symbol(R_PAREN)
            (Expl, xs, ty)
          else null
      else if trySymbol(L_BRACE) then
        val (xs, prety) = grouping()
        val p = pos
        val ty = prety match
          case null => Tm.Hole(p, None)
          case ty   => ty
        symbol(R_BRACE)
        (Impl, xs, ty)
      else null

    private def lam(): Tm =
      println(s"lam $debug")
      val ps = list(tryParam())
      symbol(DOUBLE_ARROW)
      val b = expr()
      ps.foldRight(b) { case ((a, xs, ty), b) =>
        xs.foldRight(b) { case ((p, x), b) => Tm.Lam(p, x, a, Option(ty), b) }
      }

    private def tryParam(): DefParam | Null =
      println(s"tryParam $debug")
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
        val p = pos
        tryBind() match
          case null => null
          case x    => (ArgInfo.Expl, mutable.ArrayBuffer((p, x)), null)

    private def defn(): (Boolean, Name, Tm | Null, Tm) =
      println(s"defn $debug")
      val x = nameOrOp()
      val ps = list(tryParam())
      val p = pos
      val prety = if trySymbol(COLON) then expr() else null
      val meta =
        if trySymbol(COLON_EQUALS) then false else { symbol(EQUALS); true }
      val prebody = expr()
      val (ty, body) = prety match
        case null =>
          val body = ps.foldRight(prebody) { case ((i, xs, ty), b) =>
            xs.foldRight(b) { case ((p, x), b) =>
              Tm.Lam(p, x, i, Option(ty), b)
            }
          }
          (null, body)
        case rty =>
          val ty = mkPi(p, ps, rty, meta)
          val body = ps.foldRight(prebody) { case ((i, xs, _), b) =>
            xs.foldRight(b) { case ((p, x), b) => Tm.Lam(p, x, i, None, b) }
          }
          (ty, body)
      (meta, x, ty, body)

    private def mkPi(
        p: PosInfo,
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
          case null => Tm.Hole(p, None) // TODO: this position is incorrect
          case ty   => ty
        xs.foldRight(rty) { case ((p, x), rty) =>
          val px = if meta then x else DontBind
          Tm.Pi(p, px, i, pty, rty)
        }
      }

    private def expr(): Tm =
      println(s"expr $debug")
      val p = pos
      if tryKeyword(LET) then
        val rec = tryKeyword(REC)
        val (meta, x, t, v) = defn()
        if rec && meta then err(s"meta level let cannot be recursive")
        symbol(SEMICOLON)
        val b = expr()
        if meta then Tm.Let1(p, x, Option(t), v, b)
        else if rec then Tm.LetRec(p, x, Option(t), v, b)
        else Tm.Let0(p, x, Option(t), v, b)
      else if trySymbol(BACKSLASH) then lam()
      else
        backtrack(tryPiParam()) match
          case null => apps()
          case p =>
            val ps = list(tryPiParam())
            ps.insert(0, p)
            symbol(ARROW)
            val rt = expr()
            ps.foldRight(rt) { case ((i, xs, ty), rt) =>
              xs.foldRight(rt) { case ((p, x), rt) => Tm.Pi(p, x, i, ty, rt) }
            }

    @tailrec
    private def imports(
        res: mutable.ArrayBuffer[(PosInfo, PosInfo, Name, Option[Name])] =
          mutable.ArrayBuffer.empty
    ): mutable.ArrayBuffer[(PosInfo, PosInfo, Name, Option[Name])] =
      if trySymbol(R_PAREN) then res
      else
        val p1 = pos
        val x = nameOrOp()
        var p2 = p1
        val r = if trySymbol(DOUBLE_ARROW) then
          p2 = pos
          Some(nameOrOp())
        else None
        res += ((p1, p2, x, r))
        if trySymbol(COMMA) then imports(res)
        else
          symbol(R_PAREN)
          res

    private def defs(): Defs = Defs(list(tryDef()).toSeq)

    private def tryDef(): Def | Null =
      val p = pos
      if tryKeyword(DEF) then
        val (meta, x, ty, body) = defn()
        if meta then Def.Def1(p, x, Option(ty), body)
        else Def.Def0(p, x, Option(ty), body)
      else null

    def module(mod: String): Module =
      val p = pos
      keyword(MODULE)
      val x = name()
      if x.expose != mod then
        err(
          s"module name does not match file name or path, expected $mod but got $x"
        )
      val deps = mutable.Set.empty[Name]
      val imps = mutable.Map.empty[Name, (PosInfo, PosInfo, Name, Option[Name])]
      val moduleAliases = mutable.Map.empty[Name, Name]
      while tryKeyword(IMPORT) do
        val m = name()
        val xr = if trySymbol(DOUBLE_ARROW) then name() else m
        moduleAliases += m -> xr
        deps += m
        if trySymbol(L_PAREN) then imports().foreach(p => imps += x -> p)
      val ds = defs()
      Module(p, x, deps.toSet, imps.toMap, moduleAliases.toMap, ds)
