import Common.*
import Common.Icit.*
import Common.Bind.*
import Lexer.{Symbol, Keyword, Token}
import Lexer.Symbol.*
import Lexer.Keyword.*
import Lexer.Token.*
import Surface.*

import scala.collection.mutable
import scala.reflect.ClassTag
import scala.annotation.tailrec

// TODO: fix positions
object Parser:
  class ParseError(val pos: PosInfo, msg: String) extends RuntimeException(msg)

  def parseModule(mod: String, text: String): Option[Module] =
    val tokens = Lexer.tokenize(text)
    if tokens.length == 1 then
      // empty file
      None
    else
      val state = new State(tokens)
      val m = state.module(mod)
      if state.isDone then Some(m)
      else
        throw new ParseError(
          state.pos,
          s"expected EOF but got ${state.peek.pretty}"
        )

  // Implementation
  private type DefParam =
    (ArgInfo[PiIcit], mutable.ArrayBuffer[(PosInfo, Bind)], Tm | Null)
  private final class State(
      var tokens: mutable.ArrayBuffer[Token],
      var ix: Int = 0
  ):
    private inline def err(msg: String): Nothing =
      throw new ParseError(pos, msg)

    inline def isDone: Boolean = ix == tokens.length - 1

    inline def peek: Token = tokens(ix)
    inline def pos: PosInfo = peek.pos
    private inline def skip(): Unit = ix += 1
    private inline def pop(): Token =
      val token = peek
      skip()
      token

    private inline def backtrack[A](inline action: A | Null): A | Null =
      given CanEqual[Null, A | Null] = CanEqual.derived
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
      given CanEqual[Null, A | Null] = CanEqual.derived
      val result: mutable.ArrayBuffer[A] = mutable.ArrayBuffer.empty
      var go = true
      while go do
        test match
          case null            => go = false
          case v: A @unchecked => result += v
      result

    private inline def tryConsume[A](
        inline test: Token => A | Null
    ): A | Null =
      given CanEqual[Null, A | Null] = CanEqual.derived
      test(peek) match
        case null => null
        case v    => skip(); v
    private inline def tryConsumeBool(inline test: Token => Boolean): Boolean =
      if test(peek) then { skip(); true }
      else false
    private inline def consume[A](ty: String)(
        inline test: Token => A | Null
    ): A =
      given CanEqual[Null, A | Null] = CanEqual.derived
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
        case null                   => null
        case x if x.startsWith("_") => err(s"invalid name: $x")
        case x                      => Name(x)
    private def name(): Name = Name(ident())

    private def nameOrOp(): Name =
      if trySymbol(L_PAREN) then
        val x = op()
        symbol(R_PAREN)
        Name.op(x)
      else name()

    private def tryNameOrOp(): Name | Null =
      if trySymbol(L_PAREN) then
        val x = op()
        symbol(R_PAREN)
        Name.op(x)
      else tryName()

    private def bind(): Bind =
      if trySymbol(UNDERSCORE) then DontBind
      else DoBind(nameOrOp())

    private def tryBind(): Bind | Null =
      backtrack {
        if trySymbol(UNDERSCORE) then DontBind
        else if trySymbol(L_PAREN) then
          tryOp() match
            case null => null
            case x =>
              if trySymbol(R_PAREN) then DoBind(Name.op(x))
              else null
        else
          tryName() match
            case null => null
            case x    => DoBind(x)
      }

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
    private def tryAtomInner(): Tm | Null =
      val p = pos
      tryPrimitive() match
        case null =>
          tryNumber() match
            case null =>
              tryIdent() match
                case null =>
                  if trySymbol(UNDERSCORE) then Tm.Hole(p, None)
                  else if trySymbol(CARET) then Tm.Lift(p, atom())
                  else if trySymbol(GRAVE) then Tm.Quote(p, atom())
                  else if trySymbol(DOLLAR) then Tm.Splice(p, atom())
                  else if trySymbol(L_BRACKET) then
                    if trySymbol(R_BRACKET) then Tm.EmptyRecord(p)
                    else
                      val tm = record(p)
                      symbol(R_BRACKET)
                      tm
                  else if trySymbol(L_PAREN) then
                    val p2 = pos
                    tryOp() match
                      case null =>
                        if trySymbol(R_PAREN) then Tm.UnitLit(p)
                        else
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
                            ArgInfo.PiExpl,
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
                case x if x.startsWith("_") =>
                  val y = if x.length == 1 then None else Some(Name(x.tail))
                  Tm.Hole(p, y)
                case x => Tm.Var(p, Name(x))
            case n =>
              n.toIntOption match
                case Some(n) => Tm.IntLit(p, n)
                case None    => err(s"invalid number literal: $n")
        case pr => Tm.Prim(p, pr)

    private def tryPrimitive(): Primitive | Null =
      val l = Primitives.length
      var i = 0
      while (i < l) {
        val p = Primitives(i)
        if tryKeyword(p) then
          p match
            case META     => return Primitive.Meta
            case TYPE     => return Primitive.Type
            case CV       => return Primitive.CV
            case VAL      => return Primitive.Val
            case COMP     => return Primitive.Comp
            case BOOL     => return Primitive.Bool
            case TRUE     => return Primitive.True
            case FALSE    => return Primitive.False
            case INT      => return Primitive.Int
            case LT       => return Primitive.Lt
            case ADD      => return Primitive.Add
            case SUB      => return Primitive.Sub
            case MUL      => return Primitive.Mul
            case IO       => return Primitive.IO
            case RETURNIO => return Primitive.ReturnIO
            case BINDIO   => return Primitive.BindIO
            case ID       => return Primitive.Id
            case REFL     => return Primitive.Refl
            case ELIMID   => return Primitive.ElimId
            case _        => return null
        i += 1
      }
      null

    private val RecordKindNone = 0
    private val RecordKind0 = 1
    private val RecordKind1 = 2
    private val RecordKindTy = 3
    private inline def recordKindSymbol(k: Int): Symbol =
      k match
        case RecordKind0  => COLON_EQUALS
        case RecordKind1  => EQUALS
        case RecordKindTy => COLON
    private def record(p: PosInfo): Tm =
      backtrack {
        val xs = list(tryBind())
        val kind =
          if trySymbol(COLON_EQUALS) then RecordKind0
          else if trySymbol(EQUALS) then RecordKind1
          else if trySymbol(COLON) then RecordKindTy
          else RecordKindNone
        if kind == RecordKindNone then null
        else
          val sym = recordKindSymbol(kind)
          val tm = expr()
          val tl = mutable.ArrayBuffer.empty[(List[Bind], Tm)]
          while trySymbol(COMMA) do
            val xs = list(tryBind())
            symbol(sym)
            val tm = expr()
            tl += ((xs.toList, tm))
          val fields = ((xs, tm) :: tl.toList).flatMap { (xs, tm) =>
            xs.map(x => (x, tm))
          }
          inline def checkIfNames(): Unit =
            fields.foreach((x, _) =>
              if x == DontBind then
                err("records literals cannot contain fields named _")
            )
          kind match
            case RecordKindTy => Tm.RecordTy(pos, fields)
            case RecordKind1 =>
              checkIfNames()
              Tm.RecordCon1(pos, fields.map((x, t) => (x.toName, t)))
            case RecordKind0 =>
              checkIfNames()
              Tm.RecordCon0(pos, fields.map((x, t) => (x.toName, t)))
      } match
        case null =>
          val hd = expr()
          val tl = mutable.ArrayBuffer.empty[Tm]
          while trySymbol(COMMA) do tl += expr()
          Tm.Tuple(p, hd :: tl.toList)
        case tm => tm

    private def tryAtom(): Tm | Null =
      tryAtomInner() match
        case null => null
        case tm =>
          val projs = mutable.ArrayBuffer.empty[(PosInfo, ProjType)]
          while trySymbol(PERIOD) do
            val p = pos
            val proj = tryNumber() match
              case null => ProjType.Named(nameOrOp())
              case n =>
                n.toIntOption match
                  case None    => err(s"invalid number for projection: $n")
                  case Some(n) => ProjType.Indexed(n)
            projs += ((p, proj))
          projs.foldLeft(tm) { case (tm, (p, proj)) =>
            Tm.Proj(p, tm, proj)
          }

    private def atom(): Tm =
      tryAtom() match
        case null => err("expected an expression")
        case a    => a

    @tailrec
    private def apps(
        res: mutable.ArrayBuffer[Tm | (PosInfo, String)] =
          mutable.ArrayBuffer.empty
    ): Tm =
      val hd = atom()
      val tl = list(tryArg())
      if trySymbol(BACKSLASH) then tl += ((lam(), ArgInfo.Expl))
      else if tryKeyword(MATCH) then tl += ((pmatch(), ArgInfo.Expl))
      val tm = tl.foldLeft(hd) { case (f, (a, i)) => Tm.App(a.pos, f, a, i) }
      res += tm
      inline def finalize() =
        val tm = shunting(res)
        val p = pos
        if trySymbol(ARROW) then
          val rt = expr()
          Tm.Pi(p, DontBind, PiIcit.Expl, tm, rt)
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

    private def tryArg(): (Tm, ArgInfo[Icit]) | Null =
      if trySymbol(L_BRACE) then
        inline def next(i: ArgInfo[Icit]): (Tm, ArgInfo[Icit]) | Null =
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
      val p = pos
      val x = (p, bind())
      val xs = list(tryBindPos())
      xs.insert(0, x)
      val ty = if trySymbol(COLON) then expr() else null
      (xs, ty)

    private def tryPiParam()
        : (PiIcit, mutable.ArrayBuffer[(PosInfo, Bind)], Tm) | Null =
      if trySymbol(L_PAREN) then
        if trySymbol(R_PAREN) then null
        else
          val p = pos
          tryBind() match
            case null => null
            case bx =>
              val x = (p, bx)
              val xs = list(tryBindPos())
              xs.insert(0, x)
              if trySymbol(COLON) then
                val ty = expr()
                symbol(R_PAREN)
                (PiIcit.Expl, xs, ty)
              else null
      else if trySymbol(L_BRACE) then
        val i =
          if tryKeyword(DEFAULT) then PiIcit.ImplD(atom())
          else PiIcit.ImplU
        val (xs, prety) = grouping()
        val p = pos
        val ty = prety match
          case null => Tm.Hole(p, None)
          case ty   => ty
        symbol(R_BRACE)
        (i, xs, ty)
      else null

    private def lam(): Tm =
      val ps = list(tryParam())
      symbol(DOUBLE_ARROW)
      val b = expr()
      ps.foldRight(b) { case ((a, xs, ty), b) =>
        xs.foldRight(b) { case ((p, x), b) => Tm.Lam(p, x, a, Option(ty), b) }
      }

    private def tryParam(): DefParam | Null =
      if trySymbol(L_PAREN) then
        val (xs, ty) = grouping()
        symbol(R_PAREN)
        (ArgInfo.PiExpl, xs, ty)
      else if trySymbol(L_BRACE) then
        val i =
          if tryKeyword(DEFAULT) then ArgInfo.PiImplD(atom())
          else ArgInfo.PiImplU
        val (xs, ty) = grouping()
        val named = if trySymbol(EQUALS) then nameOrOp() else null
        symbol(R_BRACE)
        val arginfo = named match
          case null => i
          case x    => ArgInfo.Named(x)
        (arginfo, xs, ty)
      else
        val p = pos
        tryBind() match
          case null => null
          case x    => (ArgInfo.PiExpl, mutable.ArrayBuffer((p, x)), null)

    private def defn(): (Boolean, Name, Tm | Null, Tm) =
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

    private def tryCaseParam(): List[(Bind, Icit)] | Null =
      if trySymbol(L_BRACE) then
        val xs = list(tryBind())
        symbol(R_BRACE)
        xs.map(x => (x, Impl)).toList
      else
        tryBind() match
          case null => null
          case x    => List((x, Expl))

    private def pcase(): Case =
      val p = pos
      val fst = bind()
      val (cx, ps) = tryOp() match
        case null => (fst, list(tryCaseParam()).flatten.toList)
        case op =>
          val snd = bind()
          (Bind.op(op), List((fst, Expl), (snd, Expl)))
      symbol(DOUBLE_ARROW)
      val b = expr()
      Case(p, cx, ps, b)

    private def pmatch(): Tm =
      val p = pos
      var startedWithBracket = false
      val (scrut, ty) =
        if trySymbol(L_BRACE) then
          startedWithBracket = true
          (None, None)
        else if trySymbol(PIPE) then (None, None)
        else
          val scrut = atom()
          val ty =
            if trySymbol(COLON) then
              val x = bind()
              symbol(DOUBLE_ARROW)
              val ty = expr()
              Some((x, ty))
            else None
          if trySymbol(L_BRACE) then startedWithBracket = true
          else symbol(PIPE)
          (Some(scrut), ty)
      val cs =
        if startedWithBracket && trySymbol(R_BRACE) then Nil
        else
          if startedWithBracket then trySymbol(PIPE)
          val hd = pcase()
          val tl =
            mutable.ArrayBuffer.empty[Case]
          while trySymbol(PIPE) do tl += pcase()
          if startedWithBracket then symbol(R_BRACE)
          hd :: tl.toList
      Tm.Match(p, scrut, ty, cs)

    private def expr(): Tm =
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
      else if tryKeyword(IF) then
        val c = expr()
        keyword(THEN)
        val t = expr()
        keyword(ELSE)
        val f = expr()
        Tm.If(p, c, t, f)
      else if tryKeyword(MATCH) then pmatch()
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

    private def tryDataConParam(): List[(Bind, PiIcit, Ty)] | Null =
      if trySymbol(L_BRACE) then
        val p = pos
        val i =
          if tryKeyword(DEFAULT) then PiIcit.ImplD(atom()) else PiIcit.ImplU
        val x = bind()
        val xs = list(tryBind())
        if trySymbol(COLON) then
          val ty = expr()
          symbol(R_BRACE)
          (x :: xs.toList).map(x => (x, i, ty))
        else
          symbol(R_BRACE)
          (x :: xs.toList).map(x => (x, i, Tm.Hole(p, None)))
      else
        backtrack {
          if trySymbol(L_PAREN) then
            tryBind() match
              case null => null
              case x =>
                val xs = list(tryBind())
                if trySymbol(COLON) then
                  val ty = expr()
                  symbol(R_PAREN)
                  (x :: xs.toList).map(x => (x, PiIcit.Expl, ty))
                else null
          else null
        } match
          case null =>
            tryAtom() match
              case null => null
              case t    => List((DontBind, PiIcit.Expl, t))
          case p => p

    private def dataCon(dataPub: Boolean): Constructor =
      val p = pos
      val pub =
        if tryKeyword(PRIV) then
          if dataPub then false
          else
            err(
              s"unnecessary priv for constructor, datatype is already private"
            )
        else dataPub
      val cx = nameOrOp()
      val ps = list(tryDataConParam()).toList.flatten
      Constructor(p, pub, cx, ps)

    private def tryDataParam(): List[(Name, Icit, Ty)] | Null =
      if trySymbol(L_BRACE) then
        val x = nameOrOp()
        val xs = list(tryNameOrOp())
        if trySymbol(COLON) then
          val ty = expr()
          symbol(R_BRACE)
          (x :: xs.toList).map(x => (x, Impl, ty))
        else
          symbol(R_BRACE)
          val p = pos
          (x :: xs.toList).map(x => (x, Impl, Tm.Hole(p, None)))
      else if trySymbol(L_PAREN) then
        val x = nameOrOp()
        val xs = list(tryNameOrOp())
        symbol(COLON)
        val ty = expr()
        symbol(R_PAREN)
        (x :: xs.toList).map(x => (x, Expl, ty))
      else
        tryNameOrOp() match
          case null => null
          case x    => List((x, Expl, Tm.Hole(pos, None)))

    private def data(pos: PosInfo, pub: Boolean): Def =
      val dx = nameOrOp()
      val ps = list(tryDataParam()).toList.flatten
      val univ = if trySymbol(COLON) then Some(expr()) else None
      val (continue, isMeta) =
        if trySymbol(COLON_EQUALS) then { trySymbol(PIPE); (true, Some(false)) }
        else if trySymbol(EQUALS) then { trySymbol(PIPE); (true, Some(true)) }
        else (trySymbol(PIPE), None)
      val cons = if continue then
        val hd = dataCon(pub)
        val tl = mutable.ArrayBuffer.empty[Constructor]
        while trySymbol(PIPE) do tl += dataCon(pub)
        hd :: tl.toList
      else Nil
      Def.Data(pos, pub, isMeta, dx, ps, univ, cons)

    private def tryDef(): Def | Null =
      val p = pos
      val pub = tryKeyword(PUB)
      if tryKeyword(DEF) then
        val (meta, x, ty, body) = defn()
        if meta then Def.Def1(p, pub, x, Option(ty), body)
        else Def.Def0(p, pub, x, Option(ty), body)
      else if tryKeyword(DATA) then data(p, pub)
      else null

    private def defs(): Defs = Defs(list(tryDef()).toList)

    @tailrec
    private def imports(
        res: mutable.ArrayBuffer[
          (PosInfo, PosInfo, Boolean, Name, Option[Name])
        ] = mutable.ArrayBuffer.empty
    ): mutable.ArrayBuffer[(PosInfo, PosInfo, Boolean, Name, Option[Name])] =
      if trySymbol(R_PAREN) then res
      else
        val p1 = pos
        val reexport = tryKeyword(PUB)
        val x = nameOrOp()
        var p2 = p1
        val r = if trySymbol(DOUBLE_ARROW) then
          p2 = pos
          Some(nameOrOp())
        else None
        res += ((p1, p2, reexport, x, r))
        if trySymbol(COMMA) then imports(res)
        else
          symbol(R_PAREN)
          res

    def module(mod: String): Module =
      val p = pos
      keyword(MODULE)
      val x = name()
      if x.expose != mod then
        err(
          s"module name does not match file name or path, expected $mod but got $x"
        )
      val deps = mutable.Set.empty[Name]
      val imps =
        mutable.ArrayBuffer
          .empty[(PosInfo, PosInfo, Boolean, Name, Name, Option[Name])]
      val moduleAliases = mutable.Map.empty[Name, Name]
      while tryKeyword(IMPORT) do
        val m = name()
        val xr = if trySymbol(DOUBLE_ARROW) then name() else m
        moduleAliases += m -> xr
        deps += m
        if trySymbol(L_PAREN) then
          imports().foreach((p1, p2, rex, x, r) =>
            imps += ((p1, p2, rex, m, x, r))
          )
      val ds = defs()
      Module(p, x, deps.toSet, imps.toList, moduleAliases.toMap, ds)
