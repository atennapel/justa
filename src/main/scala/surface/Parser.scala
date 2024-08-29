package surface

import common.Common.*
import Syntax.*
import Lexer.implicits.implicitSymbol

import parsley.Parsley
import parsley.Result
import parsley.Parsley.*
import parsley.errors.ErrorBuilder
import parsley.combinator.option
import parsley.expr.{precedence, Ops, InfixL, InfixR, Prefix}

object Parser:
  private val unittype = Var(Name("()"))
  private val hole = Hole(None)

  private val userOp: Parsley[Name] = Lexer.userOp.map(Name.apply)
  private val id: Parsley[Name] =
    Lexer.id.filter(x => !x.startsWith("_")).map(Name.apply)
  private val idOrOp: Parsley[Name] = ("(" ~> userOp <~ ")") | id
  private val bind: Parsley[Bind] =
    ("(" ~> userOp <~ ")").map(DoBind.apply) | Lexer.id.map {
      case x if x.startsWith("_") => DontBind
      case x                      => DoBind(Name(x))
    }

  private val varOrHole: Parsley[Tm] =
    Lexer.id.map(x =>
      if x.startsWith("_") then
        Hole(if x.length == 1 then None else Some(Name(x.tail)))
      else Var(Name(x))
    )

  private def positioned(p: => Parsley[Tm]): Parsley[Tm] =
    (pos <~> p).map(Pos.apply)

  private lazy val atom: Parsley[Tm] = positioned(
    ("^" ~> atom).map(Lift.apply) |
      ("`" ~> atom).map(Quote.apply) |
      ("$" ~> atom).map(Splice.apply) |
      ("(" ~> tm <~ ")") |
      "meta".as(U1) |
      ("type" ~> atom).map(U0.apply) |
      varOrHole
  )

  private lazy val tm: Parsley[Tm] = atomic(pi) | let | lam |
    precedence[Tm](app)(
      Ops(InfixR)("->".as((l, r) => Pi(DontBind, Expl, l, r)))
    )

  private type PiParam = (List[Bind], Icit, Option[Ty])
  private lazy val piParam: Parsley[PiParam] =
    ("{" ~> some(bind) <~> option(":" ~> tm) <~ "}")
      .map((xs, t) => (xs, Impl, t)) |
      ("(" ~> (")" <+> (some(bind) <~> option(":" ~> tm) <~ ")")))
        .map {
          case Left(_)        => (List(DontBind), Expl, Some(unittype))
          case Right((xs, t)) => (xs, Expl, t)
        }

  private lazy val pi: Parsley[Tm] = positioned(
    ((some(piParam) |
      app.map(t => List((List(DontBind), Expl, Some(t))))) <~> "->" ~> tm).map {
      case (ps, rt) =>
        ps.foldRight(rt) { case ((xs, i, ty), rt) =>
          xs.foldRight(rt)((x, rt) => Pi(x, i, ty.getOrElse(hole), rt))
        }
    }
  )

  private type DefParam = (List[Bind], Icit, Option[Ty])
  private val defParam: Parsley[DefParam] =
    piParam | bind.map(x => (List(x), Expl, None))

  private lazy val let: Parsley[Tm] = positioned(
    ("let" ~> (("rec" ~> idOrOp <~> many(defParam) <~> option(":" ~> tm) <~>
      ":=" ~> tm <~> ";" ~> tm) <+>
      (idOrOp <~> many(defParam) <~> option(":" ~> tm) <~> (":=" <+> "=") <~>
        tm <~> ";" ~> tm)))
      .map {
        case Left(((((x, ps), t), v), b)) =>
          LetRec(
            x,
            t.map(typeFromParams(false, ps, _)),
            lamFromDefParams(ps, v, t.isEmpty),
            b
          )
        case Right((((((x, ps), t), Left(_)), v), b)) =>
          Let0(
            x,
            t.map(typeFromParams(false, ps, _)),
            lamFromDefParams(ps, v, t.isEmpty),
            b
          )
        case Right((((((x, ps), t), Right(_)), v), b)) =>
          Let1(
            x,
            t.map(typeFromParams(true, ps, _)),
            lamFromDefParams(ps, v, t.isEmpty),
            b
          )
      }
  )

  private type LamParam = (List[Bind], ArgInfo, Option[Ty])
  private val lamParam: Parsley[LamParam] =
    ("{" ~> some(bind) <~> option(":" ~> tm) <~> option("=" ~> idOrOp) <~ "}")
      .map {
        case ((xs, t), None)    => (xs, ArgIcit(Impl), t)
        case ((xs, t), Some(y)) => (xs, ArgNamed(y), t)
      } |
      ("(" ~> (")" <+> (some(bind) <~> option(":" ~> tm) <~ ")")))
        .map {
          case Left(_)        => (List(DontBind), ArgIcit(Expl), Some(unittype))
          case Right((xs, t)) => (xs, ArgIcit(Expl), t)
        } |
      bind.map(x => (List(x), ArgIcit(Expl), None))
  private lazy val lam: Parsley[Tm] = positioned(
    ("\\" ~> many(lamParam) <~> "=>" ~> tm).map(lamFromLamParams)
  )

  private lazy val app: Parsley[Tm] = {
    val ops = defaultOps[Tm](
      (op, t) => App(Var(op), t, ArgIcit(Expl)),
      (op, l, r) => App(App(Var(op), l, ArgIcit(Expl)), r, ArgIcit(Expl))
    )
    precedence[Tm](appAtom | lam)(ops.head, ops.tail*)
  }

  private lazy val appAtom: Parsley[Tm] = positioned(
    (atom <~> many(arg) <~> option(lam)).map { case ((fn, args), optArg) =>
      (args.flatten ++ optArg.map(t => (t, ArgIcit(Expl))))
        .foldLeft(fn) { case (fn, (arg, i)) => App(fn, arg, i) }
    }
  )

  private type Arg = (Tm, ArgInfo)
  private lazy val arg: Parsley[List[Arg]] =
    atomic("{" ~> some(idOrOp) <~> "=" ~> tm <~ "}")
      .map((xs, t) => xs.map(x => (t, ArgNamed(x)))) |
      ("{" ~> tm <~ "}").map(t => List((t, ArgIcit(Impl)))) |
      atom.map(t => List((t, ArgIcit(Expl))))

  // defs
  private val defP: Parsley[Def] =
    (pos <~> "native" ~> idOrOp <~> many(defParam) <~> ":" ~> tm).map {
      case (((p, x), ps), rt) =>
        DNative(p, x, typeFromParams(true, ps, rt))
    } |
      (pos <~> "def" ~> (("rec" ~> idOrOp <~> many(defParam) <~> option(
        ":" ~> tm
      ) <~>
        ":=" ~> tm) <+>
        (idOrOp <~> many(defParam) <~> option(
          ":" ~> tm
        ) <~> (":=" <+> "=") <~> tm)))
        .map {
          case (p, Left((((x, ps), t), v))) =>
            DDefRec(
              p,
              x,
              t.map(typeFromParams(false, ps, _)),
              lamFromDefParams(ps, v, t.isEmpty)
            )
          case (p, Right(((((x, ps), t), Left(_)), v))) =>
            DDef0(
              p,
              x,
              t.map(typeFromParams(false, ps, _)),
              lamFromDefParams(ps, v, t.isEmpty)
            )
          case (p, Right(((((x, ps), t), Right(_)), v))) =>
            DDef1(
              p,
              x,
              t.map(typeFromParams(true, ps, _)),
              lamFromDefParams(ps, v, t.isEmpty)
            )
        }

  private val defs: Parsley[Defs] = many(defP).map(Defs.apply)

  def parse[Err: ErrorBuilder](input: String): Result[Err, Defs] =
    Lexer.fully(defs).parse(input)

  // operators
  private def userOpStart(s: String): Parsley[String] =
    Lexer.userOp.filter(_.startsWith(s))

  private def opL[T](
      o: String,
      handle: (Name, T, T) => T
  ): Parsley[InfixL.Op[T, T]] =
    atomic(userOpStart(o).filterNot(_.endsWith(":"))).map(op =>
      (l, r) => handle(Name(op), l, r)
    )

  private def opR[T](
      o: String,
      handle: (Name, T, T) => T
  ): Parsley[InfixR.Op[T, T]] =
    atomic(userOpStart(o)).map(op => (l, r) => handle(Name(op), l, r))

  private def opP[T](
      o: String,
      handle: (Name, T) => T
  ): Parsley[Prefix.Op[T, T]] =
    atomic(userOpStart(o)).map(op => t => handle(Name(op), t))

  private def opLevel[T](
      s: String,
      prefix: (Name, T) => T,
      infix: (Name, T, T) => T
  ): List[Ops[T, T]] =
    val chars = s.toList
    List(
      Ops(Prefix)(chars.map(c => opP(c.toString, prefix))*),
      Ops(InfixL)(chars.map(c => opL(c.toString, infix))*),
      Ops(InfixR)(chars.map(c => opR(c.toString, infix))*)
    )

  private def ops[T](prefix: (Name, T) => T, infix: (Name, T, T) => T)(
      ss: String*
  ): List[Ops[T, T]] = ss.flatMap(s => opLevel(s, prefix, infix)).toList

  private def defaultOps[T](
      prefix: (Name, T) => T,
      infix: (Name, T, T) => T
  ): List[Ops[T, T]] =
    ops(prefix, infix)(
      "`@#?,.",
      "*/%",
      "+-",
      ":",
      "=!",
      "<>",
      "&",
      "^",
      "|",
      "$",
      "~"
    )

  // helpers
  private def lamFromLamParams(ps: List[LamParam], b: Tm): Tm =
    ps.foldRight(b) { case ((xs, i, ty), b) =>
      xs.foldRight(b)(Lam(_, i, ty, _))
    }

  private def typeFromParams(meta: Boolean, ps: List[DefParam], rt: Ty): Ty =
    ps.foldRight(rt) { case ((xs, i, ty), b) =>
      xs.foldRight(b)((x, b) =>
        Pi(if meta then x else DontBind, i, ty.getOrElse(hole), b)
      )
    }

  private def lamFromDefParams(
      ps: List[DefParam],
      b: Tm,
      useTypes: Boolean
  ): Tm =
    ps.foldRight(b) { case ((xs, i, ty), b) =>
      xs.foldRight(b)(
        Lam(
          _,
          ArgIcit(i),
          if useTypes then Some(ty.getOrElse(hole)) else None,
          _
        )
      )
    }
