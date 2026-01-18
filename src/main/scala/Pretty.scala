import Common.*
import Common.Icit.*
import Common.Bind.*
import Core.*
import Core.{Tm1 as T1, Tm0 as T0}

import scala.annotation.tailrec

// TODO: ensure this produces syntax that can be parsed
object Pretty:
  private def prettyApp0(tm: Tm0)(using ns: Seq[Bind]): String = tm match
    case T0.App(f, a) => s"${prettyApp0(f)} ${prettyParen0(a)}"
    case f            => prettyParen0(f)

  private def prettyApp1(tm: Tm1)(using ns: Seq[Bind]): String = tm match
    case T1.App(f, a, Expl) => s"${prettyApp1(f)} ${prettyParen1(a)}"
    case T1.App(f, a, Impl) => s"${prettyApp1(f)} {${pretty1(a)}}"
    case T1.MetaApp1(f, a)  => s"${prettyApp1(f)} ${prettyParen1(a)}"
    case T1.MetaApp0(f, a)  => s"${prettyApp1(f)} ${prettyParen0(a)}"
    case f                  => prettyParen1(f)

  private def prettyPi(tm: Ty)(using ns: Seq[Bind]): String = tm match
    case T1.Fun(a, _, b) => s"${prettyParen1(a, true)} -> ${prettyPi(b)}"
    case T1.Pi(DontBind, Expl, t, b) =>
      s"${prettyParen1(t, true)} -> ${prettyPi(b)(using DontBind +: ns)}"
    case T1.Pi(bx @ DoBind(x), Expl, t, b) =>
      s"($x : ${pretty1(t)}) -> ${prettyPi(b)(using bx +: ns)}"
    case T1.Pi(x, i, t, b) =>
      s"${i.wrap(s"$x : ${pretty1(t)}")} -> ${prettyPi(b)(using x +: ns)}"
    case T1.MetaPi1(t, b) =>
      s"${prettyParen1(t, true)} 1-> ${prettyPi(b)(using DontBind +: ns)}"
    case T1.MetaPi0(t, b) =>
      s"${prettyParen1(t, true)} 0-> ${prettyPi(b)(using DontBind +: ns)}"
    case rest => pretty1(rest)

  private def prettyLam0(tm: Tm0)(using ns: Seq[Bind]): String =
    def go(tm: Tm0, first: Boolean = false)(using ns: Seq[Bind]): String =
      tm match
        case T0.Lam(x, _, b) =>
          s"${if first then "" else " "}$x${go(b)(using x +: ns)}"
        case rest => s" => ${pretty0(rest)}"
    s"\\${go(tm, true)}"

  private def prettyLam1(tm: Tm1)(using ns: Seq[Bind]): String =
    def go(tm: Tm1, first: Boolean = false)(using ns: Seq[Bind]): String =
      tm match
        case T1.Lam(x, Expl, _, b) =>
          s"${if first then "" else " "}$x${go(b)(using x +: ns)}"
        case T1.Lam(x, Impl, _, b) =>
          s"${if first then "" else " "}{$x}${go(b)(using x +: ns)}"
        case T1.MetaLam1(b) =>
          s"${if first then "" else " "}1${go(b)(using DontBind +: ns)}"
        case T1.MetaLam0(b) =>
          s"${if first then "" else " "}0${go(b)(using DontBind +: ns)}"
        case rest => s" => ${pretty1(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  def prettyParen0(tm: Tm0, app: Boolean = false)(using
      ns: Seq[Bind]
  ): String =
    tm match
      case T0.Var(_)           => pretty0(tm)
      case T0.Global(_, _)     => pretty0(tm)
      case T0.IntLit(_)        => pretty0(tm)
      case T0.Splice(_)        => pretty0(tm)
      case T0.App(_, _) if app => pretty0(tm)
      case T0.Proj(_, _, _)    => pretty0(tm)
      case Tm0.RecordCon(_, _) => pretty0(tm)
      case T0.Wk0(tm)          => prettyParen0(tm, app)(using ns.tail)
      case T0.Wk1(tm)          => prettyParen0(tm, app)(using ns.tail)
      case _                   => s"(${pretty0(tm)})"

  @tailrec
  def prettyParen1(tm: Tm1, app: Boolean = false)(using
      ns: Seq[Bind]
  ): String =
    tm match
      case T1.Var(_)                => pretty1(tm)
      case T1.Global(_, _, _)       => pretty1(tm)
      case T1.Prim(_)               => pretty1(tm)
      case T1.TypeCon(_, _)         => pretty1(tm)
      case T1.Con(_, _, _)          => pretty1(tm)
      case T1.Meta(_)               => pretty1(tm)
      case T1.Lift(_, _)            => pretty1(tm)
      case T1.Quote(_)              => pretty1(tm)
      case T1.AppPruning(_, _)      => pretty1(tm)
      case T1.App(_, _, _) if app   => pretty1(tm)
      case T1.MetaApp1(_, _) if app => pretty1(tm)
      case T1.MetaApp0(_, _) if app => pretty1(tm)
      case T1.RecordTy1(_)          => pretty1(tm)
      case T1.RecordTy0(_)          => pretty1(tm)
      case T1.RecordCon(_)          => pretty1(tm)
      case T1.Proj(_, _)            => pretty1(tm)
      case T1.Wk0(tm)               => prettyParen1(tm, app)(using ns.tail)
      case T1.Wk1(tm)               => prettyParen1(tm, app)(using ns.tail)
      case _                        => s"(${pretty1(tm)})"

  private inline def prettyLift0(x: Bind, tm: Tm0)(using
      ns: Seq[Bind]
  ): String =
    pretty0(tm)(using x +: ns)

  private inline def prettyLift1(x: Bind, tm: Tm1)(using
      ns: Seq[Bind]
  ): String =
    pretty1(tm)(using x +: ns)

  def pretty0(tm: Tm0)(using ns: Seq[Bind]): String = tm match
    case T0.Var(ix) =>
      ns(ix.expose) match
        case DontBind => s"_@${ns.size - ix.expose - 1}"
        case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
          s"$x@${ns.size - ix.expose - 1}"
        case DoBind(x) => s"$x"
    case T0.Global(m, x) => s"$m.$x"
    case T0.IntLit(v)    => s"$v"
    case T0.Let(x, t, v, b) =>
      s"let $x : ${pretty1(t)} := ${pretty0(v)}; ${prettyLift0(x.toBind, b)}"
    case T0.LetRec(x, t, v, b) =>
      s"let rec $x : ${pretty1(t)} := ${prettyLift0(x.toBind, v)}; ${prettyLift0(x.toBind, b)}"

    case T0.Lam(_, _, _) => prettyLam0(tm)
    case T0.App(_, _)    => prettyApp0(tm)

    case T0.If(_, c, t, f) =>
      s"if ${pretty0(c)} then ${pretty0(t)} else ${pretty0(f)}"

    case T0.Splice(t) => s"$$${prettyParen1(t)}"

    case T0.Wk1(tm) => pretty0(tm)(using ns.tail)
    case T0.Wk0(tm) => pretty0(tm)(using ns.tail)

    case Tm0.RecordCon(_, fs) => fs.map(pretty0).mkString("[", ", ", "]")
    case T0.Proj(_, s, p)     => s"${prettyParen0(s)}.$p"

    case T0.Case(_, _, s, Cases.Empty) => s"match $s {}"
    case T0.Case(_, _, s, cs) =>
      def go(c: Cases): String =
        c match
          case Cases.Ext(x, Nil, b, r) =>
            val next = if r.isEmpty then "" else s" | ${go(r)}"
            s"$x => ${pretty0(b)}$next"
          case Cases.Ext(x, ps, b, r) =>
            val innerns = ps.map((x, _) => x).reverse ++ ns
            val next = if r.isEmpty then "" else s" | ${go(r)}"
            s"$x ${ps.map((x, _) => x).mkString(" ")} => ${pretty0(b)(using innerns)}$next"
          case Cases.Otherwise(b) => s"_ => ${pretty0(b)}"
          case Cases.Empty        => s""
      s"match ${pretty0(s)} { ${go(cs)} }"

  private def goRec(ns: Seq[Bind], fs: Assoc[Ty]): Seq[String] =
    fs match
      case Nil => Nil
      case (x, t) :: rest =>
        val nns = DoBind(x) +: ns
        s"$x : ${pretty1(t)(using ns)}" +: goRec(nns, rest)

  def pretty1(tm: Tm1)(using ns: Seq[Bind]): String = tm match
    case T1.Var(ix) =>
      ns(ix.expose) match
        case DontBind => s"_@${ns.size - ix.expose - 1}"
        case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
          s"$x@${ns.size - ix.expose - 1}"
        case DoBind(x) => s"$x"
    case T1.Global(m, x, _) => s"$m.$x"
    case T1.Prim(p)         => s"$p"
    case T1.TypeCon(m, x)   => s"$m.$x"
    case T1.Con(m, _, cx)   => s"$m.$cx"
    case T1.Let(x, t, v, b) =>
      s"let $x : ${pretty1(t)} = ${pretty1(v)}; ${prettyLift1(x.toBind, b)}"

    case T1.Pi(_, _, _, _)  => prettyPi(tm)
    case T1.Fun(_, _, _)    => prettyPi(tm)
    case T1.MetaPi1(_, _)   => prettyPi(tm)
    case T1.MetaPi0(_, _)   => prettyPi(tm)
    case T1.Lam(_, _, _, _) => prettyLam1(tm)
    case T1.MetaLam1(_)     => prettyLam1(tm)
    case T1.MetaLam0(_)     => prettyLam1(tm)
    case T1.App(_, _, _)    => prettyApp1(tm)
    case T1.MetaApp1(_, _)  => prettyApp1(tm)
    case T1.MetaApp0(_, _)  => prettyApp1(tm)

    case T1.Lift(_, t) => s"^${prettyParen1(t)}"
    case T1.Quote(t)   => s"`${prettyParen0(t)}"

    case Tm1.RecordTy1(fs) => goRec(ns, fs).mkString("[", ", ", "]")
    case Tm1.RecordTy0(fs) =>
      fs.map((x, t) => s"$x : ${pretty1(t)}").mkString("[", ", ", "]")
    case Tm1.RecordCon(fs) => fs.map(pretty1).mkString("[", ", ", "]")
    case Tm1.Proj(tm, p)   => s"${prettyParen1(tm)}.$p"

    case T1.Wk0(tm) => pretty1(tm)(using ns.tail)
    case T1.Wk1(tm) => pretty1(tm)(using ns.tail)

    case T1.Meta(id)          => s"?$id"
    case T1.AppPruning(id, _) => s"?*$id"
