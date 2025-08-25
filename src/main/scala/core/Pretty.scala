package core

import common.Common.*
import common.Common.Icit.*
import common.Common.Bind.*
import Core.*

import scala.annotation.tailrec

object Pretty:
  private def prettyApp0(tm: Tm0)(using ns: List[Bind]): String = tm match
    case Tm0.App(f, a) => s"${prettyApp0(f)} ${prettyParen0(a)}"
    case f             => prettyParen0(f)

  private def prettyApp1(tm: Tm1)(using ns: List[Bind]): String = tm match
    case Tm1.App(f, a, Expl) => s"${prettyApp1(f)} ${prettyParen1(a)}"
    case Tm1.App(f, a, Impl) => s"${prettyApp1(f)} {${pretty1(a)}}"
    case f                   => prettyParen1(f)

  private def prettyPi(tm: Ty)(using ns: List[Bind]): String = tm match
    case Tm1.Fun(a, _, b) => s"${prettyParen1(a, true)} -> ${prettyPi(b)}"
    case Tm1.Pi(DontBind, Expl, t, b) =>
      s"${prettyParen1(t, true)} -> ${prettyPi(b)(using DontBind :: ns)}"
    case Tm1.Pi(bx @ DoBind(x), Expl, t, b) =>
      s"($x : ${pretty1(t)}) -> ${prettyPi(b)(using bx :: ns)}"
    case Tm1.Pi(x, i, t, b) =>
      s"${i.wrap(s"$x : ${pretty1(t)}")} -> ${prettyPi(b)(using x :: ns)}"
    case rest => pretty1(rest)

  private def prettyLam0(tm: Tm0)(using ns: List[Bind]): String =
    def go(tm: Tm0, first: Boolean = false)(using ns: List[Bind]): String =
      tm match
        case Tm0.Lam(x, _, b) =>
          s"${if first then "" else " "}$x${go(b)(using x :: ns)}"
        case rest => s" => ${pretty0(rest)}"
    s"\\${go(tm, true)}"

  private def prettyLam1(tm: Tm1)(using ns: List[Bind]): String =
    def go(tm: Tm1, first: Boolean = false)(using ns: List[Bind]): String =
      tm match
        case Tm1.Lam(x, Expl, _, b) =>
          s"${if first then "" else " "}$x${go(b)(using x :: ns)}"
        case Tm1.Lam(x, Impl, _, b) =>
          s"${if first then "" else " "}{$x}${go(b)(using x :: ns)}"
        case rest => s" => ${pretty1(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  private def prettyParen0(tm: Tm0, app: Boolean = false)(using
      ns: List[Bind]
  ): String =
    tm match
      case Tm0.Var(_)           => pretty0(tm)
      case Tm0.IntLit(_)        => pretty0(tm)
      case Tm0.Global(_, _)     => pretty0(tm)
      case Tm0.Splice(_)        => pretty0(tm)
      case Tm0.App(_, _) if app => pretty0(tm)
      case Tm0.RecordCon(_, _)  => pretty0(tm)
      case Tm0.Proj(_, _, _)    => pretty0(tm)
      case Tm0.Wk1(tm)          => prettyParen0(tm, app)(using ns.tail)
      case _                    => s"(${pretty0(tm)})"

  @tailrec
  def prettyParen1(tm: Tm1, app: Boolean = false)(using
      ns: List[Bind]
  ): String =
    tm match
      case Tm1.Var(_)              => pretty1(tm)
      case Tm1.Primitive(_, _)     => pretty1(tm)
      case Tm1.Global(_, _, _)     => pretty1(tm)
      case Tm1.Con(_, _, _)        => pretty1(tm)
      case Tm1.TypeCon(_, _, _)    => pretty1(tm)
      case Tm1.Lift(_, _)          => pretty1(tm)
      case Tm1.Quote(_)            => pretty1(tm)
      case Tm1.App(_, _, _) if app => pretty1(tm)
      case Tm1.UMeta               => pretty1(tm)
      case Tm1.CV                  => pretty1(tm)
      case Tm1.Val                 => pretty1(tm)
      case Tm1.Comp                => pretty1(tm)
      case Tm1.RecordTy1(_)        => pretty1(tm)
      case Tm1.RecordTy0(_)        => pretty1(tm)
      case Tm1.RecordCon(_)        => pretty1(tm)
      case Tm1.Wk0(tm)             => prettyParen1(tm, app)(using ns.tail)
      case Tm1.Wk1(tm)             => prettyParen1(tm, app)(using ns.tail)
      case _                       => s"(${pretty1(tm)})"

  private def prettyLift0(x: Bind, tm: Tm0)(using ns: List[Bind]): String =
    pretty0(tm)(using x :: ns)
  private def prettyLift1(x: Bind, tm: Tm1)(using ns: List[Bind]): String =
    pretty1(tm)(using x :: ns)

  def pretty0(tm: Tm0)(using ns: List[Bind]): String = tm match
    case Tm0.Var(ix) =>
      ns(ix.expose) match
        case DontBind => s"_@${ns.size - ix.expose - 1}"
        case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
          s"$x@${ns.size - ix.expose - 1}"
        case DoBind(x) => s"$x"
    case Tm0.IntLit(v)          => v.toString
    case Tm0.Global(m, x)       => s"$m.$x"
    case Tm0.Select(_, _, s, i) => s"select $i ${pretty0(s)}"
    case Tm0.Let(x, t, v, b)    =>
      s"let $x : ${pretty1(t)} := ${pretty0(v)}; ${prettyLift0(x.toBind, b)}"
    case Tm0.LetRec(x, t, v, b) =>
      s"let rec $x : ${pretty1(t)} := ${prettyLift0(x.toBind, v)}; ${prettyLift0(x.toBind, b)}"

    case Tm0.Lam(_, _, _) => prettyLam0(tm)
    case Tm0.App(_, _)    => prettyApp0(tm)

    case Tm0.Splice(t)            => s"$$${prettyParen1(t)}"
    case Tm0.Instr(x, _, _, args) =>
      s"instr $x${if args.isEmpty then "" else " "}${args.map(pretty0).mkString(" ")}"

    case Tm0.Match(_, _, s, Nil, None)    => s"match ${pretty0(s)} { }"
    case Tm0.Match(_, _, s, Nil, Some(b)) =>
      s"match ${pretty0(s)} { _ => ${pretty0(b)} }"
    case Tm0.Match(_, _, s, cs, o) =>
      val scs =
        cs.map((x, b) => s"$x => ${prettyLift0(DoBind(Name("c")), b)}")
      val so = o.map(o => s" | _ => ${pretty0(o)}")
      s"match ${pretty0(s)} { ${scs.mkString(" | ")}$so }"

    case Tm0.RecordCon(_, fs) => fs.map(pretty0).mkString("[", ", ", "]")
    case Tm0.Proj(_, tm, p)   => s"${prettyParen0(tm)}.$p"

    case Tm0.Wk1(tm) => pretty0(tm)(using ns.tail)
    case Tm0.Wk0(tm) => pretty0(tm)(using ns.tail)

  def pretty1(tm: Tm1)(using ns: List[Bind]): String =
    def goRec(ns: List[Bind], fs: Assoc[Ty]): List[String] =
      fs match
        case Nil            => Nil
        case (x, t) :: rest =>
          val nns = DoBind(x) :: ns
          s"$x : ${pretty1(t)(using ns)}" :: goRec(nns, rest)
    tm match
      case Tm1.Var(ix) =>
        ns(ix.expose) match
          case DontBind => s"_@${ns.size - ix.expose - 1}"
          case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
            s"$x@${ns.size - ix.expose - 1}"
          case DoBind(x) => s"$x"
      case Tm1.Primitive(m, x)  => s"$m.$x"
      case Tm1.Global(m, x, _)  => s"$m.$x"
      case Tm1.Con(m, _, cx)    => s"$m.$cx"
      case Tm1.TypeCon(_, m, x) => s"$m.$x"
      case Tm1.Let(x, t, v, b)  =>
        s"let $x : ${pretty1(t)} = ${pretty1(v)}; ${prettyLift1(x.toBind, b)}"

      case Tm1.UTy(s) => s"type ${prettyParen1(s)}"
      case Tm1.UMeta  => "meta"

      case Tm1.CV   => "cv"
      case Tm1.Val  => "val"
      case Tm1.Comp => "comp"

      case Tm1.Pi(_, _, _, _)  => prettyPi(tm)
      case Tm1.Fun(_, _, _)    => prettyPi(tm)
      case Tm1.Lam(_, _, _, _) => prettyLam1(tm)
      case Tm1.App(_, _, _)    => prettyApp1(tm)

      case Tm1.Lift(_, t) => s"^${prettyParen1(t)}"
      case Tm1.Quote(t)   => s"`${prettyParen0(t)}"

      case Tm1.RecordTy1(fs) => goRec(ns, fs).mkString("[", ", ", "]")
      case Tm1.RecordTy0(fs) =>
        fs.map((x, t) => s"$x : ${pretty1(t)}").mkString("[", ", ", "]")
      case Tm1.RecordCon(fs) => fs.map(pretty1).mkString("[", ", ", "]")

      case Tm1.Wk0(tm) => pretty1(tm)(using ns.tail)
      case Tm1.Wk1(tm) => pretty1(tm)(using ns.tail)
