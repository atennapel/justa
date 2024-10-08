package core

import common.Common.*
import Syntax.*

import scala.annotation.tailrec

object Pretty:
  private def prettyApp0(tm: Tm0)(implicit ns: List[Bind]): String = tm match
    case App0(f, a) => s"${prettyApp0(f)} ${prettyParen0(a)}"
    case f          => prettyParen0(f)

  private def prettyApp1(tm: Tm1)(implicit ns: List[Bind]): String = tm match
    case App1(f, a, Expl) => s"${prettyApp1(f)} ${prettyParen1(a)}"
    case App1(f, a, Impl) => s"${prettyApp1(f)} {${pretty1(a)}}"
    case MetaApp1(f, a)   => s"${prettyApp1(f)} ${prettyParen1(a)}"
    case MetaApp0(f, a)   => s"${prettyApp1(f)} ${prettyParen0(a)}"
    case f                => prettyParen1(f)

  private def prettyPi(tm: Ty)(implicit ns: List[Bind]): String = tm match
    case Fun(a, _, b) => s"${prettyParen1(a, true)} -> ${prettyPi(b)}"
    case Pi(DontBind, Expl, t, b) =>
      s"${prettyParen1(t, true)} -> ${prettyPi(b)(DontBind :: ns)}"
    case Pi(bx @ DoBind(x), Expl, t, b) =>
      s"($x : ${pretty1(t)}) -> ${prettyPi(b)(bx :: ns)}"
    case Pi(x, i, t, b) =>
      s"${i.wrap(s"$x : ${pretty1(t)}")} -> ${prettyPi(b)(x :: ns)}"
    case MetaPi1(t, b) =>
      s"${prettyParen1(t, true)} 1-> ${prettyPi(b)(DontBind :: ns)}"
    case MetaPi0(t, b) =>
      s"${prettyParen1(t, true)} 0-> ${prettyPi(b)(DontBind :: ns)}"
    case rest => pretty1(rest)

  private def prettyLam0(tm: Tm0)(implicit ns: List[Bind]): String =
    def go(tm: Tm0, first: Boolean = false)(implicit ns: List[Bind]): String =
      tm match
        case Lam0(x, _, b) =>
          s"${if first then "" else " "}$x${go(b)(x :: ns)}"
        case rest => s" => ${pretty0(rest)}"
    s"\\${go(tm, true)}"

  private def prettyLam1(tm: Tm1)(implicit ns: List[Bind]): String =
    def go(tm: Tm1, first: Boolean = false)(implicit ns: List[Bind]): String =
      tm match
        case Lam1(x, Expl, _, b) =>
          s"${if first then "" else " "}$x${go(b)(x :: ns)}"
        case Lam1(x, Impl, _, b) =>
          s"${if first then "" else " "}{$x}${go(b)(x :: ns)}"
        case MetaLam1(b) =>
          s"${if first then "" else " "}1${go(b)(DontBind :: ns)}"
        case MetaLam0(b) =>
          s"${if first then "" else " "}0${go(b)(DontBind :: ns)}"
        case rest => s" => ${pretty1(rest)}"
    s"\\${go(tm, true)}"

  @tailrec
  def prettyParen0(tm: Tm0, app: Boolean = false)(implicit
      ns: List[Bind]
  ): String =
    tm match
      case Var0(_)           => pretty0(tm)
      case Global0(_)        => pretty0(tm)
      case Splice(_)         => pretty0(tm)
      case App0(_, _) if app => pretty0(tm)
      case Wk10(tm)          => prettyParen0(tm, app)(ns.tail)
      case _                 => s"(${pretty0(tm)})"

  @tailrec
  def prettyParen1(tm: Tm1, app: Boolean = false)(implicit
      ns: List[Bind]
  ): String =
    tm match
      case Var1(_)               => pretty1(tm)
      case Global1(_)            => pretty1(tm)
      case Native(_)             => pretty1(tm)
      case Meta(_)               => pretty1(tm)
      case Lift(_, _)            => pretty1(tm)
      case Quote(_)              => pretty1(tm)
      case AppPruning(_, _)      => pretty1(tm)
      case App1(_, _, _) if app  => pretty1(tm)
      case MetaApp1(_, _) if app => pretty1(tm)
      case MetaApp0(_, _) if app => pretty1(tm)
      case U1                    => pretty1(tm)
      case CV                    => pretty1(tm)
      case CVV                   => pretty1(tm)
      case CVC                   => pretty1(tm)
      case Wk01(tm)              => prettyParen1(tm, app)(ns.tail)
      case Wk11(tm)              => prettyParen1(tm, app)(ns.tail)
      case _                     => s"(${pretty1(tm)})"

  private def prettyLift0(x: Bind, tm: Tm0)(implicit ns: List[Bind]): String =
    pretty0(tm)(x :: ns)

  private def prettyLift1(x: Bind, tm: Tm1)(implicit ns: List[Bind]): String =
    pretty1(tm)(x :: ns)

  def pretty0(tm: Tm0)(implicit ns: List[Bind]): String = tm match
    case Var0(ix) =>
      ns(ix.expose) match
        case DontBind => s"_@${ns.size - ix.expose - 1}"
        case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
          s"$x@${ns.size - ix.expose - 1}"
        case DoBind(x) => s"$x"
    case Global0(x) => s"$x"
    case Let0(x, t, v, b) =>
      s"let $x : ${pretty1(t)} := ${pretty0(v)}; ${prettyLift0(x.toBind, b)}"
    case LetRec(x, t, v, b) =>
      s"let rec $x : ${pretty1(t)} := ${prettyLift0(x.toBind, v)}; ${prettyLift0(x.toBind, b)}"

    case Lam0(_, _, _) => prettyLam0(tm)
    case App0(_, _)    => prettyApp0(tm)

    case Splice(t) => s"$$${prettyParen1(t)}"

    case Wk10(tm) => pretty0(tm)(ns.tail)
    case Wk00(tm) => pretty0(tm)(ns.tail)

  def pretty1(tm: Tm1)(implicit ns: List[Bind]): String = tm match
    case Var1(ix) =>
      ns(ix.expose) match
        case DontBind => s"_@${ns.size - ix.expose - 1}"
        case DoBind(x) if ns.take(ix.expose).contains(DoBind(x)) =>
          s"$x@${ns.size - ix.expose - 1}"
        case DoBind(x) => s"$x"
    case Global1(x) => s"$x"
    case Native(x)  => s"$x"
    case Let1(x, t, v, b) =>
      s"let $x : ${pretty1(t)} = ${pretty1(v)}; ${prettyLift1(x.toBind, b)}"

    case U0(s) => s"type ${prettyParen1(s)}"
    case U1    => "meta"

    case CV  => "CV"
    case CVV => "Val"
    case CVC => "Comp"

    case Pi(_, _, _, _)   => prettyPi(tm)
    case Fun(_, _, _)     => prettyPi(tm)
    case MetaPi1(_, _)    => prettyPi(tm)
    case MetaPi0(_, _)    => prettyPi(tm)
    case Lam1(_, _, _, _) => prettyLam1(tm)
    case MetaLam1(_)      => prettyLam1(tm)
    case MetaLam0(_)      => prettyLam1(tm)
    case App1(_, _, _)    => prettyApp1(tm)
    case MetaApp1(_, _)   => prettyApp1(tm)
    case MetaApp0(_, _)   => prettyApp1(tm)

    case Lift(_, t) => s"^${prettyParen1(t)}"
    case Quote(t)   => s"`${prettyParen0(t)}"

    case Wk01(tm) => pretty1(tm)(ns.tail)
    case Wk11(tm) => pretty1(tm)(ns.tail)

    case Meta(id)          => s"?$id"
    case AppPruning(id, _) => s"?*$id"
