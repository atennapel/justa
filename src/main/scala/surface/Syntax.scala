package surface

import common.Common.*

object Syntax:
  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  enum Def:
    case DDef0(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)
    case DDef1(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)
    case DDefRec(pos: PosInfo, name: Name, ty: Option[Ty], value: Tm)

    override def toString: String = this match
      case DDef0(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case DDef1(_, x, t, v) =>
        s"def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case DDefRec(_, x, t, v) =>
        s"def rec $x${t.map(t => s" : $t").getOrElse("")} := $v"
  export Def.*

  enum ArgInfo:
    case ArgNamed(name: Name)
    case ArgIcit(icit: Icit)
  export ArgInfo.*

  type Ty = Tm
  enum Tm:
    case Var(name: Name)
    case Let0(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case LetRec(name: Name, ty: Option[Ty], value: Tm, body: Tm)

    case U0(cv: Ty)
    case U1

    case Pi(name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(name: Bind, info: ArgInfo, ty: Option[Ty], body: Tm)
    case App(fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(ty: Ty)
    case Quote(tm: Tm)
    case Splice(tm: Tm)

    case Hole(name: Option[Name])

    case Pos(pos: PosInfo, tm: Tm)

    def isPos: Boolean = this match
      case Pos(_, _) => true
      case _         => false

    override def toString: String = this match
      case Var(x) => s"$x"
      case Let0(x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Let1(x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} = $v; $b)"
      case LetRec(x, ty, v, b) =>
        s"(let rec $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case U0(cv)                         => s"(type $cv)"
      case U1                             => "meta"
      case Pi(DontBind, Expl, ty, b)      => s"($ty -> $b)"
      case Pi(x, i, ty, b)                => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(x, ArgIcit(Expl), None, b) => s"(\\$x => $b)"
      case Lam(x, ArgIcit(i), ty, b) =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")} => $b)"
      case Lam(x, ArgNamed(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")} => $b)"
      case App(fn, arg, ArgIcit(Expl)) => s"($fn $arg)"
      case App(fn, arg, ArgIcit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(fn, arg, ArgNamed(x))   => s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(ty)                    => s"^$ty"
      case Quote(tm)                   => s"`$tm"
      case Splice(tm)                  => s"$$$tm"
      case Hole(None)                  => s"_"
      case Hole(Some(x))               => s"_$x"
      case Pos(_, tm)                  => s"$tm"
  export Tm.*
