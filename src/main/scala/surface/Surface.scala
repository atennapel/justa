package surface

import common.Common.*
import common.Common.Icit.*
import common.Common.Bind.*

object Surface:
  final case class Module(
      name: Name,
      deps: Set[Name],
      imports: Map[Name, (PosInfo, PosInfo, Name, Option[Name])],
      moduleAliases: Map[Name, Name],
      defs: Defs
  ):
    override def toString: String =
      s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Constructor(
      pos: PosInfo,
      public: Boolean,
      name: Name,
      params: List[(Option[Bind], Ty)]
  ):
    override def toString: String =
      val ps = params
        .map((ox, t) => ox.fold(t.toString)(x => s"($x : $t)"))
        .mkString(" ")
      s"$name $ps"

  enum Def:
    case D0(
        pos: PosInfo,
        public: Boolean,
        name: Name,
        ty: Option[Ty],
        value: Tm
    )
    case D1(
        pos: PosInfo,
        public: Boolean,
        name: Name,
        ty: Option[Ty],
        value: Tm
    )
    case Primitive(
        pos: PosInfo,
        public: Boolean,
        name: Name,
        ty: Ty
    )
    case Data(
        pos: PosInfo,
        public: Boolean,
        name: Name,
        kind: DataKind,
        cons: List[Constructor]
    )
    override def toString: String = this match
      case D0(_, p, x, t, v) =>
        s"${if p then "pub " else ""}def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case D1(_, p, x, t, v) =>
        s"${if p then "pub " else ""}def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case Primitive(_, p, x, t) =>
        s"${if p then "pub " else ""}primitive $x : $t"
      case Data(_, p, x, k, cs) =>
        val css = cs.mkString(" | ")
        s"${if p then "pub " else ""}$k $x = $css"

  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: common.Common.Icit)

  type Ty = Tm
  enum Tm:
    case Var(posInfo: PosInfo, mod: Option[Name], name: Name)
    case IntLit(posInfo: PosInfo, value: Int)

    case Let0(posInfo: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(posInfo: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case LetRec(
        posInfo: PosInfo,
        name: Name,
        ty: Option[Ty],
        value: Tm,
        body: Tm
    )

    case Pi(posInfo: PosInfo, name: Bind, icit: Icit, ty: Ty, body: Ty)
    case Lam(
        posInfo: PosInfo,
        name: Bind,
        info: ArgInfo,
        ty: Option[Ty],
        body: Ty
    )
    case App(posInfo: PosInfo, fn: Tm, arg: Tm, info: ArgInfo)

    case Lift(posInfo: PosInfo, ty: Ty)
    case Quote(posInfo: PosInfo, tm: Tm)
    case Splice(posInfo: PosInfo, tm: Tm)

    case Hole(posInfo: PosInfo, name: Option[Name])

    case Instr(posInfo: PosInfo, instr: String, args: List[Tm])

    def pos: PosInfo = this match
      case Tm.Var(pos, _, _)          => pos
      case Tm.IntLit(pos, _)          => pos
      case Tm.Let0(pos, _, _, _, _)   => pos
      case Tm.Let1(pos, _, _, _, _)   => pos
      case Tm.LetRec(pos, _, _, _, _) => pos
      case Tm.Pi(pos, _, _, _, _)     => pos
      case Tm.Lam(pos, _, _, _, _)    => pos
      case Tm.App(pos, _, _, _)       => pos
      case Tm.Lift(pos, _)            => pos
      case Tm.Quote(pos, _)           => pos
      case Tm.Splice(pos, _)          => pos
      case Tm.Hole(pos, _)            => pos
      case Tm.Instr(pos, _, _)        => pos

    override def toString: String = this match
      case Var(_, None, x)      => s"$x"
      case Var(_, Some(m), x)   => s"$m.$x"
      case IntLit(_, v)         => v.toString
      case Let0(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Let1(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} = $v; $b)"
      case LetRec(_, x, ty, v, b) =>
        s"(let rec $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Pi(_, DontBind, Expl, ty, b) => s"($ty -> $b)"
      case Pi(_, x, i, ty, b)           => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(_, x, ArgInfo.Icit(Expl), None, b) => s"(\\$x => $b)"
      case Lam(_, x, ArgInfo.Icit(i), ty, b)      =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")} => $b)"
      case Lam(_, x, ArgInfo.Named(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")} => $b)"
      case App(_, fn, arg, ArgInfo.Icit(Expl)) => s"($fn $arg)"
      case App(_, fn, arg, ArgInfo.Icit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(_, fn, arg, ArgInfo.Named(x))   =>
        s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(_, ty)       => s"^$ty"
      case Quote(_, tm)      => s"`$tm"
      case Splice(_, tm)     => s"$$$tm"
      case Hole(_, None)     => s"_"
      case Hole(_, Some(x))  => s"_$x"
      case Instr(_, x, args) => s"(instr $x ${args.mkString(" ")})"
