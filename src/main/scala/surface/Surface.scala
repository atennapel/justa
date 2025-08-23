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
      params: List[(Bind, Ty)]
  ):
    override def toString: String =
      val ps = params
        .map((x, t) => s"($x : $t)")
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
        params: List[Name],
        cons: List[Constructor]
    )
    override def toString: String = this match
      case D0(_, p, x, t, v) =>
        s"${if p then "pub " else ""}def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case D1(_, p, x, t, v) =>
        s"${if p then "pub " else ""}def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case Primitive(_, p, x, t) =>
        s"${if p then "pub " else ""}primitive $x : $t"
      case Data(_, p, x, k, ps, cs) =>
        val css = cs.mkString(" | ")
        s"${if p then "pub " else ""}$k $x ${ps.mkString(" ")} = $css"

  enum ArgInfo:
    case Named(name: Name)
    case Icit(icit: common.Common.Icit)

  enum ProjType:
    case Named(name: Name)
    case Indexed(ix: Int)

    override def toString: String = this match
      case Named(x)    => x.toString
      case Indexed(ix) => ix.toString

  type Ty = Tm
  enum Tm:
    case Var(posInfo: PosInfo, name: Name)
    case IntLit(posInfo: PosInfo, value: Int)
    case Proj(posInfo: PosInfo, tm: Tm, proj: ProjType)

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

    case Match(
        posInfo: PosInfo,
        scrut: Option[Tm],
        cases: List[(PosInfo, Name, List[Bind], Tm)],
        otherwise: Option[(PosInfo, Tm)]
    )
    case If(posInfo: PosInfo, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    case RecordTy(posInfo: PosInfo, fields: Assoc[Ty])
    case RecordCon1(posInfo: PosInfo, fields: Assoc[Tm])
    case RecordCon0(posInfo: PosInfo, fields: Assoc[Tm])
    case Tuple(posInfo: PosInfo, fields: List[Tm])

    def pos: PosInfo = this match
      case Tm.Var(pos, _)             => pos
      case Tm.IntLit(pos, _)          => pos
      case Tm.Proj(pos, _, _)         => pos
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
      case Tm.Match(pos, _, _, _)     => pos
      case Tm.If(pos, _, _, _)        => pos
      case RecordTy(pos, _)           => pos
      case RecordCon1(pos, _)         => pos
      case RecordCon0(pos, _)         => pos
      case Tuple(pos, _)              => pos

    def splitProjs: (Tm, List[(PosInfo, ProjType)]) = this match
      case Proj(pos, tm, proj) =>
        val (hd, tl) = tm.splitProjs
        (hd, tl ++ List((pos, proj)))
      case tm => (tm, Nil)

    override def toString: String = this match
      case Var(_, x)            => s"$x"
      case IntLit(_, v)         => v.toString
      case Proj(_, t, p)        => s"$t.$p"
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
      case Lift(_, ty)                   => s"^$ty"
      case Quote(_, tm)                  => s"`$tm"
      case Splice(_, tm)                 => s"$$$tm"
      case Hole(_, None)                 => s"_"
      case Hole(_, Some(x))              => s"_$x"
      case Instr(_, x, args)             => s"(instr $x ${args.mkString(" ")})"
      case Match(_, s, cs, Some((_, o))) =>
        s"(match ${s.getOrElse("")} { ${cs.map((_, x, ps, b) => s"$x ${ps.mkString(" ")} => $b").mkString(" | ")} | _ => $o })"
      case Match(_, s, cs, None) =>
        s"(match ${s.getOrElse("")} { ${cs.map((_, x, ps, b) => s"$x ${ps.mkString(" ")} => $b").mkString(" | ")} })"
      case If(_, c, a, b)  => s"(if $c then $a else $b)"
      case RecordTy(_, fs) =>
        fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case RecordCon1(_, fs) =>
        fs.map((x, t) => s"$x = $t").mkString("[", ", ", "]")
      case RecordCon0(_, fs) =>
        fs.map((x, t) => s"$x := $t").mkString("[", ", ", "]")
      case Tuple(_, fs) => fs.mkString("[", ", ", "]")
