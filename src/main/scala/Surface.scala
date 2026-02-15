import Common.*
import Common.Icit.*

object Surface:
  final case class Module(
      pos: PosInfo,
      name: Name,
      deps: Set[Name],
      imports: List[(PosInfo, PosInfo, Boolean, Name, Name, Option[Name])],
      moduleAliases: Map[Name, Name],
      defs: Defs
  ):
    override def toString: String =
      s"module $name\n$defs"

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    inline def toList: List[Def] = defs

  final case class Constructor(
      pos: PosInfo,
      pub: Boolean,
      name: Name,
      params: List[(Bind, PiIcit, Ty)]
  ):
    override def toString: String =
      params match
        case Nil => s"${if pub then "" else "priv "}$name"
        case _ =>
          val ps = params
            .map((x, i, t) => i.wrap(s"$x : $t"))
            .mkString(" ")
          s"${if pub then "" else "priv "}$name $ps"

  enum Def:
    case Def0(
        _pos: PosInfo,
        pub: Boolean,
        name: Name,
        ty: Option[Ty],
        value: Tm
    )
    case Def1(
        _pos: PosInfo,
        pub: Boolean,
        auto: Boolean,
        name: Name,
        ty: Option[Ty],
        value: Tm
    )
    case Data(
        _pos: PosInfo,
        pub: Boolean,
        meta: Option[Boolean],
        name: Name,
        params: List[(Name, Icit, Ty)],
        univ: Option[Ty],
        cons: List[Constructor]
    )
    case DeclareData(
        _pos: PosInfo,
        name: Name,
        ty: Ty
    )
    case Variable(_pos: PosInfo, vars: List[(PosInfo, Name, PiIcit, Ty)])

    override def toString: String = this match
      case Def0(_, p, x, t, v) =>
        s"${if p then "public " else ""}def $x${t.map(t => s" : $t").getOrElse("")} := $v"
      case Def1(_, p, a, x, t, v) =>
        s"${if p then "pub " else ""}${if p then "auto " else ""}def $x${t.map(t => s" : $t").getOrElse("")} = $v"
      case Data(_, p, meta, x, ps, u, cs) =>
        val css = cs.mkString(" | ")
        val ustr = u.fold("")(t => s" : $t")
        val df = meta.fold("|")(m => if m then "=" else ":=")
        s"${if p then "pub " else ""}data $x ${ps.map((x, i, ty) => i.wrap(s"$x : $ty")).mkString(" ")}$ustr $df $css"
      case DeclareData(_, x, t) => s"declare data $x : $t"
      case Variable(_, vs) =>
        vs.map((_, x, i, t) => i.wrap(s"$x : $t")).mkString(" ")

    def pos: PosInfo = this match
      case Def0(p, _, _, _, _)       => p
      case Def1(p, _, _, _, _, _)    => p
      case Data(p, _, _, _, _, _, _) => p
      case DeclareData(p, _, _)      => p
      case Variable(p, _)            => p

  enum ImplMode derives CanEqual:
    case Unif
    case Default(tm: Tm)
    case Auto

    override def toString: String = this match
      case Unif        => ""
      case Default(tm) => s"default $tm "
      case Auto        => "auto "

  enum PiIcit derives CanEqual:
    case Expl
    case Impl(mode: ImplMode)

    def wrap(x: Any): String = this match
      case Expl    => s"($x)"
      case Impl(m) => s"{$m$x}"

    def wrapI(x: Any): String = this match
      case Expl    => s"$x"
      case Impl(m) => s"{$m$x}"

    def toIcit: Icit = this match
      case Expl    => Icit.Expl
      case Impl(_) => Icit.Impl

    def isImpl: Boolean = this match
      case Expl    => false
      case Impl(_) => true

  object PiIcit:
    val ImplU = Impl(ImplMode.Unif)
    val ImplA = Impl(ImplMode.Auto)
    inline def ImplD(tm: Tm) = Impl(ImplMode.Default(tm))

    def apply(i: Common.Icit): PiIcit = i match
      case Common.Icit.Expl => PiIcit.Expl
      case Common.Icit.Impl => PiIcit.ImplU

  enum ArgInfo[I] derives CanEqual:
    case Named(name: Name)
    case Icit(icit: I)
  object ArgInfo:
    val Expl = Icit(Common.Icit.Expl)
    val Impl = Icit(Common.Icit.Impl)
    val PiExpl = Icit(PiIcit.Expl)
    val PiImplU = Icit(PiIcit.ImplU)
    val PiImplA = Icit(PiIcit.ImplA)
    inline def PiImplD(tm: Tm) = Icit(PiIcit.ImplD(tm))

  enum ProjType:
    case Named(name: Name)
    case Indexed(ix: Int)

    override def toString: String = this match
      case Named(x)    => x.toString
      case Indexed(ix) => ix.toString

  final case class Case(
      pos: PosInfo,
      con: Bind,
      params: List[(Bind, Icit)],
      body: Tm
  ):
    override def toString: String =
      params match
        case Nil => s"$con => $body"
        case ps =>
          inline def showP(p: (Bind, Icit)): String = p._2.wrapI(p._1)
          s"$con ${ps.map(showP).mkString(" ")} => $body"

  type Ty = Tm
  enum Tm:
    case Var(_pos: PosInfo, name: Name)
    case Prim(_pos: PosInfo, prim: Primitive)

    case IntLit(_pos: PosInfo, value: Int)
    case StringLit(_pos: PosInfo, value: String)

    case Let0(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)
    case Let1(
        _pos: PosInfo,
        auto: Boolean,
        name: Name,
        ty: Option[Ty],
        value: Tm,
        body: Tm
    )
    case LetRec(_pos: PosInfo, name: Name, ty: Option[Ty], value: Tm, body: Tm)

    case Proj(_pos: PosInfo, tm: Tm, proj: ProjType)

    case Pi(_pos: PosInfo, name: Bind, icit: PiIcit, ty: Ty, body: Ty)
    case Lam(
        _pos: PosInfo,
        name: Bind,
        info: ArgInfo[PiIcit],
        ty: Option[Ty],
        body: Tm
    )
    case App(_pos: PosInfo, fn: Tm, arg: Tm, info: ArgInfo[Icit])

    case Lift(_pos: PosInfo, ty: Ty)
    case Quote(_pos: PosInfo, tm: Tm)
    case Splice(_pos: PosInfo, tm: Tm)

    case If(_pos: PosInfo, cond: Tm, ifTrue: Tm, ifFalse: Tm)
    case Match(
        _pos: PosInfo,
        scrut: Option[Tm],
        ty: Option[(Bind, Ty)],
        cases: List[Case]
    )

    case UnitLit(_pos: PosInfo)
    case EmptyRecord(_pos: PosInfo)
    case RecordTy(_pos: PosInfo, fields: AssocBind[Ty])
    case RecordCon1(_pos: PosInfo, fields: Assoc[Tm])
    case RecordCon0(_pos: PosInfo, fields: Assoc[Tm])
    case Tuple(_pos: PosInfo, fields: List[Tm])

    case Unsafe(_pos: PosInfo, io: Boolean, label: Tm, args: List[Tm])

    case Hole(_pos: PosInfo, name: Option[Name])

    def pos: PosInfo = this match
      case Var(_pos, _)              => _pos
      case Prim(_pos, _)             => _pos
      case IntLit(_pos, _)           => _pos
      case StringLit(_pos, _)        => _pos
      case Proj(_pos, _, _)          => _pos
      case Let0(_pos, _, _, _, _)    => _pos
      case Let1(_pos, _, _, _, _, _) => _pos
      case LetRec(_pos, _, _, _, _)  => _pos
      case Pi(_pos, _, _, _, _)      => _pos
      case Lam(_pos, _, _, _, _)     => _pos
      case App(_pos, _, _, _)        => _pos
      case Lift(_pos, _)             => _pos
      case Quote(_pos, _)            => _pos
      case Splice(_pos, _)           => _pos
      case If(_pos, _, _, _)         => _pos
      case Match(_pos, _, _, _)      => _pos
      case Hole(_pos, _)             => _pos
      case UnitLit(_pos)             => _pos
      case EmptyRecord(_pos)         => _pos
      case RecordTy(_pos, _)         => _pos
      case RecordCon1(_pos, _)       => _pos
      case RecordCon0(_pos, _)       => _pos
      case Tuple(_pos, _)            => _pos
      case Unsafe(_pos, _, _, _)     => _pos

    def splitProjs: (Tm, List[(PosInfo, ProjType)]) = this match
      case Proj(pos, tm, proj) =>
        val (hd, tl) = tm.splitProjs
        (hd, tl :+ (pos, proj))
      case tm => (tm, Nil)

    override def toString: String = this match
      case Var(_, x)       => s"$x"
      case Prim(_, p)      => s"$p"
      case IntLit(_, v)    => s"$v"
      case StringLit(_, v) => s"\"$v\""
      case Proj(_, t, p)   => s"$t.$p"
      case Let0(_, x, ty, v, b) =>
        s"(let $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Let1(_, auto, x, ty, v, b) =>
        val a = if auto then s"auto " else ""
        s"(let $a$x${ty.map(t => s" : $t").getOrElse("")} = $v; $b)"
      case LetRec(_, x, ty, v, b) =>
        s"(let rec $x${ty.map(t => s" : $t").getOrElse("")} := $v; $b)"
      case Pi(_, Bind.DontBind, PiIcit.Expl, ty, b) => s"($ty -> $b)"
      case Pi(_, x, i, ty, b) => s"(${i.wrap(s"$x : $ty")} -> $b)"
      case Lam(_, x, ArgInfo.Icit(PiIcit.Expl), None, b) => s"(\\$x => $b)"
      case Lam(_, x, ArgInfo.Icit(i), ty, b) =>
        s"(\\${i.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")}")} => $b)"
      case Lam(_, x, ArgInfo.Named(y), ty, b) =>
        s"(\\${Impl.wrap(s"$x${ty.map(t => s" : $t").getOrElse("")} = $y")} => $b)"
      case App(_, fn, arg, ArgInfo.Icit(Expl)) => s"($fn $arg)"
      case App(_, fn, arg, ArgInfo.Icit(Impl)) => s"($fn ${Impl.wrap(arg)})"
      case App(_, fn, arg, ArgInfo.Named(x)) =>
        s"($fn ${Impl.wrap(s"$x = $arg")})"
      case Lift(_, ty)                           => s"^$ty"
      case Quote(_, tm)                          => s"`$tm"
      case Splice(_, tm)                         => s"$$$tm"
      case If(_, c, t, f)                        => s"(if $c then $t else $f)"
      case Hole(_, None)                         => s"_"
      case Hole(_, Some(x))                      => s"_$x"
      case Match(_, None, _, Nil)                => s"(match {})"
      case Match(_, Some(s), None, Nil)          => s"(match $s {})"
      case Match(_, Some(s), Some((x, ty)), Nil) => s"(match $s : $x => $ty {})"
      case Match(_, s, t, cs) =>
        val ty = t match
          case None          => ""
          case Some((x, ty)) => s" : $x => $ty "
        s"(match ${s.map(t => s"$t ").getOrElse("")}$ty{ ${cs.mkString(" | ")} })"
      case UnitLit(_)     => "()"
      case EmptyRecord(_) => "[]"
      case RecordTy(_, fs) =>
        fs.map((x, t) => s"$x : $t").mkString("[", ", ", "]")
      case RecordCon1(_, fs) =>
        fs.map((x, t) => s"$x = $t").mkString("[", ", ", "]")
      case RecordCon0(_, fs) =>
        fs.map((x, t) => s"$x := $t").mkString("[", ", ", "]")
      case Tuple(_, fs)          => fs.mkString("[", ", ", "]")
      case Unsafe(_, io, l, Nil) => s"(unsafe${if io then "IO" else ""} $l)"
      case Unsafe(_, io, l, args) =>
        s"(unsafe${if io then "IO" else ""} $l ${args.mkString(" ")})"
