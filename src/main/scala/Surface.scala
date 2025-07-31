import scala.collection.mutable

import Common.*

object Surface:
  type Name = String

  final case class MName(module: Option[Name], name: Name)

  enum Type:
    case Named(name: MName)
    case Jvm(qualifiedName: String)
    case Array(ty: Type)

  final case class TypeDef(params: List[Type], io: Boolean, rty: Type)

  type CaseItem = (Option[Name], List[Name], Expr)

  enum Expr:
    case Var(name: MName)
    case Lam(name: Name, body: Expr)
    case App(fn: Expr, arg: Expr)
    case Let(name: Name, ty: Option[TypeDef], value: Expr, body: Expr)
    case LetRec(name: Name, ty: TypeDef, value: Expr, body: Expr)

    case IntLit(value: Int)

    case If(scrut: Expr, ifTrue: Expr, ifFalse: Expr)

    case Instr(instr: String, args: List[Expr])

    case Con(datatype: Option[MName], name: Name, args: List[Expr])
    case RecordCon(dx: Option[MName], args: List[Expr])

    case Field(scrut: Expr, ix: Either[Name, Int])
    case Case(scrut: Expr, cases: List[CaseItem])

    case FiniteCon(datatype: Option[MName], name: Name)
    case FiniteCase(scrut: Expr, cases: List[(Option[Name], Expr)])

    case ReturnIO(expr: Expr)
    case BindIO(name: Name, value: Expr, body: Expr)

  final case class Constructor(
      name: Name,
      parameters: List[(Option[Name], Type)]
  )

  enum Def:
    case Value(name: Name, ty: Option[TypeDef], value: Expr)
    case Data(name: Name, constructors: List[Constructor])
    case Record(name: Name, fields: List[(Option[Name], Type)])
    case Finite(name: Name, constructors: List[Name])

  final case class Module(
      name: Name,
      deps: Set[Name],
      imports: Map[Name, (Name, Option[Name])],
      renames: Map[Name, Name],
      defs: List[Def]
  )

  // elaboration
  private enum DataKind:
    case ADT
    case Record
    case Finite

  private final case class LocalCtx(env: List[(Name, IR.TypeDef)] = Nil):
    def bind(x: Name, ty: IR.TypeDef): LocalCtx = copy(env = (x, ty) :: env)

  private type DataParams = Map[Name, List[IR.Type]]
  private type RecordParams = List[(Option[Name], IR.Type)]
  private type FiniteParams = List[Name]

  private final case class ModuleCtx(
      name: Name,
      private val modules: mutable.Map[Name, Name] = mutable.Map.empty,
      private val imports: mutable.Map[Name, IR.MName] = mutable.Map.empty,
      private val globals: mutable.Map[Name, IR.TypeDef] = mutable.Map.empty,
      private val types: mutable.Map[Name, DataKind] = mutable.Map.empty,
      private val recordparams: mutable.Map[Name, RecordParams] =
        mutable.Map.empty,
      private val dataparams: mutable.Map[Name, DataParams] = mutable.Map.empty,
      private val finiteparams: mutable.Map[Name, FiniteParams] =
        mutable.Map.empty
  ):
    def addModule(globalName: Name, innerName: Name): Unit =
      modules += innerName -> globalName

    def addGlobal(x: Name, ty: IR.TypeDef): Unit =
      globals += x -> ty
    def addType(x: Name, kind: DataKind): Unit =
      types += x -> kind
    def addRecordParams(x: Name, ps: List[(Option[Name], IR.Type)]): Unit =
      recordparams += x -> ps
    def addDataParams(x: Name, ps: Map[Name, List[IR.Type]]): Unit =
      dataparams += x -> ps
    def addFiniteParams(x: Name, ps: List[Name]): Unit =
      finiteparams += x -> ps
    def addImport(m: Name, x: Name, r: Name): Unit =
      imports += r -> IR.MName(m, x)

    def hasName(x: Name): Boolean = globals.contains(x) || types.contains(x)

    private def datakind(x: Name): DataKind =
      types.get(x) match
        case None    => err(s"undefined type $name.$x")
        case Some(k) => k
    def dataparam(x: Name): DataParams =
      dataparams.get(x) match
        case None     => err(s"undefined data type $name.$x")
        case Some(ps) => ps
    def recordparam(x: Name): RecordParams =
      recordparams.get(x) match
        case None     => err(s"undefined record type $name.$x")
        case Some(ps) => ps
    def finiteparam(x: Name): FiniteParams =
      finiteparams.get(x) match
        case None     => err(s"undefined finite type $name.$x")
        case Some(ps) => ps

    private def module(x: Name)(using ctx: Ctx): ModuleCtx =
      modules.get(x) match
        case None    => err(s"undefined module $x")
        case Some(y) => ctx.module(y)

    private def transform(mx: MName)(using ctx: Ctx): (ModuleCtx, Name) =
      mx match
        case MName(Some(m), x) => (module(m), x)
        case MName(None, x)    =>
          val target = imports.getOrElse(x, IR.MName(name, x))
          (ctx.module(target.module), target.name)

    def global(mx: MName)(using ctx: Ctx): (IR.MName, IR.TypeDef) =
      val (mctx, x) = transform(mx)
      mctx.global(x)
    def global(x: Name)(using ctx: Ctx): (IR.MName, IR.TypeDef) =
      globals.get(x) match
        case Some(ty) => (IR.MName(name, x), ty)
        case None     =>
          imports.get(x) match
            case Some(x) => ctx.global(x.module, x.name)
            case None    => err(s"undefined variable $name.$x")

    def datakind(mx: MName)(using ctx: Ctx): (IR.MName, DataKind) =
      val (mctx, x) = transform(mx)
      (IR.MName(mctx.name, x), mctx.datakind(x))
    def dataparam(mx: MName)(using ctx: Ctx): (IR.MName, DataParams) =
      val (mctx, x) = transform(mx)
      (IR.MName(mctx.name, x), mctx.dataparam(x))
    def recordparam(mx: MName)(using ctx: Ctx): (IR.MName, RecordParams) =
      val (mctx, x) = transform(mx)
      (IR.MName(mctx.name, x), mctx.recordparam(x))
    def finiteparam(mx: MName)(using ctx: Ctx): (IR.MName, FiniteParams) =
      val (mctx, x) = transform(mx)
      (IR.MName(mctx.name, x), mctx.finiteparam(x))

  private final case class Ctx(
      private val modules: mutable.Map[Name, ModuleCtx] = mutable.Map.empty
  ):
    def addModule(m: Name): ModuleCtx =
      val mctx = ModuleCtx(m)
      modules += m -> mctx
      mctx

    def module(name: Name): ModuleCtx = modules(name)

    def moduleOption(name: Name): Option[ModuleCtx] = modules.get(name)

    def data(name: IR.MName): DataParams =
      module(name.module).dataparam(name.name)
    def record(name: IR.MName): RecordParams =
      module(name.module).recordparam(name.name)
    def finite(name: IR.MName): FiniteParams =
      module(name.module).finiteparam(name.name)

    def global(m: Name, x: Name): (IR.MName, IR.TypeDef) =
      modules.get(m) match
        case Some(mod) => mod.global(x)(using this)
        case None      =>
          err(s"undefined module $m, while looking for variable $m.$x")

  def elaborate(mods: List[Module]): List[IR.Module] =
    given ctx: Ctx = Ctx()
    mods.map(elaborate)

  private def elaborate(mod: Module)(using ctx: Ctx): IR.Module =
    given moduleCtx: ModuleCtx = ctx.addModule(mod.name)
    moduleCtx.addModule(mod.name, mod.name)
    mod.renames.foreach((m, r) => moduleCtx.addModule(m, r))
    mod.imports.foreach { case (x, (m, r)) =>
      ctx.moduleOption(m) match
        case None => err(s"undefined module $m in imports")
        case Some(mod) if !mod.hasName(x) =>
          err(s"undefined name $m.$x in imports")
        case _ => moduleCtx.addImport(m, x, r.getOrElse(x))
    }
    val ds = mod.defs.map(elaborate)
    IR.Module(mod.name, ds)

  private def elaborate(
      defn: Def
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.Def =
    defn match
      case Def.Value(x, ty, value) =>
        given localCtx: LocalCtx = LocalCtx()
        val (evalue, ety) = inferValue(ty, value)
        moduleCtx.addGlobal(x, ety)
        IR.Def.Value(x, ety, evalue)
      case Def.Data(x, cons) =>
        moduleCtx.addType(x, DataKind.ADT)
        val econs = cons.map { case Constructor(x, params) =>
          IR.Constructor(x, params.map((x, t) => (x, elaborate(t))))
        }
        moduleCtx.addDataParams(
          x,
          econs.map(c => (c.name, c.parameters.map(_._2))).toMap
        )
        IR.Def.Data(x, econs)
      case Def.Record(x, fields) =>
        moduleCtx.addType(x, DataKind.Record)
        val efields = fields.map((x, t) => (x, elaborate(t)))
        moduleCtx.addRecordParams(x, efields)
        IR.Def.Record(x, efields)
      case Def.Finite(x, cs) =>
        moduleCtx.addType(x, DataKind.Finite)
        moduleCtx.addFiniteParams(x, cs)
        IR.Def.Finite(x, cs.size)

  private def elaborate(
      ty: TypeDef
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.TypeDef =
    IR.TypeDef(ty.params.map(elaborate), ty.io, elaborate(ty.rty))

  private def elaborate(
      ty: Type
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.Type =
    ty match
      case Type.Jvm(x)                       => IR.Type.Jvm(x)
      case Type.Array(ty)                    => IR.Type.Array(elaborate(ty))
      case Type.Named(MName(None, "Byte"))   => IR.Type.Byte
      case Type.Named(MName(None, "Char"))   => IR.Type.Char
      case Type.Named(MName(None, "Short"))  => IR.Type.Short
      case Type.Named(MName(None, "Int"))    => IR.Type.Int
      case Type.Named(MName(None, "Long"))   => IR.Type.Long
      case Type.Named(MName(None, "Float"))  => IR.Type.Float
      case Type.Named(MName(None, "Double")) => IR.Type.Double
      case Type.Named(x)                     =>
        moduleCtx.datakind(x) match
          case (tyName, DataKind.ADT)    => IR.Type.Data(tyName)
          case (tyName, DataKind.Record) => IR.Type.Record(tyName)
          case (tyName, DataKind.Finite) => IR.Type.Finite(tyName)

  private def inferValue(ty: Option[TypeDef], value: Expr)(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): (IR.Expr, IR.TypeDef) =
    ty match
      case None     => infer(value)
      case Some(ty) =>
        val ety = elaborate(ty)
        (check(value, ety), ety)

  private def check(expr: Expr, exty: IR.TypeDef)(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): IR.Expr =
    expr match
      case Expr.Lam(x, body) =>
        exty match
          case IR.TypeDef(pty :: _, _, _) =>
            val ebody =
              check(body, exty.tail)(using
                localCtx = localCtx.bind(x, IR.TypeDef(pty))
              )
            IR.Expr.Lam(pty, ebody)
          case _ => err(s"cannot check lambda against $exty")

      case Expr.Let(x, ty, value, body) =>
        val (evalue, ety) = inferValue(ty, value)
        val ebody = check(body, exty)(using localCtx = localCtx.bind(x, ety))
        IR.Expr.Let(ety, evalue, ebody)
      case Expr.LetRec(x, ty, value, body) =>
        val ety = elaborate(ty)
        val evalue = check(value, ety)(using localCtx = localCtx.bind(x, ety))
        val ebody = check(body, exty)(using localCtx = localCtx.bind(x, ety))
        IR.Expr.LetRec(ety, evalue, ebody)

      case Expr.If(c, t, f) =>
        val (ec, bty) = inferIfScrut(c)
        val et = check(t, exty)
        val ef = check(f, exty)
        IR.Expr.FiniteCase(exty, bty, ec, List((1, et), (0, ef)), None)

      case Expr.Instr(instr, args) =>
        val rt = exty match
          case IR.TypeDef(Nil, _, rt) => rt
          case ty                     =>
            err(
              s"instr can only be checked against a value type or a value type in IO but got $ty"
            )
        val (eargs, ts) = args.map { a =>
          val (ea, ty) = infer(a)
          ty match
            case IR.TypeDef(Nil, false, t) =>
              (ea, t)
            case ty =>
              err(s"instr arguments have to be value types, but got $ty")
        }.unzip
        IR.Expr.Instr(instr, ts, rt, eargs)

      case Expr.Con(None, cx, args) =>
        exty match
          case IR.TypeDef(Nil, _, IR.Type.Data(dx)) => inferCon(dx, cx, args)
          case _                                    =>
            err(
              s"cannot check data constructor against $exty"
            )
      case Expr.RecordCon(None, args) =>
        exty match
          case IR.TypeDef(Nil, _, IR.Type.Record(x)) => inferRecordCon(x, args)
          case _                                     =>
            err(
              s"cannot check record constructor against $exty"
            )
      case Expr.FiniteCon(None, cx) =>
        exty match
          case IR.TypeDef(Nil, _, IR.Type.Finite(dx)) =>
            ctx.finite(dx).zipWithIndex.find((cx2, _) => cx == cx2) match
              case None =>
                err(s"undefined finite constructor $cx in $dx")
              case Some((_, i)) => IR.Expr.FiniteCon(dx, i)
          case _ =>
            err(
              s"cannot check finite constructor against $exty"
            )

      case Expr.Case(scrut, cases) => inferCase(scrut, cases, Some(exty))._1
      case Expr.FiniteCase(scrut, cases) =>
        inferFinCase(scrut, cases, Some(exty))._1

      case Expr.ReturnIO(v) =>
        exty match
          case IR.TypeDef(Nil, true, ty) =>
            check(v, IR.TypeDef(Nil, false, ty))
          case _ =>
            err(s"cannot check returnIO against $exty")
      case Expr.BindIO(x, value, body) =>
        exty match
          case IR.TypeDef(Nil, true, _) =>
            val (evalue, ety) = infer(value)
            ety match
              case IR.TypeDef(Nil, true, ty) =>
                val ebody =
                  check(body, exty)(using
                    localCtx = localCtx.bind(x, IR.TypeDef(ty))
                  )
                IR.Expr.BindIO(ty, evalue, ebody)
              case _ => err(s"invalid type in bindIO: $ety")
          case _ => err(s"cannot match bindIO against type: $exty")

      case expr =>
        val (ie, ity) = infer(expr)
        if ity == exty then ie
        else err(s"type mismatch: expected $exty, but got $ity")

  private def infer(expr: Expr)(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): (IR.Expr, IR.TypeDef) =
    expr match
      case Expr.IntLit(value) =>
        (IR.Expr.IntLit(value), IR.TypeDef(IR.Type.Int))

      case Expr.Var(x) =>
        inline def findGlobal(x: MName): (IR.Expr, IR.TypeDef) =
          val (ex, ty) = moduleCtx.global(x)
          (IR.Expr.Global(ex), ty)
        x.module match
          case None =>
            localCtx.env.zipWithIndex.find { case ((y, _), _) =>
              x.name == y
            } match
              case None                => findGlobal(x)
              case Some(((_, ty), ix)) => (IR.Expr.Local(ix, ty), ty)
          case Some(_) => findGlobal(x)

      case Expr.Lam(_, _) => err("cannot infer lambda")

      case Expr.App(fn, arg) =>
        val (efn, ty) = infer(fn)
        ty match
          case IR.TypeDef(pty :: _, _, _) =>
            val earg = check(arg, IR.TypeDef(pty))
            (IR.Expr.App(efn, earg), ty.tail)
          case _ =>
            err(
              s"expected function type in application but got $ty"
            )

      case Expr.Let(x, ty, value, body) =>
        val (evalue, ety) = inferValue(ty, value)
        val (ebody, rty) = infer(body)(using localCtx = localCtx.bind(x, ety))
        (IR.Expr.Let(ety, evalue, ebody), rty)

      case Expr.LetRec(x, ty, value, body) =>
        val ety = elaborate(ty)
        val evalue = check(value, ety)(using localCtx = localCtx.bind(x, ety))
        val (ebody, rty) = infer(body)(using localCtx = localCtx.bind(x, ety))
        (IR.Expr.LetRec(ety, evalue, ebody), rty)

      case Expr.If(c, t, f) =>
        val (ec, bty) = inferIfScrut(c)
        val (et, ety) = infer(t)
        val ef = check(f, ety)
        (IR.Expr.FiniteCase(ety, bty, ec, List((1, et), (0, ef)), None), ety)

      case Expr.Instr(n, _) =>
        err(s"cannot infer instruction $n")

      case Expr.Con(None, cx, _) =>
        err(s"cannot infer con $cx without datatype")
      case Expr.Con(Some(dx), cx, args) =>
        val edx = inferData(dx)
        (inferCon(edx, cx, args), IR.TypeDef(IR.Type.Data(edx)))

      case Expr.RecordCon(None, _) =>
        err(
          "cannot infer record constructor without record type"
        )
      case Expr.RecordCon(Some(x), args) =>
        val dx = inferRecord(x)
        (inferRecordCon(dx, args), IR.TypeDef(IR.Type.Record(dx)))

      case Expr.FiniteCon(None, cx) =>
        err(s"cannot infer finite con $cx without datatype")
      case Expr.FiniteCon(Some(dx), cx) =>
        val edx = inferFinite(dx)
        ctx.finite(edx).zipWithIndex.find((cx2, _) => cx == cx2) match
          case None =>
            err(s"undefined finite constructor $cx in $dx")
          case Some((_, i)) =>
            (IR.Expr.FiniteCon(edx, i), IR.TypeDef(IR.Type.Finite(edx)))

      case Expr.Field(scrut, ix) =>
        val (escrut, scrutty) = infer(scrut)
        scrutty match
          case IR.TypeDef(Nil, false, IR.Type.Record(x)) =>
            val ps = ctx.record(x)
            val i = ix match
              case Left(px) =>
                ps.zipWithIndex.find {
                  case ((Some(y), _), _) if px == y => true
                  case _                            => false
                } match
                  case Some((_, i)) => i
                  case None         => err(s"field $px not found in $x")
              case Right(i) =>
                if i < 0 || i > ps.size then
                  err(s"field index out of range: $i")
                else i
            (IR.Expr.Field(x, escrut, i), IR.TypeDef(ps(i)._2))
          case _ =>
            err(
              s"expected record type in field but got $scrutty"
            )

      case Expr.Case(scrut, cases)       => inferCase(scrut, cases, None)
      case Expr.FiniteCase(scrut, cases) => inferFinCase(scrut, cases, None)

      case Expr.ReturnIO(v) =>
        val (ev, ty) = infer(v)
        if ty.params.nonEmpty || ty.io then
          err(s"can only call returnIO on value types: $ty")
        (IR.Expr.ReturnIO(ev), IR.TypeDef(Nil, true, ty.returnty))
      case Expr.BindIO(x, value, body) =>
        val (evalue, ety) = infer(value)
        ety match
          case IR.TypeDef(Nil, true, ty) =>
            val (ebody, rty) =
              infer(body)(using localCtx = localCtx.bind(x, IR.TypeDef(ty)))
            rty match
              case IR.TypeDef(Nil, true, _) =>
                (IR.Expr.BindIO(ty, evalue, ebody), rty)
              case _ => err(s"invalid return type in bindIO: $rty")
          case _ => err(s"invalid type in bindIO: $ety")

  private def inferIfScrut(
      scrut: Expr
  )(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): (IR.Expr, IR.MName) =
    val (escrut, ty) = infer(scrut)
    ty match
      case IR.TypeDef(Nil, false, IR.Type.Finite(x))
          if ctx.finite(x).size == 2 =>
        (escrut, x)
      case _ =>
        err(
          s"Expected finite type with two elements in if expression but got $ty"
        )

  private def inferFinite(
      x: MName
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.MName =
    moduleCtx.finiteparam(x)._1
  private def inferRecord(
      x: MName
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.MName =
    moduleCtx.recordparam(x)._1
  private def inferData(
      x: MName
  )(using ctx: Ctx, moduleCtx: ModuleCtx): IR.MName =
    moduleCtx.dataparam(x)._1

  private def inferRecordCon(x: IR.MName, args: List[Expr])(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): IR.Expr =
    val ps = ctx.record(x)
    val eargs =
      args.zip(ps).map { case (e, (_, t)) => check(e, IR.TypeDef(t)) }
    IR.Expr.RecordCon(x, eargs)

  private def inferCon(dx: IR.MName, cx: Name, args: List[Expr])(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): IR.Expr =
    val cs = ctx.data(dx)
    cs.get(cx) match
      case None =>
        err(
          s"undefined constructor $cx in data type $dx"
        )
      case Some(ps) =>
        val eargs = args.zip(ps).map((e, t) => check(e, IR.TypeDef(t)))
        IR.Expr.Con(dx, cx, eargs)

  private def inferCase(
      scrut: Expr,
      cases: List[(Option[Name], List[Name], Expr)],
      exty: Option[IR.TypeDef]
  )(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): (IR.Expr, IR.TypeDef) =
    val (escrut, scrutty) = infer(scrut)
    scrutty match
      case IR.TypeDef(Nil, false, IR.Type.Data(dx)) =>
        val datactx = ctx.data(dx)
        var rty: Option[IR.TypeDef] = exty
        val left = mutable.Set.from(datactx.keySet)
        val seen: mutable.Set[Name] = mutable.Set.empty
        val ecases = cases.zipWithIndex.map { case ((cx, ps, b), i) =>
          val last = i == cases.size - 1
          cx match
            case Some(cx) if seen.contains(cx) =>
              err(s"duplicate case $cx")
            case Some(cx) if !left.contains(cx) =>
              err(s"invalid case $cx for type $dx")
            case Some(cx) if last && (left.toSet - cx).nonEmpty =>
              err(
                s"non-exhaustive case: ${(left.toSet - cx).mkString(", ")}"
              )
            case None if left.isEmpty =>
              err(s"otherwise case matches against nothing")
            case None if !last =>
              err(s"otherwise case should be last")

            case scx @ Some(cx) =>
              seen += cx
              left -= cx
              val types = datactx(cx)
              if types.size != ps.size then
                err("parameter size mismatch in case")
              val localctx =
                ps.zip(types).foldLeft(localCtx) { case (ctx, (x, ty)) =>
                  ctx.bind(x, IR.TypeDef(ty))
                }
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)(using localCtx = localctx)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)(using localCtx = localctx)
              val wrappedBody =
                types.zipWithIndex.foldRight(ebody.shift(types.size, 1)) {
                  case ((t, i), b) =>
                    val s = IR.Expr.Local(i, IR.TypeDef(IR.Type.Data(dx)))
                    IR.Expr.Let(
                      IR.TypeDef(t),
                      IR.Expr.DataField(dx, cx, s, i),
                      b
                    )
                }
              (scx, wrappedBody)

            case None =>
              if ps.nonEmpty then err("otherwise case cannot have parameters")
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)
              (None, ebody)
        }
        rty match
          case None =>
            err("could not figure out return type of case")
          case Some(rty) =>
            val (ecs, other) = ecases.last match
              case (None, b) => (ecases.init, Some(b))
              case _         => (ecases, None)
            (
              IR.Expr.Case(
                rty,
                dx,
                escrut,
                ecs.map((x, b) => (x.get, b)),
                other
              ),
              rty
            )
      case _ =>
        err(
          s"expected data type in case but got $scrutty"
        )

  private def inferFinCase(
      scrut: Expr,
      cases: List[(Option[Name], Expr)],
      exty: Option[IR.TypeDef]
  )(using
      ctx: Ctx,
      moduleCtx: ModuleCtx,
      localCtx: LocalCtx
  ): (IR.Expr, IR.TypeDef) =
    val (escrut, scrutty) = infer(scrut)
    scrutty match
      case IR.TypeDef(Nil, false, IR.Type.Finite(dx)) =>
        val datactx = ctx.finite(dx)
        var rty: Option[IR.TypeDef] = exty
        val left = mutable.Set.from(datactx.toSet)
        val seen: mutable.Set[Name] = mutable.Set.empty
        val ecases = cases.zipWithIndex.map { case ((cx, b), i) =>
          val last = i == cases.size - 1
          cx match
            case Some(cx) if seen.contains(cx) =>
              err(s"duplicate case $cx")
            case Some(cx) if !left.contains(cx) =>
              err(s"invalid case $cx for type $dx")
            case Some(cx) if last && (left.toSet - cx).nonEmpty =>
              err(
                s"non-exhaustive case: ${(left.toSet - cx).mkString(", ")}"
              )
            case None if left.isEmpty =>
              err(s"otherwise case matches against nothing")
            case None if !last =>
              err(s"otherwise case should be last")

            case Some(cx) =>
              seen += cx
              left -= cx
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)
              val i = datactx.zipWithIndex.find((x, _) => x == cx).get._2
              (Some(i), ebody)

            case None =>
              val ebody = rty match
                case None =>
                  val (ebody, ty) = infer(b)
                  rty = Some(ty)
                  ebody
                case Some(ty) => check(b, ty)
              (None, ebody)
        }
        rty match
          case None =>
            err("could not figure out return type of case")
          case Some(rty) =>
            val (ecs, other) = ecases.last match
              case (None, b) => (ecases.init, Some(b))
              case _         => (ecases, None)
            (
              IR.Expr.FiniteCase(
                rty,
                dx,
                escrut,
                ecs.map((x, b) => (x.get, b)),
                other
              ),
              rty
            )
      case _ =>
        err(
          s"expected data type in fincase but got $scrutty"
        )
