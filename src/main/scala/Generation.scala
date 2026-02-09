import Common.{Name, impossible}
import JVM.*

import scala.jdk.CollectionConverters.*
import scala.collection.mutable
import java.lang.classfile.*
import java.lang.constant.*
import java.nio.file.Files
import java.nio.file.Path
import Common.RuntimePrimitive

// generate JVM bytecode
// TODO: 0-arity con optimization
object Generation:
  private final case class ModuleCtx(
      jname: String,
      desc: ClassDesc,
      path: String
  )
  private final case class DatatypeCtx(
      jname: String,
      desc: ClassDesc,
      path: String,
      cons: Set[Name]
  )
  private final case class ConCtx(
      jname: String,
      desc: ClassDesc,
      path: String,
      names: List[String],
      types: List[ClassDesc],
      initdesc: MethodTypeDesc
  )
  private final case class ValueCtx(
      jname: String,
      kind: TypeKind,
      desc: ClassDesc
  )
  private final case class FunctionCtx(
      jname: String,
      pskinds: List[TypeKind],
      kind: TypeKind,
      desc: MethodTypeDesc
  )

  private final case class Ctx(
      targetDir: String,
      var currentModule: Name = null,
      modules: mutable.Map[Name, ModuleCtx] = mutable.Map.empty,
      datatypes: mutable.Map[Name, mutable.Map[Name, DatatypeCtx]] =
        mutable.Map.empty,
      constructors: mutable.Map[Name, mutable.Map[(Name, Name), ConCtx]] =
        mutable.Map.empty,
      functions: mutable.Map[Name, mutable.Map[Name, FunctionCtx]] =
        mutable.Map.empty,
      values: mutable.Map[Name, mutable.Map[Name, ValueCtx]] = mutable.Map.empty
  ):
    def registerModule(name: Name): Unit =
      val x = JName.module(name.expose)
      val d = ClassDesc.of(x)
      val p = s"$targetDir/${x.split("\\.").mkString("/")}.class"
      modules += (name -> ModuleCtx(x, d, p))
      datatypes += (name -> mutable.Map.empty)
      constructors += (name -> mutable.Map.empty)
      functions += (name -> mutable.Map.empty)
      values += (name -> mutable.Map.empty)

    def registerDatatype(name: Name, cs: List[Constructor]): Unit =
      val x = s"${modules(currentModule)._1}$$${JName(name)}"
      val d = ClassDesc.of(x)
      val p = s"$targetDir/${x.split("\\.").mkString("/")}.class"
      val cons = cs.map(_.name).toSet
      datatypes(currentModule) += (name -> DatatypeCtx(x, d, p, cons))
      cs.foreach { case Constructor(_, cx, ps) =>
        val jcx = s"$x$$${JName(cx)}"
        val dc = ClassDesc.of(x)
        val pc = s"$targetDir/${x.split("\\.").mkString("/")}.class"
        val eps = ps.map((_, t) => gen(t)(using this))
        val names = ps.zipWithIndex.map { case ((x, _), i) =>
          x.fold(s"p$i")(JName.apply)
        }
        val types = eps.map(_._2)
        val initd =
          MethodTypeDesc.of(ConstantDescs.CD_void, types.asJava)
        constructors(currentModule) += ((name, cx) -> ConCtx(
          jcx,
          dc,
          pc,
          names,
          types,
          initd
        ))
      }

    inline def getDatatype(mod: Name, name: Name): DatatypeCtx =
      datatypes(mod)(name)
    inline def getDatatype(name: Name): DatatypeCtx =
      getDatatype(currentModule, name)
    inline def getCon(m: Name, dx: Name, cx: Name): ConCtx =
      constructors(m)((dx, cx))

    def registerValue(
        name: Name,
        ty: Ty
    ): Unit =
      val x = JName(name)
      given Ctx = this
      val (k, d) = gen(ty)
      values(currentModule) += (name -> ValueCtx(x, k, d))

    inline def getValue(mod: Name, name: Name): ValueCtx =
      values(mod)(name)
    inline def getValue(name: Name): ValueCtx =
      getValue(currentModule, name)

    def registerFunction(
        name: Name,
        params: List[Ty],
        ty: Ty
    ): Unit =
      val x = JName(name)
      given Ctx = this
      val ps = params.map(gen)
      val (rk, rd) = gen(ty)
      val d = MethodTypeDesc.of(rd, ps.map(_._2).asJava)
      functions(currentModule) += (name -> FunctionCtx(x, ps.map(_._1), rk, d))

    inline def getFunction(mod: Name, name: Name): FunctionCtx =
      functions(mod)(name)
    inline def getFunction(name: Name): FunctionCtx =
      getFunction(currentModule, name)

  private enum EnvEntry:
    case Arg(kind: TypeKind, index: Int)
    case Local(kind: TypeKind, slot: Int)
    case Label(label: java.lang.classfile.Label)

  private type Env = Map[LocalName, EnvEntry]

  def generateBytecode(modules: List[Module], targetDir: String): Unit =
    given ctx: Ctx = Ctx(targetDir)
    modules.foreach(gen)

  private def gen(m: Module)(using ctx: Ctx): Unit =
    ctx.registerModule(m.name)
    ctx.currentModule = m.name
    val moduleCtx = ctx.modules(m.name)
    val bytes = ClassFile
      .of()
      .build(
        moduleCtx.desc,
        classBuilder => {
          classBuilder.withFlags(ClassFile.ACC_PUBLIC)
          gen(m.defs.toList)(using classBuilder = classBuilder)
        }
      )
    Files.write(Path.of(moduleCtx.path), bytes)

  private def gen(
      ds: List[Def]
  )(using ctx: Ctx, classBuilder: ClassBuilder): Unit =
    // register datatypes and functions for mutual recursive definitions
    ds.foreach {
      case Def.Data(_, x, cs) => ctx.registerDatatype(x, cs)
      case _                  => ()
    }
    ds.foreach {
      case Def.Function(_, x, params, retty, _) =>
        ctx.registerFunction(x, params.map(_._2), retty)
      case Def.Value(_, x, ty, _) =>
        ctx.registerValue(x, ty)
      case _ => ()
    }
    // generate classes for datatypes
    ds.foreach {
      case Def.Data(acc, x, cs) => gen(acc, x, cs)
      case _                    => ()
    }
    // generate values and methods
    ds.foreach {
      case Def.Value(acc, x, ty, v)        => gen(acc, x, ty, v)
      case Def.Function(acc, x, ps, ty, b) => gen(acc, x, ps, ty, b)
      case _                               => ()
    }

  private def gen(ty: Ty)(using ctx: Ctx): (TypeKind, ClassDesc) =
    ty match
      case Ty.Bool       => (TypeKind.BOOLEAN, ConstantDescs.CD_boolean)
      case Ty.Int        => (TypeKind.INT, ConstantDescs.CD_int)
      case Ty.Data(m, x) => (TypeKind.REFERENCE, ctx.datatypes(m)(x).desc)

  private def gen(acc: Access): Int =
    acc match
      case Access.Pub   => ClassFile.ACC_PUBLIC
      case Access.Priv  => ClassFile.ACC_PRIVATE
      case Access.Synth => ClassFile.ACC_PRIVATE | ClassFile.ACC_SYNTHETIC

  private def gen(acc: Access, name: Name, cs: List[Constructor])(using
      ctx: Ctx
  ): Unit = ???

  private def gen(acc: Access, name: Name, ty: Ty, value: Tm)(using
      ctx: Ctx
  ): Unit = ???

  private def gen(
      acc: Access,
      name: Name,
      params: List[(LocalName, Ty)],
      ty: Ty,
      body: Tm
  )(using
      ctx: Ctx,
      classBuilder: ClassBuilder
  ): Unit =
    val functx = ctx.getFunction(name)
    classBuilder.withMethodBody(
      functx.jname,
      functx.desc,
      ClassFile.ACC_STATIC | gen(acc),
      codeBuilder =>
        val env = params
          .zip(functx.pskinds)
          .zipWithIndex
          .map { case (((x, ty), k), i) =>
            x -> EnvEntry.Arg(k, i)
          }
          .toMap
        gen(body)(using
          codeBuilder = codeBuilder,
          env = env,
          returnkind = functx.kind
        )
        codeBuilder.return_(functx.kind)
    )

  private def gen(
      tm: Tm
  )(using
      ctx: Ctx,
      codeBuilder: CodeBuilder,
      env: Env,
      returnkind: TypeKind
  ): Unit =
    tm match
      case Tm.BoolLit(true)  => codeBuilder.iconst_1()
      case Tm.BoolLit(false) => codeBuilder.iconst_0()
      case Tm.IntLit(v)      => gen(v)

      case Tm.Local(ix, _) =>
        env(ix) match
          case EnvEntry.Label(_)       => impossible()
          case EnvEntry.Local(k, slot) => codeBuilder.loadLocal(k, slot)
          case EnvEntry.Arg(k, ix) =>
            val slot = codeBuilder.parameterSlot(ix)
            codeBuilder.loadLocal(k, slot)
      case Tm.Jump(ix, args) =>
        env(ix) match
          case EnvEntry.Label(l) =>
            args.foreach(gen)
            codeBuilder.goto_(l)
          case _ => impossible()

      case Tm.Global(m, x) =>
        val modctx = ctx.modules(m)
        val valctx = ctx.getValue(m, x)
        codeBuilder.getstatic(modctx.desc, valctx.jname, valctx.desc)
      case Tm.GlobalApp(m, x, args) =>
        args.foreach(gen)
        val modctx = ctx.modules(m)
        val functx = ctx.getFunction(m, x)
        codeBuilder.invokestatic(modctx.desc, functx.jname, functx.desc)

      case Tm.Let(x, ty, v, b) =>
        val (k, _) = gen(ty)
        val slot = codeBuilder.allocateLocal(k)
        gen(v)
        codeBuilder.storeLocal(k, slot)
        gen(b)(using env = env + (x -> EnvEntry.Local(k, slot)))

      case Tm.If(c, t, f) =>
        gen(c)
        codeBuilder.ifThenElse(
          codeBuilder => gen(t)(using codeBuilder = codeBuilder),
          codeBuilder => gen(f)(using codeBuilder = codeBuilder)
        )

      case Tm.Prim(p, args) =>
        args.foreach(gen)
        p match
          case RuntimePrimitive.Add => codeBuilder.iadd()
          case RuntimePrimitive.Sub => codeBuilder.isub()
          case RuntimePrimitive.Mul => codeBuilder.imul()
          case RuntimePrimitive.Lt =>
            codeBuilder.ifThenElse(
              Opcode.IF_ICMPLT,
              codeBuilder => codeBuilder.iconst_1(),
              codeBuilder => codeBuilder.iconst_0()
            )

      case Tm.Con(m, dx, cx, _, args) =>
        val conctx = ctx.getCon(m, dx, cx)
        codeBuilder.new_(conctx.desc).dup()
        args.foreach(gen)
        codeBuilder.invokespecial(
          conctx.desc,
          ConstantDescs.INIT_NAME,
          conctx.initdesc
        )

      case Tm.Select(m, dx, s, ix) =>
        val cons = ctx.getDatatype(m, dx).cons
        if cons.size != 1 then impossible()
        val conctx = ctx.getCon(m, dx, cons.head)
        gen(s)
        codeBuilder.getfield(conctx.desc, conctx.names(ix), conctx.types(ix))

      case Tm.Join(bs, b) =>
        // TODO: use codeBuilder.block
        val endLabel = codeBuilder.newLabel()
        codeBuilder.goto_(endLabel)
        val (nenv, ls) = bs.foldLeft((env, Map.empty[LocalName, Label])) {
          case ((env, ls), (x, _, _)) =>
            val l = codeBuilder.newLabel()
            (env + (x -> EnvEntry.Label(l)), ls + (x -> l))
        }
        bs.foreach { (x, ps, b) =>
          val l = ls(x)
          codeBuilder.labelBinding(l)
          val innerenv = ps.reverse.foldLeft(nenv) { case (env, (y, ty)) =>
            val (k, _) = gen(ty)
            val slot = codeBuilder.allocateLocal(k)
            codeBuilder.storeLocal(k, slot)
            env + (y -> EnvEntry.Local(k, slot))
          }
          gen(b)(using env = innerenv)
          codeBuilder.return_(returnkind)
        }
        codeBuilder.labelBinding(endLabel)
        gen(b)(using env = nenv)

      case Tm.Case(m, dty, s, cs) => ???

  private def gen(n: Int)(using codeBuilder: CodeBuilder): Unit =
    n match
      case -1                             => codeBuilder.iconst_m1
      case 0                              => codeBuilder.iconst_0
      case 1                              => codeBuilder.iconst_1
      case 2                              => codeBuilder.iconst_2
      case 3                              => codeBuilder.iconst_3
      case 4                              => codeBuilder.iconst_4
      case 5                              => codeBuilder.iconst_5
      case n if n >= -128 && n <= 127     => codeBuilder.bipush(n)
      case n if n >= -32768 && n <= 32767 => codeBuilder.sipush(n)
      case n                              => codeBuilder.ldc(n)
