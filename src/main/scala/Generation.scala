import Common.{Name, impossible, RuntimePrimitive}
import JVM.*

import scala.jdk.CollectionConverters.*
import scala.collection.mutable
import java.lang.classfile.*
import java.lang.constant.*
import java.nio.file.Files
import java.nio.file.Path
import java.lang.classfile.attribute.InnerClassInfo
import java.lang.classfile.attribute.InnerClassesAttribute
import java.util.Optional
import java.lang.classfile.constantpool.ConstantValueEntry
import java.lang.classfile.constantpool.ConstantPoolBuilder
import java.lang.classfile.attribute.ConstantValueAttribute

// generate JVM bytecode
object Generation:
  private val Arity0InstanceName = "INSTANCE"

  private final case class ModuleCtx(
      jname: String,
      desc: ClassDesc,
      path: String
  )
  private final case class DatatypeCtx(
      jname: String,
      jinnername: String,
      desc: ClassDesc,
      path: String,
      cons: Set[Name]
  )
  private final case class ConCtx(
      jname: String,
      jinnername: String,
      desc: ClassDesc,
      path: String,
      names: List[String],
      types: List[ClassDesc],
      kinds: List[TypeKind],
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
      val xinner = JName(name)
      val x = s"${modules(currentModule)._1}$$$xinner"
      val d = ClassDesc.of(x)
      val p = s"$targetDir/${x.split("\\.").mkString("/")}.class"
      val cons = cs.map(_.name).toSet
      datatypes(currentModule) += (name -> DatatypeCtx(x, xinner, d, p, cons))
      cs.foreach { case Constructor(_, cx, ps) =>
        val xcinner = JName(cx)
        val jcx = s"$x$$$xcinner"
        val dc = ClassDesc.of(jcx)
        val pc = s"$targetDir/${jcx.split("\\.").mkString("/")}.class"
        val eps = ps.map((_, t) => gen(t)(using this))
        val names = ps.zipWithIndex.map { case ((x, _), i) =>
          x.fold(s"p$i")(JName.apply)
        }
        val types = eps.map(_._2)
        val kinds = eps.map(_._1)
        val initd =
          MethodTypeDesc.of(ConstantDescs.CD_void, types.asJava)
        constructors(currentModule) += ((name, cx) -> ConCtx(
          jcx,
          xcinner,
          dc,
          pc,
          names,
          types,
          kinds,
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

    inline def getModule(mod: Name): ModuleCtx = modules(mod)
    inline def getModule(): ModuleCtx = getModule(currentModule)

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
    // static block
    val modulectx = ctx.getModule()
    classBuilder.withMethodBody(
      ConstantDescs.CLASS_INIT_NAME,
      MethodTypeDesc.of(ConstantDescs.CD_void),
      ClassFile.ACC_PRIVATE | ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
      codeBuilder =>
        ds.foreach {
          case Def.Value(_, x, _, v) if !isConstant(v) =>
            val valctx = ctx.getValue(x)
            gen(v)(using codeBuilder = codeBuilder, env = Map.empty)
            codeBuilder.putstatic(modulectx.desc, valctx.jname, valctx.desc)
          case _ => ()
        }
        codeBuilder.return_()
    )

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
      ctx: Ctx,
      outerClassBuilder: ClassBuilder
  ): Unit =
    val modulectx = ctx.getModule()
    val datactx = ctx.getDatatype(name)
    val bytes = ClassFile
      .of()
      .build(
        datactx.desc,
        classBuilder => {
          val flag = ClassFile.ACC_ABSTRACT | gen(acc)
          classBuilder.withFlags(flag)
          outerClassBuilder.`with`(
            InnerClassesAttribute.of(
              InnerClassInfo.of(
                datactx.desc,
                Optional.of(modulectx.desc),
                Optional.of(datactx.jinnername),
                flag
              )
            )
          )
          val innerClassInfos = cs.map(c => gen(name, c))
          classBuilder.`with`(InnerClassesAttribute.of(innerClassInfos.asJava))
        }
      )
    Files.write(Path.of(datactx.path), bytes)

  private def gen(dx: Name, con: Constructor)(using ctx: Ctx): InnerClassInfo =
    val Constructor(acc, cx, _) = con
    val datactx = ctx.getDatatype(dx)
    val conctx = ctx.getCon(ctx.currentModule, dx, cx)
    val flag = gen(acc)
    val bytes = ClassFile
      .of()
      .build(
        conctx.desc,
        classBuilder => {
          classBuilder.withFlags(flag)
          classBuilder.withSuperclass(datactx.desc)
          // fields
          val ps = conctx.names.zip(conctx.types).zip(conctx.kinds).map {
            case ((x, t), k) => (x, t, k)
          }
          ps.foreach { (px, pty, _) =>
            classBuilder
              .withField(px, pty, ClassFile.ACC_FINAL | ClassFile.ACC_PUBLIC)
          }
          // constructor
          classBuilder.withMethodBody(
            ConstantDescs.INIT_NAME,
            conctx.initdesc,
            flag | ClassFile.ACC_SYNTHETIC,
            codeBuilder =>
              ps.zipWithIndex.foreach { case ((px, pty, pk), ix) =>
                codeBuilder
                  .loadLocal(TypeKind.REFERENCE, codeBuilder.receiverSlot())
                codeBuilder.loadLocal(pk, codeBuilder.parameterSlot(ix))
                codeBuilder.putfield(conctx.desc, px, pty)
              }
              codeBuilder.return_()
          )
          // optimization for arity 0 constructors
          if ps.isEmpty then
            classBuilder.withField(
              Arity0InstanceName,
              conctx.desc,
              ClassFile.ACC_FINAL | ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC
            )
            classBuilder.withMethodBody(
              ConstantDescs.CLASS_INIT_NAME,
              MethodTypeDesc.of(ConstantDescs.CD_void),
              ClassFile.ACC_PRIVATE | ClassFile.ACC_STATIC | ClassFile.ACC_SYNTHETIC,
              codeBuilder =>
                codeBuilder.new_(conctx.desc).dup()
                codeBuilder.invokespecial(
                  conctx.desc,
                  ConstantDescs.INIT_NAME,
                  conctx.initdesc
                )
                codeBuilder
                  .putstatic(conctx.desc, Arity0InstanceName, conctx.desc)
                codeBuilder.return_()
            )
        }
      )
    Files.write(Path.of(conctx.path), bytes)
    InnerClassInfo.of(
      conctx.desc,
      Optional.of(datactx.desc),
      Optional.of(conctx.jinnername),
      flag
    )

  private def gen(acc: Access, name: Name, ty: Ty, value: Tm)(using
      ctx: Ctx,
      classBuilder: ClassBuilder
  ): Unit =
    val valctx = ctx.getValue(name)
    val c = constant(value)(using classBuilder.constantPool())
    classBuilder.withField(
      valctx.jname,
      valctx.desc,
      fieldBuilder =>
        fieldBuilder.withFlags(
          ClassFile.ACC_STATIC | ClassFile.ACC_FINAL | gen(acc)
        )
        c.foreach(v => fieldBuilder.`with`(ConstantValueAttribute.of(v)))
    )

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
          env = env
        )
        codeBuilder.return_(functx.kind)
    )

  private def gen(
      tm: Tm
  )(using
      ctx: Ctx,
      codeBuilder: CodeBuilder,
      env: Env
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
            codeBuilder.loadLocal(k, codeBuilder.parameterSlot(ix))
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
        if conctx.types.isEmpty then
          codeBuilder.getstatic(conctx.desc, Arity0InstanceName, conctx.desc)
        else
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
        val retLabel = codeBuilder.newLabel()
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
          codeBuilder.goto_(retLabel)
        }
        codeBuilder.labelBinding(endLabel)
        gen(b)(using env = nenv)
        codeBuilder.labelBinding(retLabel)

      case Tm.Case(m, dx, s, cs) =>
        gen(s)
        val endLabel = codeBuilder.newLabel()
        gen(m, dx, endLabel, cs)
        codeBuilder.labelBinding(endLabel)

  private def gen(m: Name, dx: Name, endLabel: Label, cs: Cases)(using
      ctx: Ctx,
      codeBuilder: CodeBuilder,
      env: Env
  ): Unit =
    val datactx = ctx.getDatatype(m, dx)
    // TODO: use codeBuilder.block
    cs match
      case Cases.Empty => codeBuilder.pop()
      case Cases.Otherwise(b) =>
        codeBuilder.pop()
        gen(b)
      case Cases.Ext(cx, cps, b, r) =>
        val conctx = ctx.getCon(m, dx, cx)
        val ps =
          cps.zip(conctx.names).zip(conctx.kinds).zip(conctx.types).map {
            case ((((x, _, u), px), k), ty) => (x, px, u, k, ty)
          }
        def genbody(codeBuilder: CodeBuilder): Unit =
          if (ps.nonEmpty) codeBuilder.checkcast(conctx.desc)
          val nenv = ps.foldLeft(env) { case (env, (x, px, u, k, ty)) =>
            if u == 0 then env
            else
              val l = codeBuilder.allocateLocal(k)
              codeBuilder.dup()
              codeBuilder.getfield(conctx.desc, px, ty)
              codeBuilder.storeLocal(k, l)
              env + (x -> EnvEntry.Local(k, l))
          }
          codeBuilder.pop()
          gen(b)(using codeBuilder = codeBuilder, env = nenv)
          codeBuilder.goto_(endLabel)
        if r == Cases.Empty then genbody(codeBuilder)
        else
          codeBuilder.dup()
          if ps.isEmpty then
            codeBuilder.getstatic(conctx.desc, Arity0InstanceName, conctx.desc)
            codeBuilder.ifThenElse(
              Opcode.IF_ACMPEQ,
              codeBuilder => genbody(codeBuilder),
              codeBuilder =>
                gen(m, dx, endLabel, r)(using codeBuilder = codeBuilder)
            )
          else
            codeBuilder.instanceOf(conctx.desc)
            codeBuilder.ifThenElse(
              codeBuilder => genbody(codeBuilder),
              codeBuilder =>
                gen(m, dx, endLabel, r)(using codeBuilder = codeBuilder)
            )

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

  private def isConstant(tm: Tm): Boolean =
    tm match
      case Tm.BoolLit(_) => true
      case Tm.IntLit(_)  => true
      case _             => false

  private def constant(tm: Tm)(using
      pool: ConstantPoolBuilder
  ): Option[ConstantValueEntry] =
    tm match
      case Tm.BoolLit(v) =>
        if v then Some(pool.intEntry(1)) else Some(pool.intEntry(0))
      case Tm.IntLit(v) => Some(pool.intEntry(v))
      case _            => None
