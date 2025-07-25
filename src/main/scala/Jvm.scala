import org.objectweb.asm.ClassWriter
import org.objectweb.asm.Type as JType
import org.objectweb.asm.Label as JLabel
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.Method
import org.objectweb.asm.commons.GeneratorAdapter

import java.io.BufferedOutputStream
import java.io.FileOutputStream
import scala.collection.mutable
import scala.annotation.tailrec
import Common.*

import java.nio.file.Path

object Jvm:
  import JvmName.{Name, MName}

  type Lvl = Int

  final case class Module(name: Name, defs: List[Def])

  final case class Constructor(
      name: Name,
      parameters: List[(Option[Name], Type)]
  )

  enum Def:
    case Value(name: Name, ty: Type, value: Expr)
    case Function(name: Name, params: List[Type], returnType: Type, body: Expr)
    case Data(name: Name, constructors: List[Constructor])
    case Record(name: Name, fields: List[(Option[Name], Type)])
    case Finite(name: Name, count: Int)

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double
    case Data(name: MName)
    case Record(name: MName)
    case Finite(name: MName)

  enum Expr:
    case Local(lvl: Lvl)
    case Global(name: MName, args: List[Expr])

    case Let(ty: Type, value: Expr, body: Expr)
    case Join(params: List[Type], value: Expr, body: Expr)
    case JoinRec(params: List[Type], value: Expr, body: Expr)
    case Jump(lvl: Lvl, args: List[Expr])

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case Con(datatype: MName, name: Name, args: List[Expr])
    case DataField(dataname: MName, conname: Name, scrut: Expr, ix: Int)
    case Case(
        dataname: MName,
        scrut: Expr,
        cases: List[(Name, Boolean, Expr)],
        otherwise: Option[Expr]
    )

    case RecordCon(name: MName, args: List[Expr])
    case Field(name: MName, scrut: Expr, ix: Int)

    case FiniteCon(name: MName, ix: Int)
    case FiniteCase(
        dataname: MName,
        scrut: Expr,
        cases: List[(Int, Expr)],
        otherwise: Option[Expr]
    )

    case Instr(opcode: Int, args: List[Expr])

    case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)

  // bytecode generation
  private case class ConstructorCtx(
      nameParts: List[Name],
      className: String,
      descriptor: String,
      ty: JType,
      params: List[(Name, JType)],
      constructor: Method
  )
  private case class DatatypeCtx(
      nameParts: List[Name],
      className: String,
      descriptor: String,
      ty: JType,
      constructors: mutable.Map[Name, ConstructorCtx] = mutable.Map.empty
  )
  private case class RecordCtx(
      nameParts: List[Name],
      className: String,
      descriptor: String,
      ty: JType,
      var constructor: Method = null,
      fields: mutable.ArrayBuffer[(Name, JType)] = mutable.ArrayBuffer.empty
  )
  private case class FiniteCtx(amount: Int, ty: JType)

  private class ModuleCtx(
      val name: Name,
      val ty: JType,
      val methods: mutable.Map[Name, Method] = mutable.Map.empty,
      val values: mutable.Map[Name, JType] = mutable.Map.empty,
      val datatypes: mutable.Map[Name, DatatypeCtx] = mutable.Map.empty,
      val records: mutable.Map[Name, RecordCtx] = mutable.Map.empty,
      val finites: mutable.Map[Name, FiniteCtx] = mutable.Map.empty
  )

  private class Ctx(val modules: Map[Name, ModuleCtx]):
    def module(name: MName): ModuleCtx = modules(name.module)
    def value(name: MName): JType = module(name).values(name.name)
    def method(name: MName): Method = module(name).methods(name.name)
    def datatype(name: MName): DatatypeCtx = module(name).datatypes(name.name)
    def record(name: MName): RecordCtx = module(name).records(name.name)
    def finite(name: MName): FiniteCtx = module(name).finites(name.name)

  private enum Local:
    case Arg(ix: Int)
    case Local(id: Int)
    case Label(label: JLabel, params: List[Int])
  private type Locals = List[Local]

  def generateBytecode(modules: List[Module], targetDir: String): Unit =
    val moduleMap = modules
      .map(m =>
        m.name -> new ModuleCtx(m.name, JType.getType(s"L${m.name.escape};"))
      )
      .toMap
    given ctx: Ctx = Ctx(moduleMap)
    modules.foreach(generateBytecode(_, targetDir))

  private def generateBytecode(module: Module, targetDir: String)(using
      ctx: Ctx
  ): Unit =
    given moduleCtx: ModuleCtx = ctx.modules(module.name)
    given cw: ClassWriter = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    ) {
      override protected def getCommonSuperClass(
          type1: String,
          type2: String
      ): String =
        val prefix = longestCommonPrefix(type1, type2)
        if prefix.endsWith("$") then prefix.init else prefix
    }
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_FINAL,
      module.name.escape,
      null,
      "java/lang/Object",
      null
    )

    // empty constructor
    val con = cw.visitMethod(ACC_PRIVATE, "<init>", "()V", null, null)
    con.visitVarInsn(ALOAD, 0)
    con.visitMethodInsn(
      INVOKESPECIAL,
      "java/lang/Object",
      "<init>",
      "()V",
      false
    )
    con.visitInsn(RETURN)
    con.visitMaxs(1, 1)
    con.visitEnd()

    // generate definitions
    updateModuleCtx(module.defs)
    module.defs.foreach(genDatatype(_, targetDir))
    module.defs.foreach(gen)

    // generate static block
    genStaticBlock(module.defs)

    // end
    cw.visitEnd()
    writeClass(cw, targetDir, List(module.name))

  private def gen(ty: Type)(using ctx: Ctx): JType = ty match
    case Type.Boolean      => JType.BOOLEAN_TYPE
    case Type.Byte         => JType.BYTE_TYPE
    case Type.Char         => JType.CHAR_TYPE
    case Type.Short        => JType.SHORT_TYPE
    case Type.Int          => JType.INT_TYPE
    case Type.Long         => JType.LONG_TYPE
    case Type.Float        => JType.FLOAT_TYPE
    case Type.Double       => JType.DOUBLE_TYPE
    case Type.Data(name)   => ctx.modules(name.module).datatypes(name.name).ty
    case Type.Record(name) => ctx.modules(name.module).records(name.name).ty
    case Type.Finite(name) => ctx.modules(name.module).finites(name.name).ty

  private def finiteType(amount: Int): JType = amount match
    case n if n <= 2          => JType.BOOLEAN_TYPE
    case n if n <= 128        => JType.BYTE_TYPE
    case n if n <= 32768      => JType.SHORT_TYPE
    case n if n <= 2147483647 => JType.INT_TYPE
    case n                    => err(s"finite type has too many members: $n")

  private def updateModuleCtx(defs: List[Def])(using
      moduleCtx: ModuleCtx,
      ctx: Ctx
  ): Unit =
    // first ensure all datatypes are known
    defs.foreach {
      case Def.Data(name, _) =>
        val className = s"${moduleCtx.name.escape}$$${name.escape}"
        val descriptor = s"L$className;"
        val ty = JType.getType(descriptor)
        moduleCtx.datatypes += (name -> DatatypeCtx(
          List(moduleCtx.name, name),
          className,
          descriptor,
          ty
        ))
      case Def.Record(name, _) =>
        val className = s"${moduleCtx.name.escape}$$${name.escape}"
        val descriptor = s"L$className;"
        val ty = JType.getType(descriptor)
        moduleCtx.records += (name -> RecordCtx(
          List(moduleCtx.name, name),
          className,
          descriptor,
          ty
        ))
      case Def.Finite(name, amount) =>
        moduleCtx.finites += (name -> FiniteCtx(amount, finiteType(amount)))
      case _ =>
    }
    defs.foreach(updateModuleCtx)

  private def updateModuleCtx(
      defn: Def
  )(using moduleCtx: ModuleCtx, ctx: Ctx): Unit =
    defn match
      case Def.Value(name, ty, _) =>
        moduleCtx.values += (name -> gen(ty))
      case Def.Function(name, params, returnType, _) =>
        val m = new Method(
          name.escape,
          gen(returnType),
          params.map(gen).toArray
        )
        moduleCtx.methods += (name -> m)
      case Def.Data(name, constructors) =>
        // handle constructors
        val datatypeCtx = moduleCtx.datatypes(name)
        constructors.foreach { c =>
          val conClassName =
            s"${datatypeCtx.className}$$${c.name.escape}"
          val descriptor = s"L$conClassName;"
          val ty = JType.getType(descriptor)
          val params = c.parameters.zipWithIndex.map { case ((x, t), i) =>
            (x.getOrElse(JvmName(s"p$i")), gen(t))
          }
          val constructorMethod =
            new Method("<init>", JType.VOID_TYPE, params.map(_._2).toArray)
          datatypeCtx.constructors(c.name) = ConstructorCtx(
            List(moduleCtx.name, name, c.name),
            conClassName,
            descriptor,
            ty,
            params,
            constructorMethod
          )
        }
      case Def.Record(name, fields) =>
        // handle fields
        val recordCtx = moduleCtx.records(name)
        val params = fields.zipWithIndex.map { case ((x, t), i) =>
          val pair = (x.getOrElse(JvmName(s"p$i")), gen(t))
          recordCtx.fields += pair
          pair
        }
        val constructorMethod =
          new Method("<init>", JType.VOID_TYPE, params.map(_._2).toArray)
        recordCtx.constructor = constructorMethod
      case Def.Finite(_, _) => ()

  private def genStaticBlock(
      defs: List[Def]
  )(using cw: ClassWriter, moduleCtx: ModuleCtx, ctx: Ctx): Unit =
    defs.flatMap {
      case Def.Value(name, ty, value) if constantValue(value).isEmpty =>
        Some((name, ty, value))
      case _ => None
    } match
      case Nil => ()
      case ds  =>
        val m = new Method("<clinit>", JType.VOID_TYPE, Nil.toArray)
        given mg: GeneratorAdapter =
          new GeneratorAdapter(ACC_STATIC, m, null, null, cw)
        given locals: Locals = Nil
        ds.foreach { case (name, ty, value) =>
          gen(value)
          mg.putStatic(moduleCtx.ty, name.escape, gen(ty))
        }
        mg.visitInsn(RETURN)
        mg.endMethod()

  private def gen(
      defn: Def
  )(using cw: ClassWriter, moduleCtx: ModuleCtx, ctx: Ctx): Unit =
    defn match
      case Def.Data(_, _)             => ()
      case Def.Record(_, _)           => ()
      case Def.Finite(_, _)           => ()
      case Def.Value(name, ty, value) =>
        cw.visitField(
          ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
          name.escape,
          gen(ty).getDescriptor,
          null,
          constantValue(value).orNull
        )
      case Def.Function(name, params, _, body) =>
        given mg: GeneratorAdapter =
          new GeneratorAdapter(
            ACC_FINAL + ACC_STATIC + ACC_PUBLIC,
            moduleCtx.methods(name),
            null,
            null,
            cw
          )
        given locals: Locals =
          params.zipWithIndex.map((_, ix) => Local.Arg(ix))
        gen(body)
        mg.returnValue()
        mg.endMethod()

  private def genDatatype(
      defn: Def,
      targetDir: String
  )(using cw: ClassWriter, moduleCtx: ModuleCtx): Unit =
    defn match
      case Def.Data(name, constructors) =>
        given datactx: DatatypeCtx = moduleCtx.datatypes(name)
        val className = datactx.className
        val datacw = new ClassWriter(
          ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
        )
        datacw.visit(
          V1_8,
          ACC_PUBLIC + ACC_ABSTRACT,
          className,
          null,
          "java/lang/Object",
          null
        )

        // private empty constructor
        val con = datacw.visitMethod(ACC_PROTECTED, "<init>", "()V", null, null)
        con.visitVarInsn(ALOAD, 0)
        con.visitMethodInsn(
          INVOKESPECIAL,
          "java/lang/Object",
          "<init>",
          "()V",
          false
        )
        con.visitInsn(RETURN)
        con.visitMaxs(1, 1)
        con.visitEnd()

        // constructors
        constructors.foreach { c =>
          given conctx: ConstructorCtx = datactx.constructors(c.name)
          genDatatypeConstructor(targetDir)
          datacw.visitInnerClass(
            conctx.className,
            className,
            c.name.escape,
            ACC_PUBLIC + ACC_STATIC + ACC_FINAL
          )
        }

        // write class file
        datacw.visitEnd()
        cw.visitInnerClass(
          className,
          moduleCtx.name.escape,
          name.escape,
          ACC_PUBLIC + ACC_ABSTRACT + ACC_STATIC
        )
        writeClass(datacw, targetDir, datactx.nameParts)
      case Def.Record(name, _) =>
        given recordctx: RecordCtx = moduleCtx.records(name)
        val className = recordctx.className
        val recordcw = new ClassWriter(
          ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
        )
        recordcw.visit(
          V1_8,
          ACC_PUBLIC,
          className,
          null,
          "java/lang/Object",
          null
        )

        // fields
        val params = recordctx.fields.zipWithIndex.map { case ((x, t), i) =>
          (x, t, i)
        }
        params.foreach { (x, ty, _) =>
          recordcw.visitField(
            ACC_PUBLIC + ACC_FINAL,
            x.escape,
            ty.getDescriptor,
            null,
            null
          )
        }

        // class constructor
        val m = recordctx.constructor
        val mg: GeneratorAdapter =
          new GeneratorAdapter(
            if params.isEmpty then ACC_PROTECTED else ACC_PUBLIC,
            m,
            null,
            null,
            recordcw
          )
        params.foreach { (x, ty, i) =>
          mg.loadThis()
          mg.loadArg(i)
          mg.putField(recordctx.ty, x.escape, ty)
        }
        mg.visitInsn(RETURN)
        mg.visitMaxs(1, 1)
        mg.visitEnd()

        // 0-ary constructor initialization
        if params.isEmpty then
          recordcw.visitField(
            ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
            "INSTANCE",
            recordctx.descriptor,
            null,
            null
          )
          val staticMethod =
            new Method("<clinit>", JType.VOID_TYPE, Nil.toArray)
          implicit val stmg: GeneratorAdapter =
            new GeneratorAdapter(ACC_STATIC, staticMethod, null, null, recordcw)
          stmg.newInstance(recordctx.ty)
          stmg.dup()
          stmg.invokeConstructor(recordctx.ty, recordctx.constructor)
          stmg.putStatic(recordctx.ty, "INSTANCE", recordctx.ty)
          stmg.visitInsn(RETURN)
          stmg.endMethod()

        // write class file
        recordcw.visitEnd()
        cw.visitInnerClass(
          className,
          moduleCtx.name.escape,
          name.escape,
          ACC_PUBLIC + ACC_STATIC
        )
        writeClass(recordcw, targetDir, recordctx.nameParts)
      case _ => ()

  private def genDatatypeConstructor(targetDir: String)(using
      datatypeCtx: DatatypeCtx,
      conCtx: ConstructorCtx
  ): Unit =
    val className = conCtx.className
    val cw = new ClassWriter(
      ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
    )
    cw.visit(
      V1_8,
      ACC_PUBLIC + ACC_STATIC + ACC_FINAL,
      className,
      null,
      datatypeCtx.className,
      null
    )

    // fields
    val params = conCtx.params.zipWithIndex.map { case ((x, t), i) =>
      (x, t, i)
    }
    params.foreach { (x, ty, _) =>
      cw.visitField(
        ACC_PUBLIC + ACC_FINAL,
        x.escape,
        ty.getDescriptor,
        null,
        null
      )
    }

    // class constructor
    val m = conCtx.constructor
    val mg: GeneratorAdapter =
      new GeneratorAdapter(
        if params.isEmpty then ACC_PROTECTED else ACC_PUBLIC,
        m,
        null,
        null,
        cw
      )
    mg.visitVarInsn(ALOAD, 0)
    mg.visitMethodInsn(
      INVOKESPECIAL,
      datatypeCtx.className,
      "<init>",
      "()V",
      false
    )
    params.foreach { (x, ty, i) =>
      mg.loadThis()
      mg.loadArg(i)
      mg.putField(conCtx.ty, x.escape, ty)
    }
    mg.visitInsn(RETURN)
    mg.visitMaxs(1, 1)
    mg.visitEnd()

    // 0-ary constructor initialization
    if params.isEmpty then
      cw.visitField(
        ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
        "INSTANCE",
        conCtx.descriptor,
        null,
        null
      )
      val staticMethod = new Method("<clinit>", JType.VOID_TYPE, Nil.toArray)
      implicit val stmg: GeneratorAdapter =
        new GeneratorAdapter(ACC_STATIC, staticMethod, null, null, cw)
      stmg.newInstance(conCtx.ty)
      stmg.dup()
      stmg.invokeConstructor(conCtx.ty, conCtx.constructor)
      stmg.putStatic(conCtx.ty, "INSTANCE", conCtx.ty)
      stmg.visitInsn(RETURN)
      stmg.endMethod()

    // done
    cw.visitEnd()
    writeClass(cw, targetDir, conCtx.nameParts)

  private def gen(
      expr: Expr
  )(using
      mg: GeneratorAdapter,
      locals: Locals,
      moduleCtx: ModuleCtx,
      ctx: Ctx
  ): Unit =
    expr match
      case Expr.Local(lvl) =>
        locals(lvl) match
          case Local.Arg(ix)     => mg.loadArg(ix)
          case Local.Local(id)   => mg.loadLocal(id)
          case Local.Label(_, _) =>
            err("tried to retrieve label")

      case Expr.Global(name, Nil) =>
        mg.getStatic(
          ctx.module(name).ty,
          name.name.escape,
          ctx.value(name)
        )
      case Expr.Global(name, args) =>
        args.foreach(gen)
        mg.invokeStatic(ctx.module(name).ty, ctx.method(name))

      case Expr.Let(ty, value, body) =>
        val id = mg.newLocal(gen(ty))
        gen(value)
        mg.storeLocal(id)
        gen(body)(using locals = locals :+ Local.Local(id))

      case Expr.Join(params, value, body) =>
        val paramLocals = params.map(ty => mg.newLocal(gen(ty)))
        val label = mg.newLabel()
        gen(body)(using locals = locals :+ Local.Label(label, paramLocals))
        mg.visitLabel(label)
        gen(value)(using
          locals = locals ++ paramLocals.map(id => Local.Local(id))
        )
      case Expr.JoinRec(params, value, body) =>
        val paramLocals = params.map(ty => mg.newLocal(gen(ty)))
        val label = mg.newLabel()
        val local = Local.Label(label, paramLocals)
        gen(body)(using locals = locals :+ local)
        mg.visitLabel(label)
        gen(value)(using
          locals = (locals :+ local) ++ paramLocals.map(id => Local.Local(id))
        )
      case Expr.Jump(lvl, args) =>
        locals(lvl) match
          case Local.Label(label, params) =>
            params.zip(args).foreach { (id, v) =>
              gen(v)
              mg.storeLocal(id)
            }
            mg.visitJumpInsn(GOTO, label)
          case _ => err("tried to jump to non-label")

      case Expr.IntLit(value)  => mg.push(value)
      case Expr.BoolLit(value) => mg.push(value)

      case Expr.Con(dname, cname, args) =>
        val conctx = ctx.datatype(dname).constructors(cname)
        if args.isEmpty then mg.getStatic(conctx.ty, "INSTANCE", conctx.ty)
        else
          mg.newInstance(conctx.ty)
          mg.dup()
          args.foreach(gen)
          mg.invokeConstructor(conctx.ty, conctx.constructor)
      case Expr.DataField(dx, cx, scrut, ix) =>
        val datactx = ctx.datatype(dx)
        val conctx = datactx.constructors(cx)
        gen(scrut)
        val (x, t) = conctx.params(ix)
        mg.getField(conctx.ty, x.escape, t)
      case Expr.Case(dx, scrut, cases, otherwise) =>
        val datactx = ctx.datatype(dx)
        val lEnd = mg.newLabel()
        gen(scrut)
        cases.zipWithIndex.foreach { case ((cx, isUsed, body), i) =>
          val isLast = i == cases.size - 1 && otherwise.isEmpty
          val conctx = datactx.constructors(cx)
          val nilary = conctx.params.isEmpty
          val lNext = mg.newLabel()
          if isUsed || !isLast then mg.dup()
          if !isLast then
            if nilary then
              mg.getStatic(conctx.ty, "INSTANCE", conctx.ty)
              mg.visitJumpInsn(IF_ACMPNE, lNext)
            else
              mg.instanceOf(conctx.ty)
              mg.visitJumpInsn(IFEQ, lNext)
          val local = mg.newLocal(conctx.ty)
          if isUsed then
            mg.checkCast(conctx.ty)
            mg.storeLocal(local)
          else if !isLast then mg.pop()
          gen(body)(using locals = locals :+ Local.Local(local))
          if !isLast then mg.visitJumpInsn(GOTO, lEnd)
          mg.visitLabel(lNext)
        }
        otherwise.foreach { o =>
          mg.pop()
          gen(o)
        }
        mg.visitLabel(lEnd)

      case Expr.RecordCon(name, args) =>
        val recordctx = ctx.record(name)
        if args.isEmpty then
          mg.getStatic(recordctx.ty, "INSTANCE", recordctx.ty)
        else
          mg.newInstance(recordctx.ty)
          mg.dup()
          args.foreach(gen)
          mg.invokeConstructor(recordctx.ty, recordctx.constructor)
      case Expr.Field(name, scrut, ix) =>
        val recordctx = ctx.record(name)
        gen(scrut)
        val (x, t) = recordctx.fields(ix)
        mg.getField(recordctx.ty, x.escape, t)

      case Expr.FiniteCon(name, ix) =>
        val finitectx = ctx.finite(name)
        finitectx.amount match
          case n if n <= 2          => mg.push(ix == 1)
          case n if n <= 128        => mg.push(ix.toByte)
          case n if n <= 32768      => mg.push(ix.toShort)
          case n if n <= 2147483647 => mg.push(ix)
          case n => err(s"finite type has too many members: $n")

      case Expr.Instr(opcode, args) =>
        args.foreach(gen)
        mg.visitInsn(opcode)

      case Expr.If(c, t, f) =>
        val falseLabel = mg.newLabel()
        val endLabel = mg.newLabel()
        gen(c)
        mg.visitJumpInsn(IFEQ, falseLabel)
        gen(t)
        mg.visitJumpInsn(GOTO, endLabel)
        mg.visitLabel(falseLabel)
        gen(f)
        mg.visitLabel(endLabel)

      case Expr.FiniteCase(dx, scrut, cases, otherwise) =>
        val datactx = ctx.finite(dx)
        datactx.amount match
          case 0 => () // is this correct?
          case 1 =>
            (cases, otherwise) match
              case (List((_, b)), None) => gen(b) // is this correct?
              case (Nil, Some(b))       => gen(b) // is this correct?
              case _                    => impossible()
          case _ =>
            if cases.isEmpty then gen(otherwise.get) // is this correct?
            else
              val s = cases.map(_._1).sorted
              gen(scrut)
              if hasNoHoles(s) then
                otherwise match
                  case Some(o) =>
                    val labels = cases.map(_ => mg.newLabel())
                    val default = mg.newLabel()
                    val end = mg.newLabel()
                    mg.visitTableSwitchInsn(
                      s.head,
                      s.last,
                      default,
                      labels.toArray*
                    )
                    cases.sortBy((i, _) => i).zip(labels).foreach {
                      case ((_, b), l) =>
                        mg.visitLabel(l)
                        gen(b)
                        mg.visitJumpInsn(GOTO, end)
                    }
                    mg.visitLabel(default)
                    gen(o)
                    mg.visitLabel(end)
                  case None =>
                    val labels = cases.init.map(_ => mg.newLabel())
                    val default = mg.newLabel()
                    val end = mg.newLabel()
                    mg.visitTableSwitchInsn(
                      s.head,
                      s.last - 1,
                      default,
                      labels.toArray*
                    )
                    val sortedCases = cases.sortBy((i, _) => i)
                    sortedCases.init.zip(labels).foreach { case ((_, b), l) =>
                      mg.visitLabel(l)
                      gen(b)
                      mg.visitJumpInsn(GOTO, end)
                    }
                    mg.visitLabel(default)
                    gen(sortedCases.last._2)
                    mg.visitLabel(end)
              else
                otherwise match
                  case Some(o) =>
                    val labels = cases.map(_ => mg.newLabel())
                    val default = mg.newLabel()
                    val end = mg.newLabel()
                    mg.visitLookupSwitchInsn(
                      default,
                      cases.map((k, _) => k).toArray,
                      labels.toArray
                    )
                    cases.zip(labels).foreach { case ((_, b), l) =>
                      mg.visitLabel(l)
                      gen(b)
                      mg.visitJumpInsn(GOTO, end)
                    }
                    mg.visitLabel(default)
                    gen(o)
                    mg.visitLabel(end)
                  case None =>
                    val labels = cases.init.map(_ => mg.newLabel())
                    val default = mg.newLabel()
                    val end = mg.newLabel()
                    mg.visitLookupSwitchInsn(
                      default,
                      cases.init.map((k, _) => k).toArray,
                      labels.toArray
                    )
                    cases.init.zip(labels).foreach { case ((_, b), l) =>
                      mg.visitLabel(l)
                      gen(b)
                      mg.visitJumpInsn(GOTO, end)
                    }
                    mg.visitLabel(default)
                    gen(cases.last._2)
                    mg.visitLabel(end)

  private def hasNoHoles(l: List[Int]): Boolean =
    @tailrec
    def go(l: List[Int], c: Int): Boolean =
      l match
        case Nil              => true
        case n :: _ if n != c => false
        case _ :: tl          => go(tl, c + 1)
    go(l.tail, l.head + 1)

  // from https://stackoverflow.com/questions/8104479/how-to-find-the-longest-common-prefix-of-two-strings-in-scala
  private def longestCommonPrefix(a: String, b: String): String =
    var same = true
    var i = 0
    while same && i < math.min(a.length, b.length) do
      if a.charAt(i) != b.charAt(i) then same = false
      else i += 1
    a.substring(0, i)

  private def constantValue(expr: Expr)(using ctx: Ctx): Option[AnyRef] =
    expr match
      case Expr.IntLit(value)    => Some(Int.box(value))
      case Expr.BoolLit(value)   => Some(Boolean.box(value))
      case Expr.FiniteCon(x, ix) => Some(finiteValue(x, ix))
      case _                     => None

  private def finiteValue(name: MName, ix: Int)(using ctx: Ctx): AnyRef =
    ctx.finite(name).amount match
      case n if n <= 2          => (ix == 1).asInstanceOf[AnyRef]
      case n if n <= 128        => ix.toByte.asInstanceOf[AnyRef]
      case n if n <= 32768      => ix.toShort.asInstanceOf[AnyRef]
      case n if n <= 2147483647 => ix.asInstanceOf[AnyRef]
      case n                    => err(s"finite type has too many members: $n")

  // io
  private def writeClass(
      cw: ClassWriter,
      targetDir: String,
      nameParts: List[Name]
  ): Unit =
    val path = s"$targetDir/${nameParts.map(_.escapePath).mkString("$")}.class"
    Path.of(path).toFile.getParentFile.mkdirs()
    val bos = new BufferedOutputStream(new FileOutputStream(path))
    bos.write(cw.toByteArray)
    bos.close()
