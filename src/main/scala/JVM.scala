import org.objectweb.asm.ClassWriter
import org.objectweb.asm.Type as JType
import org.objectweb.asm.Label as JLabel
import org.objectweb.asm.Opcodes.*
import org.objectweb.asm.commons.Method
import org.objectweb.asm.commons.GeneratorAdapter

import java.io.BufferedOutputStream
import java.io.FileOutputStream

import scala.collection.mutable

object JVM:
  type Name = String
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

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double
    case Data(name: Name)
    case Record(name: Name)

  enum Expr:
    case Local(lvl: Lvl)
    case Global(name: Name, args: List[Expr])

    case Let(ty: Type, value: Expr, body: Expr)
    case Join(params: List[Type], value: Expr, body: Expr)
    case JoinRec(params: List[Type], value: Expr, body: Expr)
    case Jump(lvl: Lvl, args: List[Expr])

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case Con(datatype: Name, name: Name, args: List[Expr])
    case Case(
        datatype: Name,
        name: Name,
        scrut: Expr,
        body: Expr,
        other: Option[Expr]
    )

    case RecordCon(name: Name, args: List[Expr])
    case Field(name: Name, scrut: Expr, ix: Either[Name, Int])

    case Instr(opcode: Int, args: List[Expr])

    case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)

  // bytecode generation
  private case class ConstructorCtx(
      className: String,
      descriptor: String,
      ty: JType,
      params: List[(Name, JType)],
      constructor: Method
  )
  private case class DatatypeCtx(
      className: String,
      descriptor: String,
      ty: JType,
      constructors: mutable.Map[Name, ConstructorCtx] = mutable.Map.empty
  )
  private case class RecordCtx(
      className: String,
      descriptor: String,
      ty: JType,
      var constructor: Method = null,
      fields: mutable.ArrayBuffer[(Name, JType)] = mutable.ArrayBuffer.empty
  )

  private class ModuleCtx(
      val name: Name,
      val ty: JType,
      val methods: mutable.Map[String, Method] = mutable.Map.empty,
      val values: mutable.Map[String, JType] = mutable.Map.empty,
      val datatypes: mutable.Map[String, DatatypeCtx] = mutable.Map.empty,
      val records: mutable.Map[String, RecordCtx] = mutable.Map.empty
  )

  private enum Local:
    case Arg(ix: Int)
    case Local(id: Int)
    case Label(label: JLabel, params: List[Int])
  private type Locals = List[Local]

  def generateBytecode(module: Module): Unit =
    given moduleCtx: ModuleCtx =
      new ModuleCtx(module.name, JType.getType(s"L${module.name};"))

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
      module.name,
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
    module.defs.foreach(genDatatype)
    module.defs.foreach(gen)

    // generate static block
    genStaticBlock(module.defs)

    // end
    cw.visitEnd()
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"${module.name}.class")
    )
    bos.write(cw.toByteArray)
    bos.close()

  private def gen(ty: Type)(using moduleCtx: ModuleCtx): JType = ty match
    case Type.Boolean      => JType.BOOLEAN_TYPE
    case Type.Byte         => JType.BYTE_TYPE
    case Type.Char         => JType.CHAR_TYPE
    case Type.Short        => JType.SHORT_TYPE
    case Type.Int          => JType.INT_TYPE
    case Type.Long         => JType.LONG_TYPE
    case Type.Float        => JType.FLOAT_TYPE
    case Type.Double       => JType.DOUBLE_TYPE
    case Type.Data(name)   => moduleCtx.datatypes(name).ty
    case Type.Record(name) => moduleCtx.records(name).ty

  private def updateModuleCtx(defs: List[Def])(using
      moduleCtx: ModuleCtx
  ): Unit =
    // first ensure all datatypes are known
    defs.foreach {
      case Def.Data(name, _) =>
        val className = s"${moduleCtx.name}$$$name"
        val descriptor = s"L$className;"
        val ty = JType.getType(descriptor)
        moduleCtx.datatypes += (name -> DatatypeCtx(
          className,
          descriptor,
          ty
        ))
      case Def.Record(name, _) =>
        val className = s"${moduleCtx.name}$$$name"
        val descriptor = s"L$className;"
        val ty = JType.getType(descriptor)
        moduleCtx.records += (name -> RecordCtx(
          className,
          descriptor,
          ty
        ))
      case _ =>
    }
    defs.foreach(updateModuleCtx)

  private def updateModuleCtx(defn: Def)(using moduleCtx: ModuleCtx): Unit =
    defn match
      case Def.Value(name, ty, _) =>
        moduleCtx.values += (name -> gen(ty))
      case Def.Function(name, params, returnType, _) =>
        val m = new Method(
          name,
          gen(returnType),
          params.map(gen).toArray
        )
        moduleCtx.methods += (name -> m)
      case Def.Data(name, constructors) =>
        // handle constructors
        val datatypeCtx = moduleCtx.datatypes(name)
        constructors.foreach { c =>
          val conClassName = s"${datatypeCtx.className}$$${c.name}"
          val descriptor = s"L$conClassName;"
          val ty = JType.getType(descriptor)
          val params = c.parameters.zipWithIndex.map { case ((x, t), i) =>
            (x.getOrElse(s"p$i"), gen(t))
          }
          val constructorMethod =
            new Method("<init>", JType.VOID_TYPE, params.map(_._2).toArray)
          datatypeCtx.constructors(c.name) = ConstructorCtx(
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
          val pair = (x.getOrElse(s"p$i"), gen(t))
          recordCtx.fields += pair
          pair
        }
        val constructorMethod =
          new Method("<init>", JType.VOID_TYPE, params.map(_._2).toArray)
        recordCtx.constructor = constructorMethod

  private def genStaticBlock(
      defs: List[Def]
  )(using cw: ClassWriter, moduleCtx: ModuleCtx): Unit =
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
          mg.putStatic(moduleCtx.ty, name, gen(ty))
        }
        mg.visitInsn(RETURN)
        mg.endMethod()

  private def gen(
      defn: Def
  )(using cw: ClassWriter, moduleCtx: ModuleCtx): Unit =
    defn match
      case Def.Data(_, _)             => ()
      case Def.Record(_, _)           => ()
      case Def.Value(name, ty, value) =>
        cw.visitField(
          ACC_PUBLIC + ACC_FINAL + ACC_STATIC,
          name,
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
      defn: Def
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
          genDatatypeConstructor()
          datacw.visitInnerClass(
            conctx.className,
            className,
            c.name,
            ACC_PUBLIC + ACC_STATIC + ACC_FINAL
          )
        }

        // write class file
        datacw.visitEnd()
        cw.visitInnerClass(
          className,
          moduleCtx.name,
          name,
          ACC_PUBLIC + ACC_ABSTRACT + ACC_STATIC
        )
        val bos = new BufferedOutputStream(
          new FileOutputStream(s"$className.class")
        )
        bos.write(datacw.toByteArray)
        bos.close()
      case Def.Record(name, _) =>
        given recordctx: RecordCtx = moduleCtx.records(name)
        val className = recordctx.className
        val recordcw = new ClassWriter(
          ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES
        )
        recordcw.visit(
          V1_8,
          ACC_PUBLIC + ACC_ABSTRACT,
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
            x,
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
          mg.putField(recordctx.ty, x, ty)
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
          moduleCtx.name,
          name,
          ACC_PUBLIC + ACC_ABSTRACT + ACC_STATIC
        )
        val bos = new BufferedOutputStream(
          new FileOutputStream(s"$className.class")
        )
        bos.write(recordcw.toByteArray)
        bos.close()
      case _ => ()

  private def genDatatypeConstructor()(using
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
        x,
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
      mg.putField(conCtx.ty, x, ty)
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
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"$className.class")
    )
    bos.write(cw.toByteArray)
    bos.close()

  private def gen(
      expr: Expr
  )(using mg: GeneratorAdapter, locals: Locals, moduleCtx: ModuleCtx): Unit =
    expr match
      case Expr.Local(lvl) =>
        locals(lvl) match
          case Local.Arg(ix)     => mg.loadArg(ix)
          case Local.Local(id)   => mg.loadLocal(id)
          case Local.Label(_, _) =>
            throw new Exception("tried to retrieve label")

      case Expr.Global(name, Nil) =>
        mg.getStatic(moduleCtx.ty, name, moduleCtx.values(name))
      case Expr.Global(name, args) =>
        args.foreach(gen)
        mg.invokeStatic(moduleCtx.ty, moduleCtx.methods(name))

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
          case _ => throw new Exception("tried to jump to non-label")

      case Expr.IntLit(value)  => mg.push(value)
      case Expr.BoolLit(value) => mg.push(value)

      case Expr.Con(dname, cname, args) =>
        val conctx = moduleCtx.datatypes(dname).constructors(cname)
        if args.isEmpty then mg.getStatic(conctx.ty, "INSTANCE", conctx.ty)
        else
          mg.newInstance(conctx.ty)
          mg.dup()
          args.foreach(gen)
          mg.invokeConstructor(conctx.ty, conctx.constructor)
      case Expr.Case(dname, cname, scrut, body, other) =>
        val conctx = moduleCtx.datatypes(dname).constructors(cname)
        val nilary = conctx.params.isEmpty
        gen(scrut)
        other match
          case Some(o) =>
            val lEnd = mg.newLabel()
            val lOther = mg.newLabel()
            mg.dup()
            if nilary then
              mg.getStatic(conctx.ty, "INSTANCE", conctx.ty)
              mg.visitJumpInsn(IF_ACMPNE, lOther)
              mg.pop()
              gen(body)
            else
              mg.instanceOf(conctx.ty)
              mg.visitJumpInsn(IFEQ, lOther)
              mg.checkCast(conctx.ty)
              val paramlocals = conctx.params.map { (x, ty) =>
                mg.dup()
                val local = mg.newLocal(ty)
                mg.getField(conctx.ty, x, ty)
                mg.storeLocal(local)
                Local.Local(local)
              }
              mg.pop()
              gen(body)(using locals = locals ++ paramlocals)
            mg.visitJumpInsn(GOTO, lEnd)
            mg.visitLabel(lOther)
            mg.pop()
            gen(o)
            mg.visitLabel(lEnd)
          case None =>
            if nilary then
              mg.pop()
              gen(body)
            else
              mg.checkCast(conctx.ty)
              val paramlocals = conctx.params.map { (x, ty) =>
                mg.dup()
                val local = mg.newLocal(ty)
                mg.getField(conctx.ty, x, ty)
                mg.storeLocal(local)
                Local.Local(local)
              }
              mg.pop()
              gen(body)(using locals = locals ++ paramlocals)

      case Expr.RecordCon(name, args) =>
        val recordctx = moduleCtx.records(name)
        if args.isEmpty then
          mg.getStatic(recordctx.ty, "INSTANCE", recordctx.ty)
        else
          mg.newInstance(recordctx.ty)
          mg.dup()
          args.foreach(gen)
          mg.invokeConstructor(recordctx.ty, recordctx.constructor)
      case Expr.Field(name, scrut, ix) =>
        val recordctx = moduleCtx.records(name)
        gen(scrut)
        val (x, t) = ix match
          case Left(x)  => recordctx.fields.find((y, t) => x == y).get
          case Right(i) => recordctx.fields(i)
        mg.getField(recordctx.ty, x, t)

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

  // from https://stackoverflow.com/questions/8104479/how-to-find-the-longest-common-prefix-of-two-strings-in-scala
  private def longestCommonPrefix(a: String, b: String): String =
    var same = true
    var i = 0
    while same && i < math.min(a.length, b.length) do
      if a.charAt(i) != b.charAt(i) then same = false
      else i += 1
    a.substring(0, i)

  private def constantValue(expr: Expr): Option[AnyRef] =
    expr match
      case Expr.IntLit(value)  => Some(Int.box(value))
      case Expr.BoolLit(value) => Some(Boolean.box(value))
      case _                   => None
