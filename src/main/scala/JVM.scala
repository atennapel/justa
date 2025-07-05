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

  final case class Module(name: Name, defs: List[Def])

  final case class Def(
      name: Name,
      params: List[Type],
      returnType: Type,
      body: Expr
  )

  enum Type:
    case Boolean
    case Byte
    case Char
    case Short
    case Int
    case Long
    case Float
    case Double

  enum Expr:
    case Local(lvl: Int)
    case Global(name: Name, args: List[Expr])

    case Let(value: Expr, ty: Type, body: Expr)
    case Join(params: List[Type], value: Expr, body: Expr)
    case JoinRec(params: List[Type], value: Expr, body: Expr)
    case Jump(lvl: Int, args: List[Expr])

    case IntLit(value: Int)
    case BoolLit(value: Boolean)

    case Instr(opcode: Int, args: List[Expr])

    // temp
    case If(cond: Expr, ifTrue: Expr, ifFalse: Expr)

  // bytecode generation
  private class ModuleCtx(
      val name: Name,
      val ty: JType,
      val methods: mutable.Map[String, Method] = mutable.Map.empty
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
    module.defs.foreach(updateModuleCtx)
    module.defs.foreach(gen)

    // end
    cw.visitEnd()
    val bos = new BufferedOutputStream(
      new FileOutputStream(s"${module.name}.class")
    )
    bos.write(cw.toByteArray)
    bos.close()

  private def gen(ty: Type): JType = ty match
    case Type.Boolean => JType.BOOLEAN_TYPE
    case Type.Byte    => JType.BYTE_TYPE
    case Type.Char    => JType.CHAR_TYPE
    case Type.Short   => JType.SHORT_TYPE
    case Type.Int     => JType.INT_TYPE
    case Type.Long    => JType.LONG_TYPE
    case Type.Float   => JType.FLOAT_TYPE
    case Type.Double  => JType.DOUBLE_TYPE

  private def updateModuleCtx(defn: Def)(using moduleCtx: ModuleCtx): Unit =
    val m = new Method(
      defn.name,
      gen(defn.returnType),
      defn.params.map(gen).toArray
    )
    moduleCtx.methods += (defn.name -> m)

  private def gen(
      defn: Def
  )(using cw: ClassWriter, moduleCtx: ModuleCtx): Unit =
    given mg: GeneratorAdapter =
      new GeneratorAdapter(
        ACC_FINAL + ACC_STATIC + ACC_PUBLIC,
        moduleCtx.methods(defn.name),
        null,
        null,
        cw
      )
    given locals: Locals =
      defn.params.zipWithIndex.map((_, ix) => Local.Arg(ix))
    gen(defn.body)
    mg.returnValue()
    mg.endMethod()

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

      case Expr.Global(name, args) =>
        args.foreach(gen)
        mg.invokeStatic(moduleCtx.ty, moduleCtx.methods(name))

      case Expr.Let(value, ty, body) =>
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
