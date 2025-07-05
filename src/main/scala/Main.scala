import JVM.{Def, Expr, Module, Type}
import org.objectweb.asm.Opcodes.{IADD, IMUL, ISUB}

object Main:
  @main def run(): Unit =
    val testModule = Module(
      "TestModule",
      List(
        Def(
          "test",
          List(),
          Type.Int,
          Expr.Join(
            List(),
            Expr.Global("add", List(Expr.IntLit(1), Expr.IntLit(2))),
            Expr.Jump(0, List())
          )
        ),
        Def(
          "add",
          List(Type.Int, Type.Int),
          Type.Int,
          Expr.Let(
            Expr.Instr(IADD, List(Expr.Local(0), Expr.Local(1))),
            Type.Int,
            Expr.Instr(IADD, List(Expr.Local(2), Expr.Local(2)))
          )
        ),
        Def(
          "isZero",
          List(Type.Int),
          Type.Boolean,
          Expr.If(Expr.Local(0), Expr.BoolLit(false), Expr.BoolLit(true))
        ),
        Def(
          "countDown",
          List(Type.Int),
          Type.Boolean,
          Expr.If(
            Expr.Global("isZero", List(Expr.Local(0))),
            Expr.BoolLit(true),
            Expr.Global(
              "countDown",
              List(Expr.Instr(ISUB, List(Expr.Local(0), Expr.IntLit(1))))
            )
          )
        ),
        Def(
          "countDownTR",
          List(Type.Int),
          Type.Boolean,
          Expr.JoinRec(
            List(Type.Int),
            Expr.If(
              Expr.Global("isZero", List(Expr.Local(2))),
              Expr.BoolLit(true),
              Expr.Jump(
                1,
                List(Expr.Instr(ISUB, List(Expr.Local(2), Expr.IntLit(1))))
              )
            ),
            Expr.Jump(1, List(Expr.Local(0)))
          )
        ),
        Def(
          "fac",
          List(Type.Int),
          Type.Int,
          Expr.If(
            Expr.Global("isZero", List(Expr.Local(0))),
            Expr.IntLit(1),
            Expr.Instr(
              IMUL,
              List(
                Expr.Local(0),
                Expr.Global(
                  "fac",
                  List(Expr.Instr(ISUB, List(Expr.Local(0), Expr.IntLit(1))))
                )
              )
            )
          )
        ),
        Def(
          "facTR",
          List(Type.Int),
          Type.Int,
          Expr.JoinRec(
            List(Type.Int, Type.Int),
            Expr.If(
              Expr.Global("isZero", List(Expr.Local(2))),
              Expr.Local(3),
              Expr.Jump(
                1,
                List(
                  Expr.Instr(ISUB, List(Expr.Local(2), Expr.IntLit(1))),
                  Expr.Instr(IMUL, List(Expr.Local(2), Expr.Local(3)))
                )
              )
            ),
            Expr.Jump(1, List(Expr.Local(0), Expr.IntLit(1)))
          )
        )
      )
    )
    JVM.generateBytecode(testModule)
