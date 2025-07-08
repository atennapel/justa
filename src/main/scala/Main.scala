import JVM.{Def, Expr, Module, Type, Constructor}
import org.objectweb.asm.Opcodes.{IADD, IMUL, ISUB}

object Main:
  @main def run(): Unit =
    val testModule = Module(
      "TestModule",
      List(
        Def.Function(
          "test",
          List(),
          Type.Int,
          Expr.Join(
            List(),
            Expr.Global("add", List(Expr.IntLit(1), Expr.IntLit(2))),
            Expr.Jump(0, List())
          )
        ),
        Def.Function(
          "add",
          List(Type.Int, Type.Int),
          Type.Int,
          Expr.Let(
            Expr.Instr(IADD, List(Expr.Local(0), Expr.Local(1))),
            Type.Int,
            Expr.Instr(IADD, List(Expr.Local(2), Expr.Local(2)))
          )
        ),
        Def.Function(
          "isZero",
          List(Type.Int),
          Type.Boolean,
          Expr.If(Expr.Local(0), Expr.BoolLit(false), Expr.BoolLit(true))
        ),
        Def.Function(
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
        Def.Function(
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
        Def.Function(
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
        Def.Function(
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
        ),
        Def.Value(
          "val1",
          Type.Int,
          Expr.IntLit(42)
        ),
        Def.Value(
          "val2",
          Type.Int,
          Expr.Instr(IADD, List(Expr.IntLit(1), Expr.IntLit(2)))
        ),
        Def.Value(
          "datatest1",
          Type.Data("IntOption"),
          Expr.Con("IntOption", "Some", List(Expr.IntLit(42)))
        ),
        Def.Value(
          "datatest2",
          Type.Data("IntList"),
          Expr.Con("IntList", "Nil", List())
        ),
        Def.Function(
          "head",
          List(Type.Data("IntList")),
          Type.Data("IntOption"),
          Expr.Case(
            "IntList",
            "Cons",
            Expr.Local(0),
            Expr.Con("IntOption", "Some", List(Expr.Local(1))),
            Some(Expr.Con("IntOption", "None", List()))
          )
        ),
        Def.Function(
          "inc",
          List(Type.Data("IntList")),
          Type.Data("IntList"),
          Expr.Case(
            "IntList",
            "Cons",
            Expr.Local(0),
            Expr.Con(
              "IntList",
              "Cons",
              List(
                Expr.Instr(IADD, List(Expr.Local(1), Expr.IntLit(1))),
                Expr.Global("inc", List(Expr.Local(2)))
              )
            ),
            Some(Expr.Con("IntList", "Nil", List()))
          )
        ),
        Def.Data(
          "IntOption",
          List(
            Constructor("None", List()),
            Constructor("Some", List((Some("value"), Type.Int)))
          )
        ),
        Def.Data(
          "IntList",
          List(
            Constructor("Nil", List()),
            Constructor(
              "Cons",
              List(
                (Some("head"), Type.Int),
                (Some("tail"), Type.Data("IntList"))
              )
            )
          )
        ),
        Def.Data(
          "B",
          List(Constructor("T", List()), Constructor("F", List()))
        ),
        Def.Data("Void", List()),
        Def.Record("Unit", List()),
        Def.Record(
          "IntPair",
          List((Some("fst"), Type.Int), (Some("snd"), Type.Int))
        ),
        Def.Value(
          "pairtest",
          Type.Record("IntPair"),
          Expr.RecordCon("IntPair", List(Expr.IntLit(1), Expr.IntLit(2)))
        ),
        Def.Function(
          "pairproj",
          List(Type.Record("IntPair")),
          Type.Record("IntPair"),
          Expr.RecordCon(
            "IntPair",
            List(
              Expr.Field("IntPair", Expr.Local(0), Left("fst")),
              Expr.Field("IntPair", Expr.Local(0), Right(1))
            )
          )
        )
      )
    )
    JVM.generateBytecode(testModule)
