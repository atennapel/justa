import JVM.{Constructor, Def, Expr, Module, Type}
import org.objectweb.asm.Opcodes.{IADD, IMUL, ISUB}

object Main:
  @main def run(): Unit =
    val testModule = Module(
      "TestModule",
      List(
        Def.Function(
          "test",
          Nil,
          Type.Int,
          Expr.Join(
            Nil,
            Expr.Global("add", List(Expr.IntLit(1), Expr.IntLit(2))),
            Expr.Jump(0, Nil)
          )
        ),
        Def.Function(
          "add",
          List(Type.Int, Type.Int),
          Type.Int,
          Expr.Let(
            Type.Int,
            Expr.Instr(IADD, List(Expr.Local(0), Expr.Local(1))),
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
          Expr.Con("IntList", "Nil", Nil)
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
            Some(Expr.Con("IntOption", "None", Nil))
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
            Some(Expr.Con("IntList", "Nil", Nil))
          )
        ),
        Def.Data(
          "IntOption",
          List(
            Constructor("None", Nil),
            Constructor("Some", List((Some("value"), Type.Int)))
          )
        ),
        Def.Data(
          "IntList",
          List(
            Constructor("Nil", Nil),
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
          List(Constructor("T", Nil), Constructor("F", Nil))
        ),
        Def.Data("Void", Nil),
        Def.Record("Unit", Nil),
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
    // JVM.generateBytecode(testModule)
    val irModule = IR.Module(
      "testmodule",
      List(
        /*
        IR.Def.Value(
          "def1",
          IR.TypeDef(List(IR.Type.Int, IR.Type.Int), IR.Type.Int),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.Lam(
              IR.Type.Int,
              IR.Expr.App(
                IR.Expr.App(IR.Expr.Global("def2"), IR.Expr.Local(1)),
                IR.Expr.Local(0)
              )
            )
          )
        ),
        IR.Def.Value(
          "def2",
          IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.Let(
              IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
              IR.Expr.Lam(IR.Type.Int, IR.Expr.Local(0)),
              IR.Expr.Let(
                IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
                IR.Expr.Local(0),
                IR.Expr.App(
                  IR.Expr.Local(0),
                  IR.Expr.App(IR.Expr.Local(0), IR.Expr.Local(2))
                )
              )
            )
          )
        ),
        IR.Def.Value(
          "def3",
          IR.TypeDef(Nil, IR.Type.Int),
          IR.Expr.LetRec(
            IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
            IR.Expr.Lam(
              IR.Type.Int,
              IR.Expr.App(IR.Expr.Local(1), IR.Expr.Local(0))
            ),
            IR.Expr.App(IR.Expr.Local(0), IR.Expr.IntLit(42))
          )
        ),*/
        IR.Def.Value(
          "isZero",
          IR.TypeDef(List(IR.Type.Int), IR.Type.Boolean),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.If(
              IR.TypeDef(Nil, IR.Type.Boolean),
              IR.Expr.Local(0, IR.TypeDef(IR.Type.Int)),
              IR.Expr.BoolLit(false),
              IR.Expr.BoolLit(true)
            )
          )
        ),
        IR.Def.Value( // \x => let c = \_ => x; c (c x)
          "freeTest",
          IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.Let(
              IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
              IR.Expr
                .Lam(IR.Type.Int, IR.Expr.Local(1, IR.TypeDef(IR.Type.Int))),
              IR.Expr.App(
                IR.Expr.Local(0, IR.TypeDef(List(IR.Type.Int), IR.Type.Int)),
                IR.Expr.App(
                  IR.Expr.Local(0, IR.TypeDef(List(IR.Type.Int), IR.Type.Int)),
                  IR.Expr.IntLit(42)
                )
              )
            )
          )
        ),
        IR.Def.Value(
          "fac",
          IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.LetRec(
              IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
              IR.Expr.Lam(
                IR.Type.Int,
                IR.Expr.If(
                  IR.TypeDef(Nil, IR.Type.Int),
                  IR.Expr.App(
                    IR.Expr.Global("isZero"),
                    IR.Expr.Local(0, IR.TypeDef(IR.Type.Int))
                  ),
                  IR.Expr.IntLit(1),
                  IR.Expr.Instr(
                    IMUL,
                    List(
                      IR.Expr.Local(0, IR.TypeDef(IR.Type.Int)),
                      IR.Expr.App(
                        IR.Expr
                          .Local(1, IR.TypeDef(List(IR.Type.Int), IR.Type.Int)),
                        IR.Expr.Instr(
                          ISUB,
                          List(
                            IR.Expr.Local(0, IR.TypeDef(IR.Type.Int)),
                            IR.Expr.IntLit(1)
                          )
                        )
                      )
                    )
                  )
                )
              ),
              IR.Expr.App(
                IR.Expr.Local(0, IR.TypeDef(List(IR.Type.Int), IR.Type.Int)),
                IR.Expr.Local(1, IR.TypeDef(IR.Type.Int))
              )
            )
          )
        ),
        /*
        def fac2 = \n =>
          let rec go = \n =>
            if isZero n then
              \acc => 1
            else
              \acc => go (n - 1) (acc * n);
          go n 1
         */
        IR.Def.Value(
          "fac2",
          IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
          IR.Expr.Lam(
            IR.Type.Int,
            IR.Expr.LetRec(
              IR.TypeDef(List(IR.Type.Int, IR.Type.Int), IR.Type.Int),
              IR.Expr.Lam(
                IR.Type.Int,
                IR.Expr.If(
                  IR.TypeDef(List(IR.Type.Int), IR.Type.Int),
                  IR.Expr.App(
                    IR.Expr.Global("isZero"),
                    IR.Expr.Local(0, IR.TypeDef(IR.Type.Int))
                  ),
                  IR.Expr.Lam(
                    IR.Type.Int,
                    IR.Expr.Local(0, IR.TypeDef(IR.Type.Int))
                  ),
                  IR.Expr.Lam(
                    IR.Type.Int,
                    IR.Expr.App(
                      IR.Expr.App(
                        IR.Expr.Local(
                          2,
                          IR.TypeDef(
                            List(IR.Type.Int, IR.Type.Int),
                            IR.Type.Int
                          )
                        ),
                        IR.Expr.Instr(
                          ISUB,
                          List(
                            IR.Expr.Local(1, IR.TypeDef(IR.Type.Int)),
                            IR.Expr.IntLit(1)
                          )
                        )
                      ),
                      IR.Expr.Instr(
                        IMUL,
                        List(
                          IR.Expr.Local(0, IR.TypeDef(IR.Type.Int)),
                          IR.Expr.Local(1, IR.TypeDef(IR.Type.Int))
                        )
                      )
                    )
                  )
                )
              ),
              IR.Expr.App(
                IR.Expr.App(
                  IR.Expr.Local(
                    0,
                    IR.TypeDef(List(IR.Type.Int, IR.Type.Int), IR.Type.Int)
                  ),
                  IR.Expr.Local(1, IR.TypeDef(IR.Type.Int))
                ),
                IR.Expr.IntLit(1)
              )
            )
          )
        )
      )
    )
    val jvmModule = IR.toJVM(irModule)
    println(jvmModule)
    JVM.generateBytecode(jvmModule)
