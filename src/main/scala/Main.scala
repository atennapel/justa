object Main:
  @main def run(): Unit =
    val script =
      """
(def iadd (-> Int Int Int) (fn (a b) (instr 96 a b)))
(def imul (-> Int Int Int) (fn (a b) (instr 104 a b)))
(def isub (-> Int Int Int) (fn (a b) (instr 100 a b)))
(def izero (-> Int Boolean) (fn n (instr 0 n)))
(def fac (-> Int Int) (fn n
  (letrec go (-> Int Int) (fn n
    (if (izero n) 1 (imul n (go (isub n 1)))))
    (go n))))
(def facTR (-> Int Int) (fn n
  (letrec go (-> Int Int Int) (fn n
    (if (izero n) (fn acc acc) (fn acc (go (isub n 1) (imul n acc)))))
    (go n 1))))
      """
    val module = Surface.parse("TestModule", script)
    val irModule = Surface.elaborate(module)
    val jvmModule = IR.toJvm(irModule)
    Jvm.generateBytecode(jvmModule)
