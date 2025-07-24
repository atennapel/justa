object Main:
  @main def run(): Unit =
    val script =
      """
(finite Void)
(finite Unit Unit)
(finite Bool False True)

(def myBool1 (fin Bool False))
(def myBool2 (fin Bool True))
(def myBool3 Bool (fin_ False))
(def myBool4 Bool (fin_ True))

(def not (-> Bool Bool) (fn b
  (fincase b
    (True (fin_ False))
    (False (fin_ True)))))

(record Person (id Int) (age Int))

(data IntList Nil (Cons (hd Int) (tl IntList)))
(data IntOption None (Some Int))

(def myRecord1 (rec Person 123 33))
(def myRecord2 Person (rec_ 123 33))

(def myList1 (con IntList Cons 42 (con IntList Nil)))
(def myList2 IntList (con_ Cons 42 (con_ Nil)))

(def age1 (field age myRecord1))
(def age2 (field 1 myRecord1))

(def head (-> IntList IntOption) (fn l
  (case l
    (Cons (hd _) (con_ Some hd))
    (Nil (con_ None)))))

(def iadd (-> Int Int Int) (fn (a b) (instr 96 a b)))

(def incList (-> IntList IntList) (fn l
  (letrec go (-> IntList IntList) (fn l
    (case l
      (Cons (hd tl) (con_ Cons (iadd hd 1) (go tl)))
      (Nil (con_ Nil))))
    (go l))))

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
