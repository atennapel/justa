import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*

import Common.err

object Main:
  @main def run(): Unit =
    val s =
      """
module test.Factorial
import Prelude
import test.TestPackage

finite Void
finite Unit = Unit
finite Bool = False | True
data List = Nil | Cons (head : Int) (tail : List)
record Person (id : Int) (age: Int) (length : Int)

def iadd : Int -> Int -> Int = \a b => instr 96 a b

def myList : List = con Cons 1 (con Nil)
"""
    val res = Parser.parse(s)
    println(res)
    /*
    val root = FileSystems.getDefault.getPath("examples")
    val files = allSourceFiles(root).map(p => (p, moduleName(root, p)))
    val modules = files.map((p, m) => Surface.parse(m, Files.readString(p)))
    val orderedModules = orderModules(modules)
    val irModules = Surface.elaborate(orderedModules)
    val jvmModules = IR.toJvm(irModules)
    val target = "justatarget"
    resetDir(target)
    Jvm.generateBytecode(jvmModules, target)
     */

  private def resetDir(target: String): Unit =
    Path.of(target).toFile.delete()
    Path.of(target).toFile.mkdir()

  private def moduleName(root: Path, path: Path): String =
    root
      .relativize(path)
      .toFile
      .getPath
      .dropRight(6)
      .replace('/', '.')
      .replace('\\', '.')

  private def allSourceFiles(path: Path): List[Path] =
    Files
      .list(path)
      .iterator()
      .asScala
      .flatMap { p =>
        if Files.isRegularFile(p) && p.toFile.getName.endsWith(".justa") then
          List(p)
        else if Files.isDirectory(p) then allSourceFiles(p)
        else Nil
      }
      .toList

  private def orderModules(
      modules: List[Surface.Module]
  ): List[Surface.Module] =
    val all = modules.map(_.name).toSet
    modules.foreach {
      case Surface.Module(x, deps, _) if deps.exists(x => !all.contains(x)) =>
        err(
          s"unknown module in dependencies of module $x: ${deps.filter(!all.contains(_)).mkString(", ")}"
        )
      case _ => ()
    }
    def go(
        modules: List[Surface.Module],
        available: Set[Surface.Name]
    ): List[Surface.Module] =
      if modules.isEmpty then Nil
      else
        modules.zipWithIndex.find((m, _) =>
          m.deps.forall(available.contains)
        ) match
          case None         => err(s"failed to resolve module dependency cycle")
          case Some((m, i)) =>
            m :: go(modules.patch(i, Nil, 1), available + m.name)

    go(modules, Set.empty)
