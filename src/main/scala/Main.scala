import java.nio.file.{FileSystems, Files, Path}
import scala.jdk.CollectionConverters.*
import common.Common.{Name, err}
import ir.IR
import jvm.Jvm
import surface.{Parser, Surface}
import surface.Elaboration.elaborate
import core.Unstaging.unstage

import java.io.File

object Main:
  @main def run(): Unit =
    val root = FileSystems.getDefault.getPath("examples")
    val files = allSourceFiles(root).map(p => (p, moduleName(root, p)))
    val modules = files.map((p, m) => Parser.parse(m, Files.readString(p)))
    val orderedModules = orderModules(modules)
    val coreModules = elaborate(orderedModules)
    val irModules = unstage(coreModules)
    val jvmModules = IR.toJvm(irModules)
    val target = "justatarget"
    resetDir(target)
    Jvm.generateBytecode(jvmModules, target)

  private def resetDir(target: String): Unit =
    deleteDir(Path.of(target).toFile)
    Path.of(target).toFile.mkdir()

  private def deleteDir(f: File): Unit =
    if f.isFile then f.delete()
    else if f.isDirectory then f.listFiles().foreach(deleteDir)

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
      case Surface.Module(x, deps, _, _, _)
          if deps.exists(x => !all.contains(x)) =>
        err(
          s"unknown module in dependencies of module $x: ${deps.filter(!all.contains(_)).mkString(", ")}"
        )
      case _ => ()
    }
    def go(
        modules: List[Surface.Module],
        available: Set[Name]
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
