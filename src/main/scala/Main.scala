import java.nio.file.{FileSystems, Files, Path}
import scala.jdk.CollectionConverters.*
import common.Common.{Name, err, PosInfo}
import common.Debug.setDebug
import core.Core
import ir.IR
import jvm.Jvm
import surface.{Parser, Surface}
import surface.Parser.ParseError
import surface.Elaboration
import surface.Elaboration.ElaborationError
import core.Unstaging.unstage

import java.io.File

object Main:
  @main def run(): Unit =
    setDebug(true)
    val root = FileSystems.getDefault.getPath("examples")
    val files = allSourceFiles(root).map(p => (p, moduleName(root, p)))
    val modules = files.map((p, m) => parse(m, Files.readString(p)))
    val orderedModules = orderModules(modules)
    val coreModules = elaborate(orderedModules, files)
    val irModules = unstage(coreModules)
    val jvmModules = IR.toJvm(irModules)
    val target = "justatarget"
    resetDir(target)
    Jvm.generateBytecode(jvmModules, target)

  // helpers
  private def parse(m: String, text: String): Surface.Module =
    try Parser.parse(m, text)
    catch
      case err: ParseError =>
        val pos = err.pos
        System.err.println(err.msg)
        System.err.println(s"in $m at $pos")
        System.err.println(showPos(text, pos))
        throw err

  private def elaborate(
      ms: List[Surface.Module],
      files: List[(Path, String)]
  ): List[Core.Module] =
    try Elaboration.elaborate(ms)
    catch
      case err: ElaborationError =>
        val pos = err.pos
        val m = err.module.expose
        System.err.println(err.msg)
        System.err.println(s"in $m at $pos")
        files.find((_, m2) => m == m2) match
          case None         => ()
          case Some((p, _)) =>
            System.err.println(showPos(Files.readString(p), pos))
        throw err

  private def showPos(text: String, pos: PosInfo): String =
    val line = text.lines.toArray.apply(pos.line - 1)
    val indicator = " " * (pos.column - 1)
    s"$line\n$indicator^"

  // util
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
