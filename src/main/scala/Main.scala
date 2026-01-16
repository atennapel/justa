import Common.{Name, PosInfo}

import java.io.File
import java.nio.file.{FileSystems, Files, Path}
import scala.jdk.CollectionConverters.*

object Main:
  private val PathToLib = "lib"

  @main def run(): Unit =
    Debug.setDebug(false)
    Util.time("all") {
      try
        val root = FileSystems.getDefault.getPath(PathToLib)
        val files = allSourceFiles(root).map(p => (p, moduleName(root, p)))
        val modules = Util.time("parsing") {
          files.flatMap((p, m) => parse(m, Files.readString(p)))
        }
        val orderedModules = Util.time("module ordering") {
          orderModules(modules)
        }
        Util.time("elaboration") { elaborate(orderedModules, files) }
        val irModules = Util.time("unstaging") { Unstaging.unstageState() }
        val simpModules = Util.time("simplification") {
          Simplification.simplifyModules(irModules)
        }
        val jvmModules = Util.time("lifting") {
          Lifting.liftModules(simpModules)
        }
        jvmModules.foreach { m =>
          println(m)
          println()
        }
      catch
        case err: Throwable =>
          System.err.println(err.getMessage)
          if (Debug.isDebug) err.printStackTrace()
    }

  // helpers
  private def parse(m: String, text: String): Option[Surface.Module] =
    try Parser.parseModule(m, text)
    catch
      case err: Lexer.LexerError =>
        val pos = err.pos
        System.err.println(err.getMessage)
        System.err.println(s"in $m at $pos")
        System.err.println(showPos(text, pos))
        throw err
      case err: Parser.ParseError =>
        val pos = err.pos
        System.err.println(err.getMessage)
        System.err.println(s"in $m at $pos")
        System.err.println(showPos(text, pos))
        throw err

  private def elaborate(
      ms: Seq[Surface.Module],
      files: Seq[(Path, String)]
  ): Unit =
    try Elaboration.elaborate(ms)
    catch
      case err: Elaboration.ElaborateError =>
        val pos = err.pos
        val m = err.module.expose
        System.err.println(err.getMessage)
        System.err.println(s"in $m at $pos")
        files.find((_, m2) => m == m2) match
          case None => ()
          case Some((p, _)) =>
            System.err.println(showPos(Files.readString(p), pos))
        throw err

  private def showPos(text: String, pos: PosInfo): String =
    if pos.line < 1 || pos.column < 1 then ""
    else
      val line = text.lines.toArray.apply(pos.line - 1)
      val indicator = " " * (pos.column - 1)
      s"$line\n$indicator^"

  // util
  private inline def err(msg: String): Nothing =
    throw new RuntimeException(msg)

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

  private def allSourceFiles(path: Path): Seq[Path] =
    Files
      .list(path)
      .iterator()
      .asScala
      .flatMap { p =>
        if Files.isRegularFile(p) && p.toFile.getName.endsWith(".justa") then
          Seq(p)
        else if Files.isDirectory(p) then allSourceFiles(p)
        else Seq.empty
      }
      .toSeq

  private def orderModules(
      modules: Seq[Surface.Module]
  ): Seq[Surface.Module] =
    val all = modules.map(_.name).toSet
    modules.foreach {
      case Surface.Module(_, x, deps, _, _, _)
          if deps.exists(x => !all.contains(x)) =>
        err(
          s"unknown module in dependencies of module $x: ${deps.filter(!all.contains(_)).mkString(", ")}"
        )
      case _ => ()
    }
    def go(
        modules: Seq[Surface.Module],
        available: Set[Name]
    ): Seq[Surface.Module] =
      if modules.isEmpty then Seq.empty
      else
        modules.zipWithIndex.find((m, _) =>
          m.deps.forall(available.contains)
        ) match
          case None => err(s"failed to resolve module dependency cycle")
          case Some((m, i)) =>
            m +: go(modules.patch(i, Seq.empty, 1), available + m.name)
    go(modules, Set.empty)
