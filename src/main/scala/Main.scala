import java.nio.file.{FileSystems, Files}
import scala.jdk.CollectionConverters.*

import Common.err

object Main:
  @main def run(): Unit =
    val dir = "examples"
    val path = FileSystems.getDefault.getPath(dir)
    val files = Files
      .list(path)
      .iterator()
      .asScala
      .toList
      .filter(Files.isRegularFile(_))
      .filter(p => p.getFileName.toFile.getName.endsWith(".justa"))
      .map(p =>
        (p.getFileName.toFile.getName.dropRight(6), Files.readString(p))
      )
    val modules = files.map((x, f) => Surface.parse(x, f))
    val orderedModules = orderModules(modules)
    val irModules = Surface.elaborate(orderedModules)
    val jvmModules = IR.toJvm(irModules)
    Jvm.generateBytecode(jvmModules, "justatarget")

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
