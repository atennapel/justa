import Common.{PosInfo, Bind}
import Debug.*

import scala.io.Source
import scala.util.Using

object Main:
  @main def run(): Unit =
    val filename = "test.justa"
    setDebug(false)
    val etimeStart = System.nanoTime()
    val text = Using(Source.fromFile(filename)) { source =>
      source.mkString
    }.get
    try
      val sdefs = Parser.parseModule("test", text).get.defs
      println(sdefs)
      println()
      Util.time("elaboration") {
        Elaboration.elaborate(sdefs)
      }
      println()
      given ctx: Ctx = Ctx.empty(PosInfo.start)
      State.getMetas().foreach { (m, t, v) =>
        v match
          case None => println(s"?$m : ${ctx.pretty1(t)}")
          case Some(v) =>
            println(s"?$m : ${ctx.pretty1(t)} = ${ctx.pretty1(v)}")
      }
      println()
      State.allGlobals.foreach {
        case State.GlobalEntry.Def0(x, tm, _, _, _, vty, _) =>
          println(
            s"def $x : ${ctx.pretty1(vty)} := ${ctx.pretty0(tm)}"
          )
        case State.GlobalEntry.Def1(x, tm, _, _, vty) =>
          println(
            s"def $x : ${ctx.pretty1(vty)} = ${ctx.pretty1(tm)}"
          )
        case State.GlobalEntry.Data(x, Nil, _, _, _, _) => println(s"data $x")
        case State.GlobalEntry.Data(x, ps, _, _, _, _) =>
          println(s"data $x ${ps.mkString(" ")}")
        case State.GlobalEntry.Con(x, _, Nil, _, _, _, _, _) => println(s"| $x")
        case State.GlobalEntry.Con(x, tps0, ps, _, _, _, _, _) =>
          val tps = tps0.map(x => Bind.DoBind(x))
          println(
            s"| $x ${ps.map((x, t) => s"($x : ${Pretty.pretty1(t)(using tps)})").mkString(" ")}"
          )
      }
      println()
      val uds = Util.time("unstaging") { Unstaging.unstageState() }
      println(uds)
      println()
      val sds = Util.time("simplification") { Simplification.simplifyDefs(uds) }
      println(sds)
      println()
      val jds = Util.time("lifting") { Lifting.liftDefs(sds) }
      println(jds)
    catch
      case err: Lexer.LexerError =>
        println(err.toString)
        showPos(err.pos, filename)
        if isDebug then err.printStackTrace()
      case err: Parser.ParseError =>
        println(err.toString)
        showPos(err.pos, filename)
        if isDebug then err.printStackTrace()
      case err: Elaboration.ElaborateError =>
        println(err.getMessage)
        showPos(err.pos, filename)
        if isDebug then err.printStackTrace()
    val etime = System.nanoTime() - etimeStart
    println(s"total time: ${etime / 1000000}ms (${etime}ns)")

  private def showPos(pos: PosInfo, filename: String): Unit =
    val PosInfo(line, col) = pos
    if line > 0 && col > 0 then
      val stream = Source.fromFile(filename)
      val lineSrc = stream.getLines.toSeq(line - 1)
      stream.close()
      println(lineSrc)
      println(s"${" " * (col - 1)}^")
      println(s"in ${filename}:$line:$col")
