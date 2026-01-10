import Common.PosInfo
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
      val sdefs = Parser.parse(text)
      Elaboration.elaborate(sdefs)
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
        case State.GlobalEntry.Def0(x, tm, ty, cv, vv, vty, vcv) =>
          println(
            s"def $x : ${ctx.pretty1(vty)} := ${ctx.pretty0(Evaluation.unstage(tm))}"
          )
        case State.GlobalEntry.Def1(x, tm, ty, vv, vty) =>
          println(
            s"def $x : ${ctx.pretty1(vty)} = ${ctx.pretty1(tm)}"
          )
      }
      println()
      val uds = Unstaging.unstageState()
      println(uds)
      println()
      val sds = Simplification.simplifyDefs(uds)
      println(sds)
      println()
      val jds = Lifting.liftDefs(sds)
      println(jds)
    catch
      case err: Parser.ParseError =>
        println(err.toString)
        if isDebug then err.printStackTrace()
      case err: Elaboration.ElaborateError =>
        println(err.getMessage)
        val PosInfo(line, col) = err.pos
        if line > 0 && col > 0 then
          val stream = Source.fromFile(filename)
          val lineSrc = stream.getLines.toSeq(line - 1)
          stream.close()
          println(lineSrc)
          println(s"${" " * (col - 1)}^")
          println(s"in ${filename}:$line:$col")
        if isDebug then err.printStackTrace()
    val etime = System.nanoTime() - etimeStart
    println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")
