import surface.Parser.parse
import common.Debug.*
import core.State
import core.Evaluation
import core.Elaboration
import core.Elaboration.*
import core.Ctx
import optimization.Normalization2

import scala.io.Source
import scala.util.Using
import parsley.{Success, Failure}

object Main:
  @main def run(): Unit =
    val filename = "test.txt"
    setDebug(false)
    val etimeStart = System.nanoTime()
    val text = Using(Source.fromFile(filename)) { source =>
      source.mkString
    }.get
    parse(text) match
      case Failure(err) => println(s"syntax error at $err")
      case Success(sdefs) =>
        val state = new State
        implicit val evaluation = new Evaluation(state)
        val elaboration = new Elaboration(evaluation)
        try elaboration.elaborate(sdefs)
        catch
          case err: ElaborateError =>
            println(err.getMessage)
            val (line, col) = err.pos
            if line > 0 && col > 0 then
              val stream = Source.fromFile(filename)
              val lineSrc = stream.getLines.toSeq(line - 1)
              stream.close()
              println(lineSrc)
              println(s"${" " * (col - 1)}^")
              println(s"in ${filename}:$line:$col")
            if isDebug then err.printStackTrace()
        println()
        implicit val ctx: Ctx = Ctx.empty((0, 0))
        state
          .getMetas()
          .foreach((m, t, v) =>
            v match
              case None => println(s"?$m : ${ctx.pretty1(t)}")
              case Some(v) =>
                println(s"?$m : ${ctx.pretty1(t)} = ${ctx.pretty1(v)}")
          )
        println()
        state.allGlobals.foreach {
          case State.GlobalEntry.GlobalEntry0(x, tm, ty, cv, vv, vty, vcv) =>
            /*println(
              s"def $x : ${ctx.pretty1(vty)} := ${ctx.pretty0(tm)}"
            )*/
            println(
              s"def $x : ${ctx.pretty1(vty)} := ${ctx.pretty0(evaluation.stage(tm))}"
            )
          case State.GlobalEntry.GlobalEntry1(x, tm, ty, vv, vty) =>
            println(
              s"def $x : ${ctx.pretty1(vty)} = ${ctx.pretty1(tm)}"
            )
          case State.GlobalEntry.GlobalEntryNative(x, ty, vty) =>
            println(s"native $x : ${ctx.pretty1(vty)}")
        }

        // normalization
        println()
        val ndefs = Normalization2.normalize(state)
        ndefs.foreach(println)
      /*
        println()
        val ndefs = Normalization.normalize(state)
        ndefs.foreach(println)
        println()
        val (store, odefs) = Optimization.optimize(ndefs)
        store.foreachEntry { case (id, (k, t)) => println(s"$id -> ($k) $t") }
        odefs.foreach(println)
        println()
        val cdefs = Compilation.compile(store, odefs)
        cdefs.foreach(println)
       */
    val etime = System.nanoTime() - etimeStart
    println(s"elaboration time: ${etime / 1000000}ms (${etime}ns)")
