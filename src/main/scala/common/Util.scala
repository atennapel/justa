package common

object Util:
  inline def time[A](label: String)(inline action: A): A =
    val t = System.nanoTime()
    val res = action
    val t2 = System.nanoTime() - t
    println(s"timed $label: ${t2}ns (${t2 / 1000000}ms)")
    res
