object Util:
  private inline val EnableTiming = false

  inline def time[A](label: String)(inline action: A): A =
    inline if EnableTiming then
      val t = System.nanoTime()
      val res = action
      val t2 = System.nanoTime() - t
      println(s"timed $label: ${t2}ns (${t2 / 1000000}ms)")
      res
    else action
