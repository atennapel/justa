object Common:
  def impossible(): Nothing =
    throw new RuntimeException("impossible")

  def err(msg: String): Nothing =
    throw new RuntimeException(msg)
