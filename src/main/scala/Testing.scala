import scala.annotation.tailrec

// eta-expansion, inlining, let-flattening
object Testing:
  type Ix = Int
  private type Lvl = Int

  enum Ty derives CanEqual:
    case Bool
    case Fun(pty: Ty, rty: Ty)

  enum Tm derives CanEqual:
    case Var(ix: Ix)
    case Lam(body: Tm)
    case App(fn: Tm, arg: Tm, argty: Ty)
    case Let(usage: Int, ty: Ty, value: Tm, body: Tm)
    case BoolLit(value: Boolean)
    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)

    override def toString: String =
      this match
        case Var(i)          => s"'$i"
        case Lam(b)          => s"(\\$b)"
        case App(f, a, _)    => s"($f $a)"
        case Let(_, _, v, b) => s"(let $v; $b)"
        case BoolLit(v)      => if v then "True" else "False"
        case If(c, t, f)     => s"(if $c then $t else $f)"

  private enum Val:
    case Var(lvl: Lvl)
    case App(fn: Val, arg: Val, argty: Ty)
    case Lam(body: Val => Val)
    case Let(ty: Ty, value: Val, body: Val => Val)
    case BoolLit(value: Boolean)
    case If(cond: Val, ifTrue: Val, ifFalse: Val)

  private type Env = List[Val]

  private def isSmall(v: Val): Boolean =
    v match
      case Val.Var(_)     => true
      case Val.BoolLit(_) => true
      case _              => false

  private def app(f: Val, a: Val, ty: Ty): Val =
    f match
      case Val.Lam(b)      => Val.Let(ty, a, b)
      case Val.If(c, t, f) => Val.If(c, app(t, a, ty), app(f, a, ty))
      case f               => Val.App(f, a, ty)

  private def let(u: Int, ty: Ty, v: Val, b: Val => Val): Val =
    if u == 0 || u == 1 || isSmall(v) then b(v)
    else
      v match
        case Val.Let(ty2, v2, b2) =>
          Val.Let(ty2, v2, v => Val.Let(ty, b2(v), b))
        case _ => Val.Let(ty, v, b)

  private def vif(c: Val, t: Val, f: Val): Val =
    c match
      case Val.BoolLit(v) => if v then t else f
      case _              => Val.If(c, t, f)

  private def eval(ty: Ty, tm: Tm, eta: Boolean = true)(using env: Env): Val =
    (ty, tm) match
      case (_, Tm.BoolLit(v))        => Val.BoolLit(v)
      case (Ty.Fun(_, r), Tm.Lam(b)) => Val.Lam(v => eval(r, b)(using v :: env))
      case (Ty.Fun(p, _), tm) if eta =>
        Val.Lam(v => app(eval(ty, tm, false), v, p))
      case (_, Tm.Var(i))       => env(i)
      case (r, Tm.App(f, a, p)) => app(eval(Ty.Fun(p, r), f), eval(p, a), p)
      case (r, Tm.Let(u, p, v, b)) =>
        let(u, p, eval(p, v), v => eval(r, b)(using v :: env))
      case (r, Tm.If(c, t, f)) => vif(eval(Ty.Bool, c), eval(r, t), eval(r, f))
      case _                   => throw new RuntimeException("impossible")

  private def quote(v: Val)(using lvl: Lvl): Tm =
    def go(v: Val)(using lvl: Lvl): (Tm, List[Int]) =
      inline def empty: List[Int] = List.fill(lvl)(0)
      inline def merge(a: List[Int], b: List[Int]): List[Int] =
        a.zip(b).map(_ + _)
      inline def body(b: Val => Val): (Tm, List[Int]) =
        go(b(Val.Var(lvl)))(using lvl + 1)
      v match
        case Val.BoolLit(v) => (Tm.BoolLit(v), empty)
        case Val.Var(k) =>
          val i = lvl - k - 1
          (Tm.Var(i), empty.updated(i, 1))
        case Val.App(f, a, ty) =>
          val (ef, uf) = go(f)
          val (ea, ua) = go(a)
          (Tm.App(ef, ea, ty), merge(uf, ua))
        case Val.Lam(b) =>
          val (eb, ub) = body(b)
          (Tm.Lam(eb), ub.tail)
        case Val.Let(p, v, b) =>
          val (ev, uv) = go(v)
          val (eb, ub) = body(b)
          (Tm.Let(ub.head, p, ev, eb), merge(uv, ub.tail))
        case Val.If(c, t, f) =>
          val (ec, uc) = go(c)
          val (et, ut) = go(t)
          val (ef, uf) = go(f)
          (Tm.If(ec, et, ef), merge(uc, merge(ut, uf)))
    go(v)._1

  private inline def normalize(ty: Ty, tm: Tm): Tm =
    quote(eval(ty, tm)(using Nil))(using 0)

  @tailrec
  def simplify(ty: Ty, tm: Tm): Tm =
    println(s"simplify $tm")
    val next = normalize(ty, tm)
    if next == tm then tm else simplify(ty, next)
