import Common.*

object IR:
  enum VTy:
    case Bool
    case Int

    override def toString: String = this match
      case Bool => "bool"
      case Int  => "int"

  final case class CTy(params: List[VTy], ret: VTy):
    def head: VTy = params.head
    def tail: CTy = CTy(params.tail, ret)
    def drop(n: Int): CTy = CTy(params.drop(n), ret)
    override def toString: String = s"${params.mkString("(", ",", ")")} -> $ret"
  object CTy:
    def apply(ret: VTy): CTy = CTy(Nil, ret)
    def apply(param: VTy, ret: VTy): CTy = CTy(List(param), ret)
    def apply(param: VTy, ret: CTy): CTy = CTy(param :: ret.params, ret.ret)

  final case class Defs(defs: List[Def]):
    override def toString: String = defs.mkString("\n")
    def toList: List[Def] = defs

  final case class Def(name: Name, ty: CTy, value: Tm):
    override def toString: String = s"def $name : $ty = $value"

  type LocalName = Int
  enum Tm:
    case Local(ix: LocalName, ty: CTy)
    case Global(name: Name)
    case Prim(prim: RuntimePrimitive)
    case BoolLit(value: Boolean)
    case IntLit(value: Int)

    case Let(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)
    case LetRec(name: LocalName, usage: Int, ty: CTy, value: Tm, body: Tm)

    case Lam(name: LocalName, usage: Int, ty: VTy, body: Tm)
    case App(fn: Tm, arg: Tm)

    case If(rty: CTy, cond: Tm, ifTrue: Tm, ifFalse: Tm)

    override def toString: String = this match
      case Local(ix, _)           => s"'$ix"
      case Global(x)              => s"$x"
      case Prim(p)                => s"$p"
      case BoolLit(v)             => s"$v"
      case IntLit(v)              => s"$v"
      case Let(x, _, ty, v, b)    => s"(let $x : $ty = $v; $b)"
      case LetRec(x, _, ty, v, b) => s"(let rec $x : $ty = $v; $b)"
      case Lam(x, _, ty, b)       => s"(\\($x : $ty) => $b)"
      case App(fn, arg)           => s"($fn $arg)"
      case If(_, c, t, f)         => s"(if $c then $t else $f)"

    def flattenApps: (Tm, List[Tm]) = this match
      case App(f, a) =>
        val (hd, args) = f.flattenApps
        (hd, args ++ List(a))
      case t => (t, Nil)

  object Tm:
    val True = BoolLit(true)
    val False = BoolLit(false)
    val Zero = IntLit(0)

    def bool(c: Boolean): Tm = if c then True else False
