package compilation

import common.Common.*

object Syntax:
  enum Ty:
    case TNat
    case TBool
    case TList(ty: Ty)

    override def toString: String = this match
      case TNat     => "Nat"
      case TBool    => "Bool"
      case TList(t) => s"List($t)"
  export Ty.*

  final case class TDef(ps: List[Ty], rt: Ty):
    override def toString: String = s"${ps.mkString("(", ", ", ")")} -> $rt"
    def arity: Int = ps.size
    def ty: Ty = if ps.isEmpty then rt else impossible()
    def drop(n: Int): TDef = TDef(ps.drop(n), rt)
  object TDef:
    def apply(t: Ty): TDef = TDef(Nil, t)
    def apply(t: Ty, rt: TDef): TDef = TDef(t :: rt.ps, rt.rt)
    def apply(t: Ty, rt: Ty): TDef = TDef(List(t), rt)
    def apply(ps: List[Ty], rt: TDef): TDef = TDef(ps ++ rt.ps, rt.rt)

  final case class Def(x: Name, ty: TDef, value: Tm):
    override def toString: String = s"def $x : $ty = $value"

  enum Val:
    case App(fn: Lvl, args: List[Lvl])
    case Global(x: Name, args: List[Lvl])
    case Con(x: Name, args: List[Lvl])
    case Lam(ty: TDef, body: Tm)
    case Rec(ty: TDef, body: Tm)

    override def toString: String = this match
      case App(fn, args) =>
        s"'$fn${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Global(x, args) =>
        s"$x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Con(x, Nil) => x.toString
      case Con(x, args) =>
        s"$x${args.map(x => s"'$x").mkString("(", ", ", ")")}"
      case Lam(ty, body) => s"\\($ty). $body"
      case Rec(ty, body) => s"\\rec ($ty). $body"

  export Val.*

  enum Tm:
    case Ret(lvl: Lvl)
    case Let(value: Val, body: Tm)
    case If(cond: Lvl, rt: Ty, ifTrue: Tm, ifFalse: Tm)

    override def toString: String = this match
      case Ret(lvl)       => s"'$lvl"
      case Let(v, b)      => s"let $v; $b"
      case If(c, _, t, f) => s"if '$c then $t else $f"

  export Tm.*
