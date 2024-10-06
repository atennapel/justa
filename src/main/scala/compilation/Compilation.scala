package compilation

import common.Common.*
import compilation.Optimization as S
import compilation.Optimization.CTm as C
import compilation.Optimization.Val as V
import Syntax.*

import scala.collection.mutable

object Compilation:
  type Id = Int

  enum Def:
    case DDef(name: Name, ty: TDef, tm: Tm)
    case DGen(id: Id, ty: TDef, tm: Tm)

    override def toString: String = this match
      case DDef(x, ty, tm)  => s"def $x : $ty = $tm"
      case DGen(id, ty, tm) => s"def gen $id : $ty = $tm"
  export Def.*

  enum Tm:
    case Var(lvl: Lvl)
    case Global(name: Name, args: List[Tm] = Nil)
    case Gen(id: Id, args: List[Tm])
    case Let(value: Tm, body: Tm)

    case Join(value: Tm, body: Tm)
    case JoinRec(value: Tm, body: Tm)
    case Jump(lvl: Lvl, args: List[Tm] = Nil)

    case If(cond: Tm, ifTrue: Tm, ifFalse: Tm)
    case CaseNat(scrut: Tm, z: Tm, s: Tm)

    case True
    case False
    case NatZ
    case NatS(pred: Tm)

    override def toString: String = this match
      case Var(lvl)         => s"'$lvl"
      case Global(x, Nil)   => s"$x"
      case Global(x, args)  => s"$x${args.mkString("(", ", ", ")")}"
      case Gen(x, args)     => s"$x${args.mkString("(", ", ", ")")}"
      case Let(v, b)        => s"(let $v; $b)"
      case Join(v, b)       => s"(join $v; $b)"
      case JoinRec(v, b)    => s"(join rec $v; $b)"
      case Jump(lvl, args)  => s"'$lvl${args.mkString("(", ", ", ")")}"
      case If(c, t, f)      => s"(if $c then $t else $f)"
      case CaseNat(n, z, s) => s"(caseNat $n $z $s)"
      case True             => "True"
      case False            => "False"
      case NatZ             => "Z"
      case NatS(pred)       => s"S($pred)"
  export Tm.*

  private type Out = mutable.Map[Id, (TDef, Tm)]

  private def addDef(id: Id, ty: TDef, tm: Tm)(implicit out: Out): Id =
    out.find(e => e._2._1 == ty && e._2._2 == tm) match
      case None =>
        out += (id -> (ty, tm))
        id
      case Some((id, _)) => id

  def compile(ds: List[S.Def]): List[Def] =
    implicit val out: Out = mutable.Map.empty
    val cds = ds.map(compile)
    val gds = out.toList.map { case (id, (ty, b)) =>
      DGen(id, ty, b)
    }
    cds ++ gds

  private def compile(d: S.Def)(implicit out: Out): Def =
    d match
      case S.Def(x, ty, tm) => DDef(x, ty, compile(ty.arity, tm))

  private enum EnvEntry:
    case EVal(tm: Tm)
    case EId(id: Id, args: List[Lvl])
    case ERec(id: Id)
  import EnvEntry.*

  private def compile(
      arity: Int,
      tm: S.CTm,
      free: Int = 0,
      rec: Option[Id] = None
  )(implicit
      out: Out
  ): Tm = ???
