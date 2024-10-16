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
    case EId(id: Id)
  import EnvEntry.*

  private type Env = List[EnvEntry]

  private def compile(arity: Int, tm: S.CTm)(implicit out: Out): Tm =
    val env = (0 until arity).map(x => EVal(Var(mkLvl(x)))).reverse.toList
    val dom = mkLvl(arity)
    go(dom, dom, env, tm)._2

  // true = in tail call position, false = not in tail call position
  // not in the map means the variable did not occur
  private type TCMap = Map[Lvl, Boolean]

  private def merge(a: TCMap, b: TCMap): TCMap =
    (a.keySet ++ b.keySet).foldLeft(Map.empty) { (m, k) =>
      (a.get(k), b.get(k)) match
        case (None, None)           => m
        case (Some(tc), None)       => m + (k -> tc)
        case (None, Some(tc))       => m + (k -> tc)
        case (Some(tc1), Some(tc2)) => m + (k -> (tc1 && tc2))
    }

  private def notInTail(vs: List[Lvl]): TCMap = vs.map(l => l -> false).toMap

  private def go(dom: Lvl, cod: Lvl, env: Env, tm: S.CTm): (TCMap, Tm) =
    inline def ix(i: Lvl): EnvEntry = env(dom.expose - i.expose - 1)
    def ixV(i: Lvl): Tm =
      ix(i) match
        case EVal(tm) => tm
        case EId(id)  => impossible()
    tm match
      case C.Ret(lvl) => (Map(lvl -> true), ixV(lvl))
      case C.If(c, rt, t, f) =>
        val (mt, tt) = go(dom, cod, env, t)
        val (mf, ff) = go(dom, cod, env, f)
        val tc = merge(merge(Map(c -> false), mt), mf)
        // TODO: join points for branches, or maybe handle that in normalization?
        (tc, If(ixV(c), tt, ff))
      case C.CaseNat(scrut, rt, z, s) =>
        val (mz, zz) = go(dom, cod, env, z)
        val (ms, ss) = go(dom + 1, cod + 1, EVal(Var(cod)) :: env, s)
        val tc = merge(merge(Map(scrut -> false), mz), ms - dom)
        // TODO: join points for branches
        (tc, CaseNat(ixV(scrut), zz, ss))
      case C.Let(u, v, b) =>
        inline def inl(tc: TCMap, v: Tm): (TCMap, Tm) =
          val (tc2, bb) = go(dom + 1, cod, EVal(v) :: env, b)
          // TODO: is this merge correct if we inline?
          (merge(tc, tc2), bb)
        inline def cont(tc: TCMap, v: Tm): (TCMap, Tm) =
          if u < 2 then inl(tc, v)
          else
            val (tc2, body) = go(dom + 1, cod + 1, EVal(Var(cod)) :: env, b)
            // TODO: handle join points
            (merge(tc, tc2 - dom), Let(v, body))
        v match
          case V.App(fn, args) =>
            ix(fn) match
              case EId(id) =>
                cont(notInTail(fn :: args), Gen(id, args.map(ixV)))
              case _ => impossible()
          case V.Global(x, args) =>
            cont(notInTail(args), Global(x, args.map(ixV)))

          case V.Con(Name("True"), Nil)      => inl(Map.empty, True)
          case V.Con(Name("False"), Nil)     => inl(Map.empty, False)
          case V.Con(Name("Z"), Nil)         => inl(Map.empty, NatZ)
          case V.Con(Name("S"), l @ List(a)) => cont(notInTail(l), NatS(ixV(a)))
          case V.Con(_, _)                   => impossible()

          case V.Lam(ty, b) => ???
          case V.Rec(ty, b) => ???
