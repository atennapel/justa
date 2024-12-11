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
    case Let(usage: Int, value: Val, body: Tm)
    case If(cond: Lvl, rt: Ty, ifTrue: Tm, ifFalse: Tm)
    case CaseNat(scrut: Lvl, rt: Ty, z: Tm, s: Tm)

    override def toString: String = this match
      case Ret(lvl)            => s"'$lvl"
      case Let(u, v, b)        => s"let $v; $b"
      case If(c, rt, t, f)     => s"if '$c then $t else $f"
      case CaseNat(n, _, z, s) => s"caseNat '$n $z $s"
  export Tm.*

  private enum ITm:
    case IVar(lvl: Lvl, args: List[ITm] = Nil)
    case IGlobal(name: Name, args: List[ITm] = Nil)
    case ICon(name: Name, args: List[ITm] = Nil)
    case ILet(tail: Boolean, value: ITm, body: ITm)
    case ILetLam(tail: Boolean, ty: TDef, lambody: ITm, body: ITm)
    case ILetRec(tail: Boolean, ty: TDef, recbody: ITm, body: ITm)
    case IIf(cond: ITm, ifTrue: ITm, ifFalse: ITm)
    case ICaseNat(scrut: ITm, z: ITm, s: ITm)

    override def toString: String = this match
      case IVar(lvl, Nil)       => s"'$lvl"
      case IVar(lvl, args)      => s"'$lvl${args.mkString("(", ", ", ")")}"
      case IGlobal(x, Nil)      => s"$x"
      case IGlobal(x, args)     => s"$x${args.mkString("(", ", ", ")")}"
      case ICon(x, Nil)         => s"$x"
      case ICon(x, args)        => s"$x${args.mkString("(", ", ", ")")}"
      case ILet(t, v, b)        => s"(let $t $v; $b)"
      case ILetLam(t, ty, v, b) => s"(letlam $t $ty ($v); $b)"
      case ILetRec(t, ty, v, b) => s"(letrec $t $ty ($v); $b)"
      case IIf(c, t, f)         => s"(if $c then $t else $f)"
      case ICaseNat(n, z, s)    => s"(caseNat $n $z $s)"
  import ITm.*

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

  private def compile(arity: Int, tm: S.CTm)(implicit out: Out): Tm =
    val env = (0 until arity).map(x => IVar(mkLvl(x))).reverse.toList
    val dom = mkLvl(arity)
    val (_, itm) = go(dom, dom, env, true, tm)
    println(itm)
    ???

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

  private def go(
      dom: Lvl,
      cod: Lvl,
      env: List[ITm],
      tail: Boolean,
      tm: S.CTm
  ): (TCMap, ITm) =
    inline def ix(i: Lvl): ITm = env(dom.expose - i.expose - 1)
    tm match
      case C.Ret(lvl) => (Map(lvl -> tail), ix(lvl))
      case C.If(c, rt, t, f) =>
        val (mt, tt) = go(dom, cod, env, tail, t)
        val (mf, ff) = go(dom, cod, env, tail, f)
        val tc = merge(merge(Map(c -> false), mt), mf)
        // TODO: join points for branches, or maybe handle that in normalization?
        (tc, IIf(ix(c), tt, ff))
      case C.CaseNat(scrut, rt, z, s) =>
        val (mz, zz) = go(dom, cod, env, tail, z)
        val (ms, ss) = go(dom + 1, cod + 1, IVar(cod) :: env, tail, s)
        val tc = merge(merge(Map(scrut -> false), mz), ms - dom)
        // TODO: join points for branches
        (tc, ICaseNat(ix(scrut), zz, ss))
      case C.Let(u, v, b) =>
        inline def inl(tc: TCMap, v: ITm): (TCMap, ITm) =
          val (tc2, bb) = go(dom + 1, cod, v :: env, tail, b)
          // TODO: is this merge correct if we inline?
          (merge(tc, tc2), bb)
        inline def cont(tc: TCMap, v: ITm): (TCMap, ITm) =
          if u < 2 then inl(tc, v)
          else
            val (tc2, body) =
              go(dom + 1, cod + 1, IVar(cod) :: env, tail, b)
            val isTail = tc2(dom)
            (merge(tc, tc2 - dom), ILet(isTail, v, body))
        v match
          case V.App(fn, args) =>
            ix(fn) match
              case IVar(lvl, Nil) =>
                cont(
                  Map(fn -> tail) ++ notInTail(args),
                  IVar(lvl, args.map(ix))
                )
              case _ => impossible()
          case V.Global(x, args) =>
            cont(notInTail(args), IGlobal(x, args.map(ix)))

          case V.Con(x, Nil)  => inl(Map.empty, ICon(x))
          case V.Con(x, args) => cont(notInTail(args), ICon(x, args.map(ix)))

          case V.Lam(ty, lb) =>
            println(s"let $u $tail lam $ty $b")
            val arity = ty.arity
            val env2 =
              (0 until arity)
                .map(x => IVar(mkLvl(x + dom.expose)))
                .reverse
                .toList
            val lamvars = (0 until arity).map(mkLvl).toSet
            val (tc1, lambody) =
              go(dom + arity, cod + arity, env2 ++ env, tail, lb)
            val (tc2, body) =
              go(dom + 1, cod + 1, IVar(cod) :: env, tail, b)
            (
              merge(tc1 -- lamvars, tc2 - dom),
              ILetLam(tc2(dom), ty, lambody, body)
            )
          case V.Rec(ty, b) => ???
