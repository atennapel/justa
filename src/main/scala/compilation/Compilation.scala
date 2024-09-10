package compilation

import common.Common.*
import optimization.Syntax as S
import Syntax.*

import scala.collection.mutable

object Compilation:
  private type Id = Int
  private type Out = mutable.Map[Id, (TDef, Tm)]

  private def addDef(id: Id, ty: TDef, tm: Tm)(implicit out: Out): Unit =
    out += (id -> (ty, tm))

  def compile(store: S.ClosureStore, ds: List[S.CDef]): List[Def] =
    implicit val out: Out = mutable.Map.empty
    val cds = ds.map(compile(store, _))
    val gds = out.toList.map { case (id, (ty, b)) =>
      DDef(Name(s"$$$id"), ty, b)
    }
    cds ++ gds

  private def compile(store: S.ClosureStore, d: S.CDef)(implicit
      out: Out
  ): Def =
    d match
      case S.DDef(x, ty, tm) =>
        val cty = goTDef(ty)
        DDef(x, cty, compile(store, cty.arity, tm))

  private def compile(store: S.ClosureStore, arity: Int, tm: S.CTm)(implicit
      out: Out
  ): Tm =
    def go(
        dom: Lvl,
        cod: Lvl,
        lets: List[(Int, S.VLetEntry)],
        ret: Lvl,
        env: List[Tm],
        fns: Map[Lvl, Id]
    ): Tm =
      inline def ix(i: Lvl): Tm = env(dom.expose - i.expose - 1)
      lets match
        case Nil => ix(ret)
        case (u, l) :: next =>
          inline def inl(v: Tm): Tm = go(dom + 1, cod, next, ret, v :: env, fns)
          inline def cont(v: Tm): Tm =
            if u == 1 then inl(v)
            else Let(v, go(dom + 1, cod + 1, next, ret, Var(cod) :: env, fns))
          l match
            case S.LetGlobal(x, args) => cont(Global(x, args.map(ix)))
            case S.LetApp(fn, args) =>
              cont(Global(Name(s"$$${fns(fn)}"), args.map(ix)))
            case S.LetLam(ty, (xs, id)) =>
              val (k, body) = store(id)
              val cbody = compile(store, ty.arity, body)
              addDef(id, goTDef(ty), cbody)
              go(dom + 1, cod, next, ret, env, fns + (dom -> id))
            case S.LetRecLam(ty, body)           => ???
            case S.LetNative(Name("True"), Nil)  => inl(True)
            case S.LetNative(Name("False"), Nil) => inl(False)
            case S.LetNative(Name("Z"), Nil)     => inl(NatZ)
            case S.LetNative(Name("S"), List(a)) => cont(NatS(ix(a)))
            case S.LetNative(_, _)               => impossible()
    val S.Tm(lets, ret) = tm
    val env = (0 until arity).map(x => Var(mkLvl(x))).reverse.toList
    val dom = mkLvl(arity)
    go(dom, dom, lets, ret, env, Map.empty)

  private def goTDef(t: S.TDef): TDef = TDef(t.ps.map(goTy), goTy(t.rt))

  private def goTy(t: S.Ty): Ty = t match
    case S.TNative(Name("Bool"), Nil) => TBool
    case S.TNative(Name("Nat"), Nil)  => TNat
    case _                            => impossible()
