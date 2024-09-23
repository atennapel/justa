package compilation

import common.Common.*
import optimization.Optimization2 as S
import optimization.Optimization2.CTm as C
import optimization.Optimization2.Val as V
import optimization.Syntax as ST
import Syntax.*

import scala.collection.mutable

object Compilation2:
  private type Id = Int
  private type Out = mutable.Map[Id, (TDef, Tm)]

  private def addDef(id: Id, ty: TDef, tm: Tm)(implicit out: Out): Unit =
    out += (id -> (ty, tm))

  def compile(store: S.ClosureStore, ds: List[S.Def]): List[Def] =
    implicit val out: Out = mutable.Map.empty
    val cds = ds.map(compile(store, _))
    val gds = out.toList.map { case (id, (ty, b)) =>
      DGen(id, ty, b)
    }
    cds ++ gds

  private def compile(store: S.ClosureStore, d: S.Def)(implicit
      out: Out
  ): Def =
    d match
      case S.Def(x, ty, tm) =>
        val cty = goTDef(ty)
        DDef(x, cty, compile(store, cty.arity, tm))

  private enum EnvEntry:
    case EVal(tm: Tm)
    case EId(id: Id, args: List[Lvl])
    case ERec(id: Id)
  import EnvEntry.*

  private def compile(
      store: S.ClosureStore,
      arity: Int,
      tm: S.CTm,
      free: Int = 0,
      rec: Option[Id] = None
  )(implicit
      out: Out
  ): Tm =
    def go(
        dom: Lvl,
        cod: Lvl,
        tm: S.CTm,
        env: List[EnvEntry]
    ): Tm =
      def ix(i: Lvl): EnvEntry =
        rec match
          case Some(id) =>
            if i.expose == 0 then ERec(id)
            else env(dom.expose - i.expose)
          case _ => env(dom.expose - i.expose - 1)
      def ixV(i: Lvl): Tm =
        ix(i) match
          case EVal(tm) => tm
          case _        => impossible()
      tm match
        case C.Ret(lvl)    => ixV(lvl)
        case C.If(c, t, f) => ???
        case C.Let(u, v, b) =>
          inline def inl(v: Tm): Tm =
            go(dom + 1, cod, b, EVal(v) :: env)
          inline def cont(v: Tm): Tm =
            if u == 1 then inl(v)
            else
              val body = go(dom + 1, cod + 1, b, EVal(Var(cod)) :: env)
              Let(v, body)
          v match
            case V.App(fn, args) =>
              ix(fn) match
                case EVal(tm) => impossible()
                case ERec(id) => cont(Gen(id, args.map(ixV)))
                case EId(id, extraArgs) =>
                  cont(Gen(id, (args ++ extraArgs).map(ixV)))
            case V.Global(x, args)         => cont(Global(x, args.map(ixV)))
            case V.Con(Name("True"), Nil)  => inl(True)
            case V.Con(Name("False"), Nil) => inl(False)
            case V.Con(Name("Z"), Nil)     => inl(NatZ)
            case V.Con(Name("S"), List(a)) => cont(NatS(ixV(a)))
            case V.Con(_, _)               => impossible()
            case V.Lam(ty, clos @ S.Closure(xs, rs, id)) =>
              println(ty)
              println(clos)
              val (k, body) = store(id)
              val extraArgsVals =
                xs.map(x => (x, rs.get(x._1).getOrElse(x._1)))
                  .toList
                  .sortBy((_, y) => y.expose)
              val extraArgs = extraArgsVals.map(_._1._1)
              val extraTypes = extraArgsVals.map(x => goTy(x._1._2._2.ty))
              val cbody = compile(store, ty.arity, body, extraArgs.size)
              val origTy = goTDef(ty)
              val funTy = TDef(origTy.ps ++ extraTypes, origTy.rt)
              addDef(id, funTy, cbody)
              go(dom + 1, cod, b, EId(id, extraArgs) :: env)
            case V.Rec(ty, S.Closure(xs, rs, id)) =>
              val (k, body) = store(id)
              val extraArgsVals =
                xs.map(x => (x, rs(x._1)))
                  .toList
                  .sortBy((_, y) => y.expose)
              val extraArgs = extraArgsVals.map(_._1._1)
              val extraTypes = extraArgsVals.map(x => goTy(x._1._2._2.ty))
              val cbody =
                compile(store, ty.arity, body, extraArgs.size, Some(id))
              val origTy = goTDef(ty)
              val funTy = TDef(origTy.ps ++ extraTypes, origTy.rt)
              addDef(id, funTy, cbody)
              go(dom + 1, cod, b, EId(id, extraArgs) :: env)
    val realArity = arity + free
    val env = (0 until realArity)
      .map(x => EVal(Var(mkLvl(x))))
      .reverse
      .toList
    val dom = mkLvl(realArity)
    go(dom, dom, tm, env)

  private def goTDef(t: ST.TDef): TDef = TDef(t.ps.map(goTy), goTy(t.rt))

  private def goTy(t: ST.Ty): Ty = t match
    case ST.TNative(Name("Bool"), Nil) => TBool
    case ST.TNative(Name("Nat"), Nil)  => TNat
    case _                             => impossible()
