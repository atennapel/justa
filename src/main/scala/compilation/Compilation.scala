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
      DGen(id, ty, b)
    }
    cds ++ gds

  private def compile(store: S.ClosureStore, d: S.CDef)(implicit
      out: Out
  ): Def =
    d match
      case S.DDef(x, ty, tm) =>
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
        lets: List[(Int, S.VLetEntry)],
        ret: Lvl,
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
      lets match
        case Nil => ixV(ret)
        case (u, l) :: next =>
          inline def inl(v: Tm): Tm =
            go(dom + 1, cod, next, ret, EVal(v) :: env)
          inline def cont(v: Tm): Tm =
            if u == 1 then inl(v)
            else
              Let(
                v,
                go(dom + 1, cod + 1, next, ret, EVal(Var(cod)) :: env)
              )
          l match
            case S.LetGlobal(x, args) => cont(Global(x, args.map(ixV)))
            case S.LetApp(fn, args) =>
              ix(fn) match
                case EVal(tm) => impossible()
                case ERec(id) => cont(Gen(id, args.map(ixV)))
                case EId(id, extraArgs) =>
                  cont(Gen(id, (args ++ extraArgs).map(ixV)))
            case S.LetLam(ty, (xs, rs, id)) =>
              val (k, body) = store(id)
              val extraArgsVals =
                xs.map(x => (x, rs(x._1)))
                  .toList
                  .sortBy((_, y) => y.expose)
              val extraArgs = extraArgsVals.map(_._1._1)
              val extraTypes = extraArgsVals.map(x => goTy(x._1._2._2.ty))
              val cbody = compile(store, ty.arity, body, extraArgs.size)
              val origTy = goTDef(ty)
              val funTy = TDef(origTy.ps ++ extraTypes, origTy.rt)
              addDef(id, funTy, cbody)
              go(dom + 1, cod, next, ret, EId(id, extraArgs) :: env)
            case S.LetRecLam(ty, (xs, rs, id)) =>
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
              go(dom + 1, cod, next, ret, EId(id, extraArgs) :: env)
            case S.LetNative(Name("True"), Nil)  => inl(True)
            case S.LetNative(Name("False"), Nil) => inl(False)
            case S.LetNative(Name("Z"), Nil)     => inl(NatZ)
            case S.LetNative(Name("S"), List(a)) => cont(NatS(ixV(a)))
            case S.LetNative(_, _)               => impossible()
    val S.Tm(lets, ret) = tm
    val realArity = arity + free
    val env = (0 until realArity)
      .map(x => EVal(Var(mkLvl(x))))
      .reverse
      .toList
    val dom = mkLvl(realArity)
    go(dom, dom, lets, ret, env)

  private def goTDef(t: S.TDef): TDef = TDef(t.ps.map(goTy), goTy(t.rt))

  private def goTy(t: S.Ty): Ty = t match
    case S.TNative(Name("Bool"), Nil) => TBool
    case S.TNative(Name("Nat"), Nil)  => TNat
    case _                            => impossible()
