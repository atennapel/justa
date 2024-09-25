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

    case True
    case False
    case NatZ
    case NatS(pred: Tm)

    override def toString: String = this match
      case Var(lvl)        => s"'$lvl"
      case Global(x, Nil)  => s"$x"
      case Global(x, args) => s"$x${args.mkString("(", ", ", ")")}"
      case Gen(x, args)    => s"$x${args.mkString("(", ", ", ")")}"
      case Let(v, b)       => s"(let $v; $b)"
      case Join(v, b)      => s"(join $v; $b)"
      case JoinRec(v, b)   => s"(join rec $v; $b)"
      case Jump(lvl, args) => s"'$lvl${args.mkString("(", ", ", ")")}"
      case If(c, t, f)     => s"(if $c then $t else $f)"
      case True            => "True"
      case False           => "False"
      case NatZ            => "Z"
      case NatS(pred)      => s"S($pred)"
  export Tm.*

  private type Out = mutable.Map[Id, (TDef, Tm)]

  private def addDef(id: Id, ty: TDef, tm: Tm)(implicit out: Out): Id =
    out.find(e => e._2._1 == ty && e._2._2 == tm) match
      case None =>
        out += (id -> (ty, tm))
        id
      case Some((id, _)) => id

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
      case S.Def(x, ty, tm) => DDef(x, ty, compile(store, ty.arity, tm))

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
        case C.Ret(lvl) => ixV(lvl)
        case C.If(c, ty, clos1, clos2) =>
          def handleClos(c: S.Closure): Tm =
            c match
              case S.Closure(xs, rs, id) =>
                val (k, body) = store(id)
                val extraArgsVals =
                  xs.map(x => (x, rs(x._1)))
                    .toList
                    .sortBy((_, y) => y.expose)
                val extraArgs = extraArgsVals.map(_._1._1)
                val extraTypes = extraArgsVals.map(x => x._1._2._2.ty)
                val cbody = compile(store, 0, body, extraArgs.size)
                val funTy = TDef(extraTypes, ty)
                Gen(addDef(id, funTy, cbody), extraArgs.map(ixV))
          val tm1 = handleClos(clos1)
          val tm2 = handleClos(clos2)
          If(ixV(c), tm1, tm2)
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
              val (k, body) = store(id)
              val extraArgsVals =
                xs.map(x => (x, rs(x._1)))
                  .toList
                  .sortBy((_, y) => y.expose)
              val extraArgs = extraArgsVals.map(_._1._1)
              val extraTypes = extraArgsVals.map(x => x._1._2._2.ty)
              val cbody = compile(store, ty.arity, body, extraArgs.size)
              val funTy = TDef(ty.ps ++ extraTypes, ty.rt)
              val fid = addDef(id, funTy, cbody)
              go(dom + 1, cod, b, EId(fid, extraArgs) :: env)
            case V.Rec(ty, S.Closure(xs, rs, id)) =>
              val (k, body) = store(id)
              val extraArgsVals =
                xs.map(x => (x, rs(x._1)))
                  .toList
                  .sortBy((_, y) => y.expose)
              val extraArgs = extraArgsVals.map(_._1._1)
              val extraTypes = extraArgsVals.map(x => x._1._2._2.ty)
              val cbody =
                compile(store, ty.arity, body, extraArgs.size, Some(id))
              val funTy = TDef(ty.ps ++ extraTypes, ty.rt)
              val fid = addDef(id, funTy, cbody)
              go(dom + 1, cod, b, EId(fid, extraArgs) :: env)
    val realArity = arity + free
    val env = (0 until realArity)
      .map(x => EVal(Var(mkLvl(x))))
      .reverse
      .toList
    val dom = mkLvl(realArity)
    go(dom, dom, tm, env)
