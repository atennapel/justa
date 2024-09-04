package compilation

import common.Common.*
import optimization.Syntax as S
import Syntax.*
import optimization.Syntax.LetEntry

object Compilation:
  def compile(store: S.ClosureStore, ds: List[S.CDef]): List[Def] =
    ds.map(compile(store, _))

  private def compile(store: S.ClosureStore, d: S.CDef): Def =
    d match
      case S.DDef(x, ty, tm) =>
        val cty = go(ty)
        DDef(x, cty, compile(store, cty.arity, tm))

  private def compile(store: S.ClosureStore, arity: Int, tm: S.CTm): Tm =
    def go(
        dom: Lvl,
        cod: Lvl,
        lets: List[(Int, S.VLetEntry)],
        ret: Lvl,
        env: List[Tm]
    ): Tm =
      inline def ix(i: Lvl): Tm = env(dom.expose - i.expose - 1)
      lets match
        case Nil => ix(ret)
        case (u, l) :: next =>
          inline def inl(v: Tm): Tm = go(dom + 1, cod, next, ret, v :: env)
          inline def cont(v: Tm): Tm =
            if u == 1 then inl(v)
            else Let(v, go(dom + 1, cod + 1, next, ret, Var(cod) :: env))
          l match
            case S.LetGlobal(x, args) => cont(Global(x, args.map(ix)))
            case S.LetApp(fn, args)   => ???
            case S.LetLam(ty, (xs, id)) =>
              val (k, body) = store(id)
              ???
            case S.LetRecLam(ty, body)           => ???
            case S.LetNative(Name("True"), Nil)  => inl(True)
            case S.LetNative(Name("False"), Nil) => inl(False)
            case S.LetNative(Name("Z"), Nil)     => inl(NatZ)
            case S.LetNative(Name("S"), List(a)) => cont(NatS(ix(a)))
            case S.LetNative(_, _)               => impossible()
    val S.Tm(lets, ret) = tm
    val env = (0 until arity).map(x => Var(mkLvl(x))).reverse.toList
    val dom = mkLvl(arity)
    go(dom, dom, lets, ret, env)

  private def go(t: S.TDef): TDef = TDef(t.ps.map(go), go(t.rt))

  private def go(t: S.Ty): Ty = t match
    case S.TNative(Name("Bool"), Nil) => TBool
    case S.TNative(Name("Nat"), Nil)  => TNat
    case _                            => impossible()
