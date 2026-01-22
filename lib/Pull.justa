module Pull

import Prelude (vtype, (&&), (||), (<), (+), (-), (*), Unit, U)
import IOUtil (return, seq)
import List => L (List)
import Push (Push)

pub def Step A S = (k : cv) (R : type k) -> R -> (A -> S -> R) -> R
pub def Pull A : meta = [S : vtype, step : S -> Step A S, value: S]

pub def fromList {A} (as : List A) : Pull A =
  [
    List A,
    \as k R stop yield =>
      match as
      | Nil => stop
      | hd :: tl => yield hd tl,
    as
  ]

pub def map {A B} (f : A -> B) (p : Pull A) : Pull B =
  [
    p.S,
    \as k R stop yield => p.step as k R stop (\a s => yield (f a) s),
    p.value
  ]

pub def toPush {A : vtype} (p : Pull A) : Push A =
  \k B c n =>
    let rec go s :=
      p.step s k B n (\a s => c a (go s));
    go p.value
