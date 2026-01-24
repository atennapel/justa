module IOUtil

import Prelude (vtype)

pub def return = returnIO
pub def bind = bindIO

pub def seq {A B} (a : IO A) (b : IO B) : IO B =
  bind a \_ => b

pub def map {A B : vtype} (f : A -> B) (io : IO A) : IO B =
  bind io \x => return (f x)
