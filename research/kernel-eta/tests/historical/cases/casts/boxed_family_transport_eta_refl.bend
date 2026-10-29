import Base

type Box<-A: Type> is Type:
  Box{value: A}

def transport(-f: Nat -> Nat, -P: @-h: Box<(Nat -> Nat)> -> Type, v: P(Box{f})) -> P(Box{x => f(x)}):
  %{{==} : {Box{f} == Box{x => f(x)} : Box<(Nat -> Nat)>}} : P(_)
  v
