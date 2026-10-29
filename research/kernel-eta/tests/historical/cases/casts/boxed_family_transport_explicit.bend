import Base

type Box<-A: Type> is Type:
  Box{value: A}

def transport(-f: Nat -> Nat, -g: Nat -> Nat, -P: @-h: Box<(Nat -> Nat)> -> Type, e: {Box{f} == Box{g} : Box<(Nat -> Nat)>}, v: P(Box{f})) -> P(Box{g}):
  %e : P(_)
  v
