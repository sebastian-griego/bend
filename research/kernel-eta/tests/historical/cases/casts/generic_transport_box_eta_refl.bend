import Base

type Box<-A: Type> is Type:
  Box{value: A}

def transport(-A: Type, -P: @-a: A -> Type, -a: A, -b: A, e: {a == b : A}, v: P(a)) -> P(b):
  %e : P(_)
  v

def specialize(-f: Nat -> Nat, -P: @-h: Box<(Nat -> Nat)> -> Type, v: P(Box{f})) -> P(Box{x => f(x)}):
  transport(Box<(Nat -> Nat)>, P, Box{f}, Box{x => f(x)}, {==}, v)
