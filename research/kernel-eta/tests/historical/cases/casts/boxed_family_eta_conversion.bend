import Base

type Box<-A: Type> is Type:
  Box{value: A}

def convert(-f: Nat -> Nat, -P: @-h: Box<(Nat -> Nat)> -> Type, v: P(Box{f})) -> P(Box{x => f(x)}):
  v
