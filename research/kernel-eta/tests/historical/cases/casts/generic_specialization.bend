import Base

def identity(-A: Type, -P: @-a: A -> Type, -a: A, v: P(a)) -> P(a):
  v

def specialize(-f: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, v: P(f)) -> P(f):
  identity(Nat -> Nat, P, f, v)
