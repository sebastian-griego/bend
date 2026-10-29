import Base

def transport(-A: Type, -P: @-a: A -> Type, -a: A, -b: A, e: {a == b : A}, v: P(a)) -> P(b):
  %e : P(_)
  v

def specialize(-f: Nat -> Nat, -g: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, e: {f == g : Nat -> Nat}, v: P(f)) -> P(g):
  transport(Nat -> Nat, P, f, g, e, v)
