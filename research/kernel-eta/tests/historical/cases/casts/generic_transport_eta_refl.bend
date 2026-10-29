import Base

def transport(-A: Type, -P: @-a: A -> Type, -a: A, -b: A, e: {a == b : A}, v: P(a)) -> P(b):
  %e : P(_)
  v

def specialize(-f: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, v: P(f)) -> P(x => f(x)):
  transport(Nat -> Nat, P, f, x => f(x), {==}, v)
