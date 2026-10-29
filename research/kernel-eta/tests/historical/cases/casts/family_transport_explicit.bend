import Base

def transport(-f: Nat -> Nat, -g: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, e: {f == g : Nat -> Nat}, v: P(f)) -> P(g):
  %e : P(_)
  v
