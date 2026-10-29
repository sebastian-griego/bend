import Base

def transport(-f: Nat -> Nat, -g: Nat -> Nat, -k: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, e: {f == g : Nat -> Nat}, v: P(f)) -> P(k):
  %e : P(_)
  v
