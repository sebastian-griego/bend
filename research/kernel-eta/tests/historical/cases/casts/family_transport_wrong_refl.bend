import Base

def transport(-f: Nat -> Nat, -g: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, v: P(f)) -> P(g):
  %{{==} : {f == g : Nat -> Nat}} : P(_)
  v
