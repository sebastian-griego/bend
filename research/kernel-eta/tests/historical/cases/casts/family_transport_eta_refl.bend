import Base

def transport(-f: Nat -> Nat, -P: @-h: (Nat -> Nat) -> Type, v: P(f)) -> P(x => f(x)):
  %{{==} : {f == (x => f(x)) : Nat -> Nat}} : P(_)
  v
