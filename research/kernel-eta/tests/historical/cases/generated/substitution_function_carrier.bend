import Base

def identity(-A: Type, x: A) -> A:
  x

def specialized(-P: @-f: (Nat -> Nat) -> Type, -f: Nat -> Nat, value: P(f)) -> P(identity(Nat -> Nat, x => f(x))):
  value
