import Base

def Handler() -> Type:
  Nat -> Nat

def diagonal_refl(-f: @-a: Nat -> Nat -> Nat) -> {(x => f(x, x)) == (x => f(x, x)) : Handler}:
  {==}

def instantiate(-g: Handler) -> {g == g : Handler}:
  diagonal_refl(a => g)

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
