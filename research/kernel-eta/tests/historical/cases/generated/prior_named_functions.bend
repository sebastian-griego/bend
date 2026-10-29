import Base

def first(x: Nat) -> Nat:
  Succ{x}

def second(x: Nat) -> Nat:
  Succ{x}

def same() -> {first == second : Nat -> Nat}:
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
