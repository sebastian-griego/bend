import Base

type FB is Type:
  FB{value: Nat -> Nat}

def id(n: Nat) -> Nat:
  n

def mk() -> FB:
  FB{id}

def same() -> {mk() == FB{n => id(n)} : FB}:
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
