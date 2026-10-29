import Base

def first(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def second(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def whole() -> {first == second : Nat -> Nat -> Nat}:
  {==}

def partial(-x: Nat) -> {first(x) == second(x) : Nat -> Nat}:
  {==}
