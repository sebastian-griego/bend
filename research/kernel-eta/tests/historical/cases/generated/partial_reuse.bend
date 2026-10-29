import Base

def first(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def second(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def whole() -> {first == second : Nat -> Nat -> Nat}:
  {==}

def reuse(-x: Nat) -> {first(x) == second(x) : Nat -> Nat}:
  Equal.cong(Nat -> Nat -> Nat, Nat -> Nat, f => f(x), first, second, whole())
