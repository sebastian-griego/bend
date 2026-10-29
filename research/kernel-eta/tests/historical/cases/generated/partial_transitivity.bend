import Base

def first(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def second(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)

def left(-x: Nat) -> {first(x) == y => second(x, y) : Nat -> Nat}:
  {==}

def right(-x: Nat) -> {y => second(x, y) == second(x) : Nat -> Nat}:
  {==}

def chain(-x: Nat) -> {first(x) == second(x) : Nat -> Nat}:
  Equal.trans(Nat -> Nat, first(x), y => second(x, y), second(x), left(x), right(x))
