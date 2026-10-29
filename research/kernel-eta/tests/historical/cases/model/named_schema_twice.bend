import Base

def self_equal(-n: Nat) -> {n == n : Nat}:
  {==}

def use_twice() -> {0n == 0n : Nat} & {1n == 1n : Nat}:
  (self_equal(0n), self_equal(1n))
