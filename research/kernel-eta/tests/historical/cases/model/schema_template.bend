import Base

def use_twice(~P: Nat -> Data, ~p: @n: Nat -> P(n)) -> P(0n) & P(1n):
  (p(0n), p(1n))

def self_equal(n: Nat) -> {n == n : Nat}:
  {==}

def main() -> {0n == 0n : Nat} & {1n == 1n : Nat}:
  use_twice(~(n => {n == n : Nat}), ~self_equal)

#|({==}, {==})
