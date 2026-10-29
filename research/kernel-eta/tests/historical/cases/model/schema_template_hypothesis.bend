import Base

def use_twice(~p: @n: Nat -> {n == n : Nat}) -> {0n == 0n : Nat} & {1n == 1n : Nat}:
  (p(0n), p(1n))

def use_local(p: @n: Nat -> {n == n : Nat}) -> {0n == 0n : Nat} & {1n == 1n : Nat}:
  use_twice(~p)
