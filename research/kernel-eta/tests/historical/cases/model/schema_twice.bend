import Base

def use_twice(-P: Nat -> Data, p: @n: Nat -> P(n)) -> P(0n) & P(1n):
  (p(0n), p(1n))
