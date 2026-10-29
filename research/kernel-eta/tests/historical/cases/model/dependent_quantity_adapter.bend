import Base

def adapt_quantity(-P: Nat -> Data, p: @-n: Nat -> P(n)) -> @n: Nat -> P(n):
  n => p(n)
