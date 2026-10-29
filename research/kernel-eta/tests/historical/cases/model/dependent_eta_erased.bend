import Base

def dependent_eta(-P: Nat -> Data, -p: @-n: Nat -> P(n)) -> {(n => p(n)) == p : @-n: Nat -> P(n)}:
  {==}
