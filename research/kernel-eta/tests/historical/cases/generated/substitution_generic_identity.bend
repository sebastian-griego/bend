import Base

def identity(-A: Type, x: A) -> A:
  x

def dependent(-A: Type, -P: @-a: A -> Type, -a: A, value: P(a)) -> P(identity(A, a)):
  value
