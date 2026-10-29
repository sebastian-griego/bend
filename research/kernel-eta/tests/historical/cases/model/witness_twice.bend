import Base

def use_twice(-A: Type, -a: A, -b: A, +e: {a == b : A}) -> {a == b : A} & {a == b : A}:
  (e, e)
