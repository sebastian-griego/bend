def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(-f: Type -> Type) -> {f == f : Type -> Type}:
  -alias = f
  reflexive(Type -> Type, alias)
