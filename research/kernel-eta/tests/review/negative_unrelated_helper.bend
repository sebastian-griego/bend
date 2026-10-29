type Box is Type:
  Box{value: Type -> Type}

def reflexive(-x: Box) -> {x == x : Box}:
  {==}

def bad(f: Type -> Type, g: Type -> Type) -> {Box{f} == Box{g} : Box}:
  reflexive(Box{f})

