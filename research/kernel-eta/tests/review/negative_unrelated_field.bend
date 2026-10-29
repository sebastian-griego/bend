type Box is Type:
  Box{value: Type -> Type}

def bad(f: Type -> Type, g: Type -> Type) -> {Box{f} == Box{g} : Box}:
  {==}

