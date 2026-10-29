type Box is Type:
  Box{value: Type -> Type}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(-f: Type -> Type) -> {Box{f} == Box{f} : Box}:
  reflexive(Box, Box{f})
