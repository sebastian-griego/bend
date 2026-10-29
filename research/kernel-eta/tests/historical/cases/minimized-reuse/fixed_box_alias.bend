type Box is Type:
  Box{value: Type -> Type}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(h: Box) -> {h == h : Box}:
  alias = h
  reflexive(Box, alias)
