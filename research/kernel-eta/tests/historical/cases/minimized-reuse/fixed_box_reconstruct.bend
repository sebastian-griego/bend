type Box is Type:
  Box{value: Type -> Type}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(h: Box) -> {h == h : Box}:
  match h:
    case Box{f}:
      reflexive(Box, Box{f})
