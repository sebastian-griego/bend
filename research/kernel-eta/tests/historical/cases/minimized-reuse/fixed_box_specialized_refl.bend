type Box is Type:
  Box{value: Type -> Type}

def reflexive(-x: Box) -> {x == x : Box}:
  {==}

def use(h: Box) -> {h == h : Box}:
  match h:
    case Box{f}:
      reflexive(Box{f})
