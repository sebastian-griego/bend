type Box is Type:
  Box{value: Type -> Type}

def reflexive(-x: Box) -> {x == x : Box}:
  {==}

def use(h: Box) -> {h == h : Box}:
  reflexive(h)

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
