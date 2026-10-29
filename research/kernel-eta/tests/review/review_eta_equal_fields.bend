type Box is Type:
  Box{value: Type -> Type}

def same(f: Type -> Type) -> {Box{f} == Box{x => f(x)} : Box}:
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
