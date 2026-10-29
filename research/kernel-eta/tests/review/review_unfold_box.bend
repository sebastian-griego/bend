type Box is Type:
  Box{value: Type -> Type}

def k(f: Type -> Type) -> Box:
  Box{f}

def same(f: Type -> Type) -> {k(f) == Box{f} : Box}:
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
