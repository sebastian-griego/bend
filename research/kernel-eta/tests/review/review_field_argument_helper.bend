type Box is Type:
  Box{value: Type -> Type}

def g(f: Type -> Type) -> {Box{f} == Box{f} : Box}:
  {==}

def use(f: Type -> Type) -> {Box{f} == Box{f} : Box}:
  g(f)

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
