type Box is Type:
  Box{value: Type -> Type}

def same(f: Type -> Type, g: Type -> Type, e: {f == g : Type -> Type}) ->
    {Box{f} == Box{g} : Box}:
  %e : {Box{f} == Box{_} : Box}
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
