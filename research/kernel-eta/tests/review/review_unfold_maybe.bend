import Base

def k(f: Type -> Type) -> Maybe<(Type -> Type)>:
  Some{f}

def same(f: Type -> Type) -> {k(f) == Some{f} : Maybe<(Type -> Type)>}:
  {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
