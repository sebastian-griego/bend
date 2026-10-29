import Base

def Handler() -> Type:
  Nat -> Nat

def select(b: Bool, f: Handler) -> Handler:
  match b:
    case True{}: f
    case False{}: f

def select_identity(b: Bool, -f: Handler) -> {select(b, f) == f : Handler}:
  match b:
    case True{}: {==}
    case False{}: {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
