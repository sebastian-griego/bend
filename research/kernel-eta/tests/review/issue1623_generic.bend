import Base

def rebuild(-A: Type, m: Maybe<A>) -> Maybe<A>:
  match m:
    case None{}: None{}
    case Some{x}: Some{x}

def rebuild_fn(m: Maybe<(Nat -> Nat)>) -> Maybe<(Nat -> Nat)>:
  match m:
    case None{}: None{}
    case Some{x}: Some{x}

def same(m: Maybe<(Nat -> Nat)>) ->
    {rebuild_fn(m) == rebuild((Nat -> Nat), m) : Maybe<(Nat -> Nat)>}:
  match m:
    case None{}: {==}
    case Some{x}: {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
