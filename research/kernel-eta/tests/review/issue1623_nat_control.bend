import Base

def rebuild(-A: Type, m: Maybe<A>) -> Maybe<A>:
  match m:
    case None{}: None{}
    case Some{x}: Some{x}

def rebuild_fn(m: Maybe<Nat>) -> Maybe<Nat>:
  match m:
    case None{}: None{}
    case Some{x}: Some{x}

def same(m: Maybe<Nat>) ->
    {rebuild_fn(m) == rebuild(Nat, m) : Maybe<Nat>}:
  match m:
    case None{}: {==}
    case Some{x}: {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
