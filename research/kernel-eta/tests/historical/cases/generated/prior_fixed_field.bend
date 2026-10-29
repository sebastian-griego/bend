import Base

type Callback is Type:
  Saved{run: Nat -> Nat}

def wrap_field(h: Callback) -> Callback:
  match h:
    case Saved{f}:
      Saved{x => f(x)}

def wrap_field_identity(h: Callback) -> {wrap_field(h) == h : Callback}:
  match h:
    case Saved{f}:
      {==}

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
