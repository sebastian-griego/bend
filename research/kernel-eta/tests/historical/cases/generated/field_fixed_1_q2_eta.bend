import Base

type C1 is Type:
  C1{value: @+x: Nat -> Nat}

def rewrap(h: C1) -> C1:
  match h:
    case C1{f}:
      C1{x => f(x)}

def check_equality(h: C1) -> {rewrap(h) == h : C1}:
  match h:
    case C1{f}:
      {==}
