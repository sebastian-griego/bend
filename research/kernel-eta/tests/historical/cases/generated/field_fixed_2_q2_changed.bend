import Base

type C1 is Type:
  C1{value: @+x: Nat -> Nat}

type C2 is Type:
  C2{value: C1}

def rewrap(h: C2) -> C2:
  match h:
    case C2{C1{f}}:
      C2{C1{x => 1n+f(x)}}

def check_equality(h: C2) -> {rewrap(h) == h : C2}:
  match h:
    case C2{C1{f}}:
      {==}
