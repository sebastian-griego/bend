import Base

type C1 is Type:
  C1{value: @+x: Nat -> Nat}

type C2 is Type:
  C2{value: C1}

type C3 is Type:
  C3{value: C2}

def rewrap(h: C3) -> C3:
  match h:
    case C3{C2{C1{f}}}:
      C3{C2{C1{x => 1n+f(x)}}}

def check_equality(h: C3) -> {rewrap(h) == h : C3}:
  match h:
    case C3{C2{C1{f}}}:
      {==}
