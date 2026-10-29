import Base

type Box<-A: Type> is Type:
  Box{value: A}

def rewrap(h: Box<@x: Nat -> Nat>) -> Box<@x: Nat -> Nat>:
  match h:
    case Box{f}:
      Box{x => f(x)}

def check_equality(h: Box<@x: Nat -> Nat>) -> {rewrap(h) == h : Box<@x: Nat -> Nat>}:
  match h:
    case Box{f}:
      {==}
