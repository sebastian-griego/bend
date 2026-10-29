import Base

type Box<-A: Type> is Type:
  Box{value: A}

def rewrap(h: Box<Box<@x: Nat -> Nat>>) -> Box<Box<@x: Nat -> Nat>>:
  match h:
    case Box{Box{f}}:
      Box{Box{x => f(x)}}

def check_equality(h: Box<Box<@x: Nat -> Nat>>) -> {rewrap(h) == h : Box<Box<@x: Nat -> Nat>>}:
  match h:
    case Box{Box{f}}:
      {==}
