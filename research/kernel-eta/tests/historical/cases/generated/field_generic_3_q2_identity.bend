import Base

type Box<-A: Type> is Type:
  Box{value: A}

def rewrap(h: Box<Box<Box<@+x: Nat -> Nat>>>) -> Box<Box<Box<@+x: Nat -> Nat>>>:
  match h:
    case Box{Box{Box{f}}}:
      Box{Box{Box{f}}}

def check_equality(h: Box<Box<Box<@+x: Nat -> Nat>>>) -> {rewrap(h) == h : Box<Box<Box<@+x: Nat -> Nat>>>}:
  match h:
    case Box{Box{Box{f}}}:
      {==}
