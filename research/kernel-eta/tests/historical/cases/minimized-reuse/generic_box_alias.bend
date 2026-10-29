type Box<-A: Type> is Type:
  Box{value: A}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(h: Box<(Type -> Type)>) -> {h == h : Box<(Type -> Type)>}:
  alias = h
  reflexive(Box<(Type -> Type)>, alias)
