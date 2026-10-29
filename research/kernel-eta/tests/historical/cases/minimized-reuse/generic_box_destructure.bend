type Box<-A: Type> is Type:
  Box{value: A}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(h: Box<(Type -> Type)>) -> {h == h : Box<(Type -> Type)>}:
  Box{f} = h
  reflexive(Box<(Type -> Type)>, Box{f})
