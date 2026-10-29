type Box<-A: Type> is Type:
  Box{value: A}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(-f: Type -> Type) -> {Box{f} == Box{f} : Box<(Type -> Type)>}:
  reflexive(Box<(Type -> Type)>, Box{f})
