type Box<-A: Type> is Type:
  Box{value: A}

def reflexive(-x: Box<(Type -> Type)>) -> {x == x : Box<(Type -> Type)>}:
  {==}

def use(-f: Type -> Type) -> {{Box{f} : Box<(Type -> Type)>} == {Box{f} : Box<(Type -> Type)>} : Box<(Type -> Type)>}:
  reflexive(Box{f})
