type Box<-A: Type> is Type:
  Box{value: A}

def reflexive(-A: Type, -x: A) -> {x == x : A}:
  {==}

def use(h: Box<(Type -> Type)>) -> {h == h : Box<(Type -> Type)>}:
  match h:
    case Box{f}:
      reflexive(Box<(Type -> Type)>, Box{f})
