type Box<-A: Type> is Type:
  Box{value: A}

def use(h: Box<(Type -> Type)>) -> {h == h : Box<(Type -> Type)>}:
  match h:
    case Box{f}:
      {==}
