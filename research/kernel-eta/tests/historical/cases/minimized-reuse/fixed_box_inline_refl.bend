type Box is Type:
  Box{value: Type -> Type}

def use(h: Box) -> {h == h : Box}:
  match h:
    case Box{f}:
      {==}
