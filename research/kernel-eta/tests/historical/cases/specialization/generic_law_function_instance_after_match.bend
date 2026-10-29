type Unit is Data:
  Unit{}

type Box<-A: Type> is Type:
  Box{value: A}

def rebuild(-A: Type, h: Box<A>) -> Box<A>:
  match h:
    case Box{x}:
      Box{x}

def rebuild_identity(-A: Type, h: Box<A>) -> {rebuild(A, h) == h : Box<A>}:
  match h:
    case Box{x}:
      {==}

def use(h: Box<(Unit -> Unit)>) -> {rebuild(Unit -> Unit, h) == h : Box<(Unit -> Unit)>}:
  match h:
    case Box{f}:
      rebuild_identity(Unit -> Unit, Box{f})
