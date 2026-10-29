type Unit is Data:
  Unit{}

type Box<-A: Type> is Type:
  Box{value: A}

def rebuild(-A: Type, h: Box<A>) -> Box<A>:
  match h:
    case Box{x}:
      Box{x}

def rebuild_function(h: Box<(Unit -> Unit)>) -> Box<(Unit -> Unit)>:
  match h:
    case Box{f}:
      Box{x => Unit{}}

def same(h: Box<(Unit -> Unit)>) -> {rebuild(Unit -> Unit, h) == rebuild_function(h) : Box<(Unit -> Unit)>}:
  match h:
    case Box{f}:
      {==}
