type Unit is Data:
  Unit{}

type Box<-A: Type> is Type:
  Box{value: A}

def rebuild_function(h: Box<(Unit -> Unit)>) -> Box<(Unit -> Unit)>:
  h

def use(h: Box<(Unit -> Unit)>) -> {rebuild_function(h) == h : Box<(Unit -> Unit)>}:
  {==}
