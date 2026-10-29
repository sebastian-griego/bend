type Bit is Data:
  Off{}
  On{}

def first(x: Bit, y: Bit) -> Bit:
  x

def second(x: Bit, y: Bit) -> Bit:
  x

type Indexed<-h: Bit -> Bit> is Type:
  Indexed{}

def Goal(-f: Bit -> Bit -> Bit, -g: Bit -> Bit -> Bit) -> Type:
  {f == g : Bit -> Bit -> Bit} -> Indexed<g(Off{})>

def make() -> Goal(first, second):
  e => Indexed{}

def same() -> {first == second : Bit -> Bit -> Bit}:
  {==}

def use() -> Indexed<first(Off{})>:
  make()(same())
