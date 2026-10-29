import Base

type Callback is Type:
  Callback{run: Nat -> Nat}

type Container is Type:
  Container{callback: Callback}

def rewrap(h: Container) -> Container:
  match h:
    case Container{Callback{f}}:
      Container{Callback{x => 1n+f(x)}}

def rewrap_identity(h: Container) -> {rewrap(h) == h : Container}:
  match h:
    case Container{Callback{f}}:
      {==}
