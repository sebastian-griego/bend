import Base

type Callback<-P: Nat -> Data> is Type:
  Callback{run: @n: Nat -> P(n)}

type Container<-P: Nat -> Data> is Type:
  Container{callback: Callback<P>}

def rewrap(-P: Nat -> Data, h: Container<P>) -> Container<P>:
  match h:
    case Container{Callback{f}}:
      Container{Callback{x => f(x)}}

def rewrap_identity(-P: Nat -> Data, h: Container<P>) -> {rewrap(P, h) == h : Container<P>}:
  match h:
    case Container{Callback{f}}:
      {==}
