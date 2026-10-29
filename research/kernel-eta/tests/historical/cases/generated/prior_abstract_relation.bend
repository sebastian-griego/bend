import Base

def Handler() -> Type:
  Nat -> Nat

def Diagonal() -> Type:
  @-a: Nat -> Nat -> Nat

def Relation() -> Type:
  @-f: Diagonal -> @-h: Diagonal -> Type

def Proof(-R: Relation) -> Type:
  @-f: Diagonal -> @-h: Diagonal -> R(f, h) -> {(x => f(x, x)) == (x => h(x, x)) : Handler}

def reuse(-R: Relation, -g: Handler, -h: Handler, p: Proof(R), e: R(a => g, a => h)) -> {g == h : Handler}:
  p(a => g, a => h, e)

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
