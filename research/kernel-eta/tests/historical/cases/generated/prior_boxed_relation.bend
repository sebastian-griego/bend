import Base

type Callback is Type:
  Saved{run: Nat -> Nat}

def Handler() -> Type:
  Nat -> Nat

def Diagonal() -> Type:
  @-a: Nat -> Nat -> Nat

def Relation() -> Type:
  @-f: Diagonal -> @-h: Diagonal -> Type

def Proof(-R: Relation) -> Type:
  @-f: Diagonal -> @-h: Diagonal -> R(f, h) -> {Saved{x => f(x, x)} == Saved{x => h(x, x)} : Callback}

def reuse(-R: Relation, -g: Handler, -h: Handler, p: Proof(R), e: R(a => g, a => h)) -> {Saved{g} == Saved{h} : Callback}:
  p(a => g, a => h, e)

#|ALL PROOFS CHECK
#|Use --verdict for mathematical validity.
