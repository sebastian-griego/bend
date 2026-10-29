import Std.Data.HashMap

-- This file contains the revised checker and its safety proofs.

-- Source section: BendTT
section

-- BendTT
-- ======
--
-- BendTT is Bend's kernel: a dependent affine calculus with Type : Type,
-- no universe levels and no native datatypes. This file holds the whole
-- kernel and the argument for its consistency, in three parts:
--
-- 1. THEORY: terms, evaluator, conversion, the bidirectional checker, the
--    live check, a parser for .bendtt text and a CLI.
-- 2. CLAIMS: the declarative theory, and the claims about Part 1's check.
-- 3. PROOF: the lemmas, in order.
--
-- A term has a dead part and a live part, read off its syntax. Types,
-- annotations, motives, and the argument, field or value of a q=0 App,
-- Tup or Let are dead: they are checked for types only, never run, and
-- may be inconsistent (Girard's paradox fits there). All else is live.
-- Every binder, App and Tup states its quantity, so the live part needs
-- no types. The typing checker (Checker) ignores usage; the live check
-- (Termination) ignores types. The live part of a def must be affine (a
-- q=1 variable is used at most once, a q=0 one never), may call only
-- earlier defs, and may call its own def only on arguments no bigger
-- than its parameters, then a smaller one, as bend2's term_descend.
-- A q=2 binder needs a Data domain, and Data holds no λ and no call.
-- A kind is *(q), for a quantity q : <Q0, Q1, Q2>: *1 is *(.Q1), Type,
-- and *2 is *(.Q2), Data. A meet (a <&> b) runs on two of those labels.
-- *(g) fits *(h) when g is .Q2 wherever h is, so a *(q) type is Data
-- only there; ∀s fit by their parts, the domain reversed.
--
-- Then live evaluation terminates by a measure that ignores types: a call
-- is replaced by smaller calls, and all else shrinks. Subject reduction
-- and progress carry the type along, and no value has type <>. So no live
-- term inhabits Empty: termination follows from linearity, and types
-- only rule out stuck terms.
--
-- A datatype is a Σ over a label: Nat = Σt:<Z, S> -> (Nat.arms t). A
-- match is a λ-match: λ{(,): h} splits a pair, λ{.k: h; m} switches on
-- a label, λ{} eliminates the empty enum. A def's leading λs and λ-matches
-- (and λ-matches applied to variables it bound) are its case tree: a call
-- unfolds only when its arguments walk the whole tree, so a stuck call
-- stays a call, and compares by its spine.
--
--   Term ::=
--   | Var ::= k                            # a bound name
--   | Ref ::= k                            # a def's name
--   | Ann ::= "{" x ":" T "}"
--   | Let ::= "!" q k "=" v ";" f          # transparent
--   | Typ ::= "*(" q ")" | "*1" | "*2"     # the kind of quantity q; Type, Data
--   | Min ::= "(" a "<&>" b ")"            # the meet of two quantities
--   | All ::= "∀" q k ":" A "->" B
--   | Lam ::= "λ" q k "=>" f
--   | App ::= "(" f (q x)+ ")"
--   | Sig ::= "Σ" q k ":" A "->" B
--   | Tup ::= "(" q a "," b ")"            # (a, b, c) is (a, (b, c))
--   | Prj ::= "λ{(,):" h "}"
--   | Enu ::= "<" k,* ">"                  # k may be ()
--   | Lab ::= "." k | "()"
--   | Mat ::= "λ{" Lab ":" h ";" m "}"
--   | Efq ::= "λ{}"
--   | Eql ::= "{" a "==" b ":" T "}"
--   | Rfl ::= "{==}"
--   | Rwt ::= "%" e ":" k "," k "=>" P ";" f  # J: P binds x, h : {a == x}
--   q    ::= "-" | "" | "+"                # 0, 1, 2
--   Def  ::= ["opaque"] k ":" T "=" v

-- Types
-- =====

inductive Quan where
  | Q0 | Q1 | Q2
  deriving DecidableEq, Repr, Inhabited



inductive Term where
  | Var (i : Nat)
  | Ref (k : String)
  | Ann (x T : Term)
  | Let (q : Quan) (v f : Term)
  | Typ (q : Term)
  | Min (a b : Term)
  | All (q : Quan) (A B : Term)
  | Lam (q : Quan) (f : Term)
  | App (q : Quan) (f x : Term)
  | Sig (q : Quan) (A B : Term)
  | Tup (q : Quan) (a b : Term)
  | Prj (h : Term)
  | Enu (ks : List String)
  | Lab (k : String)
  | Mat (k : String) (h m : Term)
  | Efq
  | Eql (a b T : Term)
  | Rfl
  | Rwt (e P f : Term)
  deriving DecidableEq, Repr, Inhabited



open Quan Term



-- an opaque def (o) never unfolds; its body is a model, checked with
-- every def transparent, so no other def learns what it computes
structure Def where
  k : String
  T : Term
  v : Term
  o : Bool
  deriving Inhabited



-- each def at its index, from n on (a def's first copy wins)
def Book.table : Nat → List Def → Std.HashMap String (Nat × Def)
  | _, [] => {}
  | n, d :: ds => (Book.table (n + 1) ds).insert d.k (n, d)



-- a Book lists defs, and a def's index orders its live calls; lib is
-- their table, so a lookup is one map read
structure Book where
  defs : List Def
  lib  : Std.HashMap String (Nat × Def)
  ok   : lib = Book.table 0 defs



-- a Ctx lists, innermost first, each variable's type and let value
abbrev Ctx := List (Term × Option Term)



-- an Env lists, innermost first, the values a case tree's λs bound
abbrev Env := List Term



-- an Arg is one spine argument and its quantity
abbrev Arg := Quan × Term



-- a Step is where a walk goes on: a term, its environment and spine
abbrev Step := Term × Env × List Arg



abbrev Ren := Nat → Nat



abbrev Subst := Nat → Term



abbrev Res := Except String



-- a Tag says a variable is the piece of column j at a path: each step,
-- innermost first, takes a pair's first (false) or second (true) field
abbrev Tag := Option (Nat × List Bool)



-- a Guard carries a def's book, its own index, column liveness, var
-- tags, and the labels its matches hit, with their columns and paths
structure Guard where
  book : Book
  self : Nat
  cols : List Bool
  tags : List Tag
  hits : List ((Nat × List Bool) × String)



abbrev Parse := ReaderT ByteArray (StateT Nat (Except String))



-- Constants
-- =========

-- the step budget of each wnf, conv and check; a native build at -O3
-- runs it within a 4 GB stack (LEAN_STACK_SIZE_KB=4194304)
def FUEL : Nat := 400000000



-- Quan
-- ====

def Quan.live : Quan → Bool
  | Q0 => false
  | _  => true



-- a λ's quantity, as far as conversion sees it: q=2 only says how a λ
-- runs (it copies), so a λ+ converts as a λ
def Quan.lin : Quan → Quan
  | Q2 => Q1
  | q  => q



-- the quantity of a pair's first field, when the pair is used at q
def Quan.fld : Quan → Quan → Quan
  | Q0, _ => Q0
  | Q1, q => q
  | Q2, _ => Q2



-- Type and Data
abbrev T1 : Term := Typ (Lab "Q1")


abbrev T2 : Term := Typ (Lab "Q2")



-- the kind a q binder's domain needs, inside a type of kind K
def Term.kindof : Quan → Term → Term
  | Q0, _ => T1
  | Q1, K => K
  | Q2, _ => T2



-- the labels of a quantity
def QS : List String := ["Q0", "Q1", "Q2"]



-- the meet of two quantities, as far as they are known: .Q2 is its
-- identity and .Q0 absorbs it, on either side, as bend2's
def Term.qmin : Term → Term → Term
  | Lab "Q2", b | b, Lab "Q2" => b
  | Lab "Q0", _ | _, Lab "Q0" => Lab "Q0"
  | Lab "Q1", Lab "Q1" => Lab "Q1"
  | a, b => Min a b



-- a q binder allows n live uses
def Quan.allows : Quan → Nat → Bool
  | Q0, n => n == 0
  | Q1, n => n ≤ 1
  | Q2, _ => true



-- Ren
-- ===

def Ren.up (r : Ren) : Nat → Nat
  | 0     => 0
  | i + 1 => r i + 1



-- moves variable v to index 0, under a new binder
def Ren.pick (v i : Nat) : Nat :=
  if i == v then 0 else i + 1



-- Term
-- ====

def Term.ren (r : Ren) : Term → Term
  | Var i => Var (r i)
  | Ref k => Ref k
  | Ann x T =>
    let x := Term.ren r x
    let T := Term.ren r T
    Ann x T
  | Let q v f =>
    let v := Term.ren r v
    let f := Term.ren (Ren.up r) f
    Let q v f
  | Typ q => Typ (Term.ren r q)
  | Min a b => Min (Term.ren r a) (Term.ren r b)
  | All q A B =>
    let A := Term.ren r A
    let B := Term.ren (Ren.up r) B
    All q A B
  | Lam q f =>
    let f := Term.ren (Ren.up r) f
    Lam q f
  | App q f x =>
    let f := Term.ren r f
    let x := Term.ren r x
    App q f x
  | Sig q A B =>
    let A := Term.ren r A
    let B := Term.ren (Ren.up r) B
    Sig q A B
  | Tup q a b =>
    let a := Term.ren r a
    let b := Term.ren r b
    Tup q a b
  | Prj h =>
    let h := Term.ren r h
    Prj h
  | Enu ks => Enu ks
  | Lab k => Lab k
  | Mat k h m =>
    let h := Term.ren r h
    let m := Term.ren r m
    Mat k h m
  | Efq => Efq
  | Eql a b T =>
    let a := Term.ren r a
    let b := Term.ren r b
    let T := Term.ren r T
    Eql a b T
  | Rfl => Rfl
  | Rwt e P f =>
    let e := Term.ren r e
    let P := Term.ren (Ren.up (Ren.up r)) P
    let f := Term.ren r f
    Rwt e P f



def Term.spine (t : Term) : List Arg → Term
  | []           => t
  | (q, x) :: xs => Term.spine (App q t x) xs



def Term.unspine : Term → List Arg → Term × List Arg
  | App q f x, xs => Term.unspine f ((q, x) :: xs)
  | t,         xs => (t, xs)



-- a λ or a λ-match: a node of a case tree, which takes an argument
def Term.takes : Term → Bool
  | Lam _ _   => true
  | Prj _     => true
  | Mat _ _ _ => true
  | Efq       => true
  | _         => false



-- an argument as it enters a type: a λ goes annotated, so its calls infer
def Term.arg (x A : Term) : Term :=
  if Term.takes x then Ann x A else x



-- a former whose parts may bind a variable
def Term.binds : Term → Bool
  | All .. | Lam .. | Sig .. | Rwt .. => true
  | _ => false



-- a node of a case tree: a λ, a λ-match, or a spine of one on a variable
def Term.node : Term → Bool
  | App _ f (Var _) => Term.takes (Term.unspine f []).1
  | t               => Term.takes t



-- Subst
-- =====

def Subst.up (s : Subst) : Nat → Term
  | 0     => Var 0
  | i + 1 => Term.ren Nat.succ (s i)



def Term.sub (s : Subst) : Term → Term
  | Var i => s i
  | Ref k => Ref k
  | Ann x T =>
    let x := Term.sub s x
    let T := Term.sub s T
    Ann x T
  | Let q v f =>
    let v := Term.sub s v
    let f := Term.sub (Subst.up s) f
    Let q v f
  | Typ q => Typ (Term.sub s q)
  | Min a b => Min (Term.sub s a) (Term.sub s b)
  | All q A B =>
    let A := Term.sub s A
    let B := Term.sub (Subst.up s) B
    All q A B
  | Lam q f =>
    let f := Term.sub (Subst.up s) f
    Lam q f
  | App q f x =>
    let f := Term.sub s f
    let x := Term.sub s x
    App q f x
  | Sig q A B =>
    let A := Term.sub s A
    let B := Term.sub (Subst.up s) B
    Sig q A B
  | Tup q a b =>
    let a := Term.sub s a
    let b := Term.sub s b
    Tup q a b
  | Prj h =>
    let h := Term.sub s h
    Prj h
  | Enu ks => Enu ks
  | Lab k => Lab k
  | Mat k h m =>
    let h := Term.sub s h
    let m := Term.sub s m
    Mat k h m
  | Efq => Efq
  | Eql a b T =>
    let a := Term.sub s a
    let b := Term.sub s b
    let T := Term.sub s T
    Eql a b T
  | Rfl => Rfl
  | Rwt e P f =>
    let e := Term.sub s e
    let P := Term.sub (Subst.up (Subst.up s)) P
    let f := Term.sub s f
    Rwt e P f



-- The CLI runs Term.sub as Term.subz (sub_subz): the same map, but it
-- passes the binder depth d down, so a value shifts once, not once per
-- binder, and a variable costs one lookup, not one per binder.

-- s under d binders
def Subst.lift (s : Subst) (d : Nat) (i : Nat) : Term :=
  if i < d then Var i else if d = 0 then s i else Term.ren (· + d) (s (i - d))



def Term.subk (s : Subst) (d : Nat) : Term → Term
  | Var i => Subst.lift s d i
  | Ref k => Ref k
  | Ann x T =>
    let x := Term.subk s d x
    let T := Term.subk s d T
    Ann x T
  | Let q v f =>
    let v := Term.subk s d v
    let f := Term.subk s (d + 1) f
    Let q v f
  | Typ q => Typ (Term.subk s d q)
  | Min a b => Min (Term.subk s d a) (Term.subk s d b)
  | All q A B =>
    let A := Term.subk s d A
    let B := Term.subk s (d + 1) B
    All q A B
  | Lam q f =>
    let f := Term.subk s (d + 1) f
    Lam q f
  | App q f x =>
    let f := Term.subk s d f
    let x := Term.subk s d x
    App q f x
  | Sig q A B =>
    let A := Term.subk s d A
    let B := Term.subk s (d + 1) B
    Sig q A B
  | Tup q a b =>
    let a := Term.subk s d a
    let b := Term.subk s d b
    Tup q a b
  | Prj h =>
    let h := Term.subk s d h
    Prj h
  | Enu ks => Enu ks
  | Lab k => Lab k
  | Mat k h m =>
    let h := Term.subk s d h
    let m := Term.subk s d m
    Mat k h m
  | Efq => Efq
  | Eql a b T =>
    let a := Term.subk s d a
    let b := Term.subk s d b
    let T := Term.subk s d T
    Eql a b T
  | Rfl => Rfl
  | Rwt e P f =>
    let e := Term.subk s d e
    let P := Term.subk s (d + 2) P
    let f := Term.subk s d f
    Rwt e P f



def Term.subz (s : Subst) (t : Term) : Term :=
  Term.subk s 0 t



theorem up_ren : Ren.up r ∘ Ren.up s = Ren.up (r ∘ s) := by
  funext i; cases i <;> rfl



theorem ren_ren (t : Term) : Term.ren r (Term.ren s t) = Term.ren (r ∘ s) t := by
  induction t generalizing r s <;> simp [Term.ren, up_ren, *]



theorem subk_sub (t : Term) : Term.subk s d t = Term.sub (Subst.lift s d) t := by
  have up d : Subst.up (Subst.lift s d) = Subst.lift s (d + 1) := by
    funext i; cases i; rfl
    simp [Subst.up, Subst.lift]; split <;> (try split) <;> simp_all [Term.ren, ren_ren]; rfl
  induction t generalizing d <;> simp [Term.subk, Term.sub, *]



@[csimp] theorem sub_subz : @Term.sub = @Term.subz := by
  funext s t; rw [Term.subz, subk_sub]; rfl



def Subst.one (v : Term) : Nat → Term
  | 0     => v
  | i + 1 => Var i



-- a pair match's motive, at the pair of its two new variables
def Subst.tup (q : Quan) : Nat → Term
  | 0     => Tup q (Var 1) (Var 0)
  | i + 1 => Var (i + 2)



def Term.inst (f v : Term) : Term :=
  Term.sub (Subst.one v) f



-- Env
-- ===

def Env.sub : Env → Nat → Term
  | [],     i     => Var i
  | x :: _, 0     => x
  | _ :: e, i + 1 => Env.sub e i



-- Book
-- ====

def Book.get (bk : Book) (k : String) : Option Def :=
  (bk.lib[k]?).map (·.2)



def Book.index (bk : Book) (k : String) : Option Nat :=
  (bk.lib[k]?).map (·.1)



def Book.length (bk : Book) : Nat :=
  bk.defs.length



def Book.of (ds : List Def) : Book :=
  ⟨ds, Book.table 0 ds, rfl⟩



-- Ctx
-- ===

-- replaces each let variable by its value; every index stays
def Ctx.sub : Ctx → Nat → Term
  | [],               i     => Var i
  | (_, some v) :: c, 0     => Term.ren Nat.succ (Term.sub (Ctx.sub c) v)
  | (_, none) :: _,   0     => Var 0
  | _ :: c,           i + 1 => Term.ren Nat.succ (Ctx.sub c i)



-- (a context without lets leaves t as is)
def Ctx.zeta (c : Ctx) (t : Term) : Term :=
  if c.any (·.2.isSome) then Term.sub (Ctx.sub c) t else t



-- Guard
-- =====

def Guard.bind (g : Guard) (o : Tag) : Guard :=
  { g with tags := o :: g.tags }



-- the tag of the next argument of a case tree: a pending piece, or
-- a new column of the given liveness
def Guard.next (g : Guard) : List Tag → Bool → Tag × Guard × List Tag
  | p :: ps, _ => (p, g, ps)
  | [],      l =>
    let p := some (g.cols.length, [])
    let g := { g with cols := g.cols ++ [l] }
    (p, g, [])



-- Show
-- ====

def Quan.mark : Quan → String
  | Q0 => "-"
  | Q1 => ""
  | Q2 => "+"



-- the name of the variable bound at depth d
def Nat.name (d : Nat) : String :=
  "x" ++ toString d



def Term.show : Term → Nat → String
  | Var i, d => Nat.name (d - i - 1)
  | Ref k, _ => k
  | Ann x T, d =>
    let x := Term.show x d
    let T := Term.show T d
    "{" ++ x ++ " : " ++ T ++ "}"
  | Let q v f, d =>
    let v := Term.show v d
    let f := Term.show f (d + 1)
    "!" ++ Quan.mark q ++ Nat.name d ++ " = " ++ v ++ "; " ++ f
  | Typ (Lab "Q1"), _ => "*1"
  | Typ (Lab "Q2"), _ => "*2"
  | Typ q, d => "*(" ++ Term.show q d ++ ")"
  | Min a b, d => "(" ++ Term.show a d ++ " <&> " ++ Term.show b d ++ ")"
  | All q A B, d =>
    let A := Term.show A d
    let B := Term.show B (d + 1)
    "∀" ++ Quan.mark q ++ Nat.name d ++ " : " ++ A ++ " -> " ++ B
  | Lam q f, d =>
    let f := Term.show f (d + 1)
    "λ" ++ Quan.mark q ++ Nat.name d ++ " => " ++ f
  | App q f x, d =>
    let f := Term.show f d
    let x := Term.show x d
    "(" ++ f ++ " " ++ Quan.mark q ++ x ++ ")"
  | Sig q A B, d =>
    let A := Term.show A d
    let B := Term.show B (d + 1)
    "Σ" ++ Quan.mark q ++ Nat.name d ++ " : " ++ A ++ " -> " ++ B
  | Tup q a b, d =>
    let a := Term.show a d
    let b := Term.show b d
    "(" ++ Quan.mark q ++ a ++ ", " ++ b ++ ")"
  | Prj h, d =>
    let h := Term.show h d
    "λ{(,): " ++ h ++ "}"
  | Enu ks, _ => "<" ++ ", ".intercalate ks ++ ">"
  | Lab k, _ => if k == "()" then k else "." ++ k
  | Mat k h m, d =>
    let k := if k == "()" then k else "." ++ k
    let h := Term.show h d
    let m := Term.show m d
    "λ{" ++ k ++ ": " ++ h ++ "; " ++ m ++ "}"
  | Efq, _ => "λ{}"
  | Eql a b T, d =>
    let a := Term.show a d
    let b := Term.show b d
    let T := Term.show T d
    "{" ++ a ++ " == " ++ b ++ " : " ++ T ++ "}"
  | Rfl, _ => "{==}"
  | Rwt e P f, d =>
    let e := Term.show e d
    let P := Term.show P (d + 2)
    let f := Term.show f d
    "%" ++ e ++ " : " ++ Nat.name d ++ ", " ++ Nat.name (d + 1) ++ " => " ++ P ++ "; " ++ f



-- Parser
-- ======

-- the parser reads the text's UTF-8 bytes at a position; a name, a space
-- and every mark but ∀, Σ and λ is one ASCII byte

-- the byte after the char at i
def Parse.next (b : ByteArray) (i : Nat) : Nat :=
  [1, 2, 3].foldl (fun j _ => if j < b.size && b[j]! &&& 0xC0 == 0x80 then j + 1 else j) (i + 1)



def Parse.fail (e : String) : Parse α := do
  let b ← read
  let i ← get
  let j := (List.range 30).foldl (fun j _ => if j < b.size then Parse.next b j else j) i
  throw ("parse error: expected " ++ e ++ " at '" ++ (String.fromUTF8? (b.extract i j)).getD "" ++ "'")



-- the first byte at or after i that is not a space or in a comment
partial def Parse.gap (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size then
    let c := Char.ofUInt8 b[i]!
    if c == '#' then Parse.gap b (eol b i)
    else if c.isWhitespace then Parse.gap b (i + 1)
    else i
  else i
where eol (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size && b[i]! != 10 then eol b (i + 1) else i



def Parse.skip : Parse Unit := do
  let b ← read
  modify (Parse.gap b)



def Parse.peek : Parse Char := do
  Parse.skip
  let b ← read
  let i ← get
  pure (if i < b.size then Char.ofUInt8 b[i]! else ' ')



-- whether the text at i starts with w
partial def Parse.at (b : ByteArray) (i : Nat) (w : String) (j : Nat := 0) : Bool :=
  if h : j < w.utf8ByteSize then
    i + j < b.size && b[i + j]! == w.getUTF8Byte ⟨j⟩ h && Parse.at b i w (j + 1)
  else true



-- whether w comes next, without taking it
def Parse.sees (w : String) : Parse Bool := do
  Parse.skip
  pure (Parse.at (← read) (← get) w)



def Parse.take (w : String) : Parse Bool := do
  if ← Parse.sees w then
    modify (· + w.utf8ByteSize)
    pure true
  else
    pure false



def Parse.eat (w : String) : Parse Unit := do
  let ok ← Parse.take w
  if !ok then
    Parse.fail ("'" ++ w ++ "'")



def Char.is_name (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'



-- the end of the name at i
partial def Parse.span (b : ByteArray) (i : Nat) : Nat :=
  if i < b.size && (Char.ofUInt8 b[i]!).is_name then Parse.span b (i + 1) else i



def Parse.name : Parse String := do
  Parse.skip
  let b ← read
  let i ← get
  let j := Parse.span b i
  if j == i then
    Parse.fail "a name"
  set j
  pure ((String.fromUTF8? (b.extract i j)).getD "")



-- a label name: a name, or ()
def Parse.label : Parse String := do
  if ← Parse.take "()" then
    return "()"
  Parse.name



-- a label key: .k or ()
def Parse.key : Parse String := do
  if ← Parse.take "()" then
    return "()"
  Parse.eat "."
  Parse.name



def Quan.parse : Parse Quan := do
  if ← Parse.take "-" then
    return Q0
  if ← Parse.take "+" then
    return Q2
  return Q1



mutual

partial def Term.parse (vs : List String) : Parse Term := do
  let c ← Parse.peek
  if c.toNat ≥ 128 then
    if ← Parse.sees "∀" then
      return ← Term.parse_bind vs "∀"
    if ← Parse.sees "Σ" then
      return ← Term.parse_bind vs "Σ"
    if ← Parse.sees "λ" then
      return ← Term.parse_lam vs
  match c with
  | '{' => Term.parse_brace vs
  | '*' => Term.parse_typ vs
  | '!' => Term.parse_let vs
  | '(' => Term.parse_paren vs
  | '<' => Term.parse_enum []
  | '.' => Lab <$> Parse.key
  | '%' => Term.parse_rwt vs
  | _   => Term.parse_name vs

partial def Term.parse_name (vs : List String) : Parse Term := do
  let k ← Parse.name
  match vs.findIdx? (· == k) with
  | some i => return Var i
  | none   => return Ref k

partial def Term.parse_brace (vs : List String) : Parse Term := do
  Parse.eat "{"
  if ← Parse.take "==" then
    Parse.eat "}"
    return Rfl
  let a ← Term.parse vs
  if ← Parse.take "==" then
    let b ← Term.parse vs
    Parse.eat ":"
    let T ← Term.parse vs
    Parse.eat "}"
    return Eql a b T
  Parse.eat ":"
  let T ← Term.parse vs
  Parse.eat "}"
  return Ann a T

partial def Term.parse_typ (vs : List String) : Parse Term := do
  Parse.eat "*"
  if ← Parse.take "(" then
    let q ← Term.parse vs
    Parse.eat ")"
    return Typ q
  if ← Parse.take "2" then
    return T2
  Parse.eat "1"
  return T1

partial def Term.parse_let (vs : List String) : Parse Term := do
  Parse.eat "!"
  let q ← Quan.parse
  let k ← Parse.name
  Parse.eat "="
  let v ← Term.parse vs
  Parse.eat ";"
  let f ← Term.parse (k :: vs)
  return Let q v f

partial def Term.parse_bind (vs : List String) (c : String) : Parse Term := do
  Parse.eat c
  let q ← Quan.parse
  let k ← Parse.name
  Parse.eat ":"
  let A ← Term.parse vs
  Parse.eat "->"
  let B ← Term.parse (k :: vs)
  return if c == "∀" then All q A B else Sig q A B

partial def Term.parse_lam (vs : List String) : Parse Term := do
  Parse.eat "λ"
  if ← Parse.take "{" then
    Term.parse_match vs
  else
    let q ← Quan.parse
    let k ← Parse.name
    Parse.eat "=>"
    let f ← Term.parse (k :: vs)
    return Lam q f

partial def Term.parse_match (vs : List String) : Parse Term := do
  if ← Parse.take "}" then
    return Efq
  if ← Parse.take "(,)" then
    Parse.eat ":"
    let h ← Term.parse vs
    Parse.eat "}"
    return Prj h
  let k ← Parse.key
  Parse.eat ":"
  let h ← Term.parse vs
  Parse.eat ";"
  let m ← Term.parse vs
  Parse.eat "}"
  return Mat k h m

partial def Term.parse_paren (vs : List String) : Parse Term := do
  Parse.eat "("
  if ← Parse.take ")" then
    return Lab "()"
  let q ← Quan.parse
  let a ← Term.parse vs
  if ← Parse.take "," then
    let b ← Term.parse_tup vs
    return Tup q a b
  else if q == Q1 then
    if ← Parse.take "<&>" then
      let b ← Term.parse vs
      Parse.eat ")"
      return Min a b
    Term.parse_args vs a
  else
    Parse.fail "a pair after a quantity mark"

-- the rest of a tuple, after a ","
partial def Term.parse_tup (vs : List String) : Parse Term := do
  let q ← Quan.parse
  let a ← Term.parse vs
  if ← Parse.take "," then
    let b ← Term.parse_tup vs
    return Tup q a b
  else if q == Q1 then
    Parse.eat ")"
    return a
  else
    Parse.fail "a pair after a quantity mark"

partial def Term.parse_args (vs : List String) (f : Term) : Parse Term := do
  if ← Parse.take ")" then
    return f
  let q ← Quan.parse
  let x ← Term.parse vs
  Term.parse_args vs (App q f x)

partial def Term.parse_enum (ks : List String) : Parse Term := do
  if ks.isEmpty then
    Parse.eat "<"
  if ← Parse.take ">" then
    return Enu ks.reverse
  let k ← Parse.label
  if ks.contains k then
    Parse.fail "a fresh label"
  let _ ← Parse.take ","
  Term.parse_enum (k :: ks)

partial def Term.parse_rwt (vs : List String) : Parse Term := do
  Parse.eat "%"
  let e ← Term.parse vs
  Parse.eat ":"
  let x ← Parse.name
  Parse.eat ","
  let h ← Parse.name
  Parse.eat "=>"
  let P ← Term.parse (h :: x :: vs)
  Parse.eat ";"
  let f ← Term.parse vs
  return Rwt e P f

end



partial def Book.parse_defs : Parse (List Def) := do
  Parse.skip
  if (← getThe Nat) ≥ (← readThe ByteArray).size then
    return []
  let k ← Parse.name
  let o := k == "opaque" && (← Parse.peek) != ':'
  let k ← if o then Parse.name else pure k
  Parse.eat ":"
  let T ← Term.parse []
  Parse.eat "="
  let v ← Term.parse []
  let ds ← Book.parse_defs
  return ⟨k, T, v, o⟩ :: ds



def Book.parse (s : String) : Res Book :=
  ((Book.parse_defs.run s.toUTF8).run' 0).map Book.of



-- Evaluator
-- =========

-- wnf reduces a head on a spine. A λ or a λ-match fires on its next
-- argument; a def unfolds only when it is not opaque and its case tree
-- takes the whole walk (run), else the call stays, so a stuck call
-- folds back to itself. Each takes fuel and returns the fuel it left,
-- so one budget bounds all the work. A caller goes on with min m n, as
-- Lean needs to see the fuel shrink (m ≤ n holds anyway).
-- On a closed term (cl), a q=2 let value or argument, which is Data,
-- goes to normal form (val) before it is bound, so its copies share the
-- work. An open term stays lazy: its stuck parts can grow without end.

mutual

def Term.wnf (ck : Book) (cl : Bool) : Nat → Term → List Arg → Term × Nat
  | 0, t, xs => (Term.spine t xs, 0)
  | n + 1, Ann x _, xs => Term.wnf ck cl n x xs
  | n + 1, Let q v f, xs =>
    let (v, m) := Term.val ck cl n q v
    Term.wnf ck cl (min m n) (Term.inst f v) xs
  | n + 1, App q f x, xs => Term.wnf ck cl n f ((q, x) :: xs)
  | n + 1, Rwt e P f, xs =>
    match Term.wnf ck cl n e [] with
    | (Rfl, m) => Term.wnf ck cl (min m n) f xs
    | (e, m)   => (Term.spine (Rwt e P f) xs, m)
  | n + 1, Min a b, xs =>
    let (a, m) := Term.wnf ck cl n a []
    let (b, m) := Term.wnf ck cl (min m n) b []
    (Term.spine (Term.qmin a b) xs, m)
  | n + 1, Ref k, xs =>
    match ck.get k with
    | some ⟨_, _, v, false⟩ =>
      match Term.run ck cl n v [] xs with
      | (some t, m) => Term.wnf ck cl (min m n) t []
      | (none, m)   => (Term.spine (Ref k) xs, m)
    | _ => (Term.spine (Ref k) xs, n)
  | n + 1, t, xs =>
    match Term.fire ck cl n t [] xs with
    | (some (t, e, xs), m) =>
      let t := Term.sub (Env.sub e) t
      Term.wnf ck cl (min m n) t xs
    | (none, m) => (Term.spine t xs, m)

-- walks a def's case tree on a spine, binding its variables in the
-- environment e: some leaf when the walk leaves the tree
def Term.run (ck : Book) (cl : Bool) : Nat → Term → Env → List Arg → Option Term × Nat
  | 0, _, _, _ => (none, 0)
  | n + 1, App q f (Var v), e, xs =>
    if Term.takes (Term.unspine f []).1 then
      Term.run ck cl n f e ((q, Env.sub e v) :: xs)
    else
      let t := Term.sub (Env.sub e) (App q f (Var v))
      let t := Term.spine t xs
      (some t, n)
  | n + 1, t, e, xs =>
    match Term.fire ck cl n t e xs with
    | (some (t, e, xs), m) => Term.run ck cl (min m n) t e xs
    | (none, m) =>
      if Term.takes t then
        (none, m)
      else
        let t := Term.sub (Env.sub e) t
        let t := Term.spine t xs
        (some t, m)

-- fires a λ or a λ-match on its next argument; a λ binds it in e
def Term.fire (ck : Book) (cl : Bool) : Nat → Term → Env → List Arg → Option Step × Nat
  | n + 1, Lam q f, e, (_, x) :: xs =>
    let (x, m) := Term.val ck cl n q x
    (some (f, x :: e, xs), m)
  | n + 1, Prj h, e, (q, x) :: xs =>
    match Term.wnf ck cl n x [] with
    | (Tup r a b, n) =>
      let xs := (Quan.fld r q, a) :: (q, b) :: xs
      (some (h, e, xs), n)
    | (_, n)         => (none, n)
  | n + 1, Mat k h m, e, (q, x) :: xs =>
    match Term.wnf ck cl n x [] with
    | (Lab j, n) =>
      if j == k then
        (some (h, e, xs), n)
      else
        (some (m, e, (q, Lab j) :: xs), n)
    | (_, n)     => (none, n)
  | n, _, _, _ => (none, n)

-- a value bound at q: on a closed term, a q=2 one goes to normal form
def Term.val (ck : Book) : Bool → Nat → Quan → Term → Term × Nat
  | true, n + 1, Q2, t =>
    match Term.wnf ck true n t [] with
    | (Tup q a b, m) =>
      let (a, m) := Term.val ck true (min m n) (Quan.fld q Q2) a
      let (b, m) := Term.val ck true (min m n) Q2 b
      (Tup q a b, m)
    | r => r
  | _, n, _, t => (t, n)

end



def Ctx.wnf (ck : Book) (c : Ctx) (t : Term) : Term :=
  (Term.wnf ck c.isEmpty FUEL (Ctx.zeta c t) []).1



-- Equality
-- ========

-- the parts two weak heads must match on: the children of one former,
-- as pairs; none when the heads differ. A λ+ matches a λ
def Term.parts : Term → Term → Option (List (Term × Term))
  | All q A B, All p C D => if q = p then some [(A, C), (B, D)] else none
  | Lam q f,   Lam p g   => if q.lin = p.lin then some [(f, g)] else none
  | App q f x, App p g y => if q = p then some [(f, g), (x, y)] else none
  | Sig q A B, Sig p C D => if q = p then some [(A, C), (B, D)] else none
  | Tup q a b, Tup p c d => if q = p then some [(a, c), (b, d)] else none
  | Prj h,     Prj g     => some [(h, g)]
  | Typ q,     Typ p     => some [(q, p)]
  | Min a b,   Min c d   => some [(a, c), (b, d)]
  | Mat k h m, Mat j g n => if k = j then some [(h, g), (m, n)] else none
  | Eql a b T, Eql c d U => some [(a, c), (b, d), (T, U)]
  | Rwt e P f, Rwt d Q g => some [(e, d), (P, Q), (f, g)]
  | a,         b         => if a = b then some [] else none



-- Checker
-- =======

def Res.need (ok : Bool) (e : String) : Res Unit :=
  if ok then pure () else throw e



def Ctx.fail (c : Ctx) (x : String) (o : Term) : Res α :=
  let o := Term.show (Ctx.zeta c o) c.length
  throw ("expected: " ++ x ++ "\nobserved: " ++ o)



-- passes when r holds; else fails as out of fuel, or on the mismatch
def Ctx.need (c : Ctx) (r : Bool × Nat) (x : String) (o : Term) : Res Unit :=
  match r with
  | (true, _) => pure ()
  | (_, 0)    => throw "out of fuel"
  | _         => Ctx.fail c x o



-- Termination
-- ===========

-- The live check reads only the live part. A binder's variable is used
-- live at most as its quantity allows (Term.uses); the two arms of a
-- match add up. A def's case tree gives each variable it binds a tag:
-- a column j and a path into it; a λ-match on a tagged variable splits
-- it into pieces one step deeper, or hits a label, which the guard
-- records. A live call must name an earlier def, or its own def with
-- arguments that descend: compared left to right, each live column gets
-- a value no bigger than itself (eq) until one gets a smaller one (lt),
-- as bend2's term_descend decides against the column's pattern (Pat.cmp).
-- Dead columns are skipped.

-- the live uses of variable i in t
def Term.uses : Term → Nat → Nat
  | Var j, i => if i == j then 1 else 0
  | Ann x _, i => Term.uses x i
  | Let q v f, i =>
    let v := if Quan.live q then Term.uses v i else 0
    let f := Term.uses f (i + 1)
    v + f
  | Lam _ f, i => Term.uses f (i + 1)
  | App q f x, i =>
    let f := Term.uses f i
    let x := if Quan.live q then Term.uses x i else 0
    f + x
  | Tup q a b, i =>
    let a := if Quan.live q then Term.uses a i else 0
    let b := Term.uses b i
    a + b
  | Prj h, i => Term.uses h i
  | Mat _ h m, i =>
    let h := Term.uses h i
    let m := Term.uses m i
    h + m
  | Rwt e _ f, i =>
    let e := Term.uses e i
    let f := Term.uses f i
    e + f
  | Min a b, i =>
    let a := Term.uses a i
    let b := Term.uses b i
    a + b
  | _, _ => 0



-- A column's pattern: the pieces the def's case tree split open, each a
-- pair of its parts, and holes for the rest
inductive Pat where
  | hole
  | pair (a b : Pat)



-- p, split open down to the piece at π (outermost step first)
def Pat.ins : List Bool → Pat → Pat
  | [], p => p
  | b :: π, p =>
    let (x, y) := match p with | .pair x y => (x, y) | .hole => (.hole, .hole)
    if b then .pair x (Pat.ins π y) else .pair (Pat.ins π x) y



-- column j's pattern: split down to every variable the case tree bound in
-- it and every label a match hit
def Guard.pat (g : Guard) (j : Nat) : Pat :=
  let ps := (g.tags.filterMap id ++ g.hits.map (·.1)).filterMap fun (c, π) =>
    if c == j then some π else none
  ps.foldl (fun p π => Pat.ins π.reverse p) .hole



-- x is the piece at π of column j as the case tree saw it: the variable it
-- bound there, or the label a match hit there
def Guard.at (g : Guard) (j : Nat) (π : List Bool) : Term → Bool
  | Var v => g.tags[v]? == some (some (j, π))
  | Lab k => g.hits.contains ((j, π), k)
  | _ => false



mutual
-- how x compares to the piece at π of column j, whose pattern is p, as
-- bend2's term_descend: field by field (Pat.fields), and when one may be
-- bigger, x is lt if it is no bigger than another of those fields
def Pat.cmp (g : Guard) (j : Nat) (p : Pat) (π : List Bool) (x : Term) : Ordering :=
  match Pat.fields g j p π x with
  | .ok o => o
  | .error bad => match p with
    | .pair _ b => if Pat.visit g j bad b (true :: π) x then .lt else .gt
    | .hole => .gt
termination_by 2 * sizeOf p + 1

-- x against the piece at π, whose pattern is p: eq when it is the
-- variable the case tree bound there, or the label a match hit there;
-- else a constructor's fields in turn, down its right spine (a dead one
-- must be such a variable): how they compare, or the path of the first
-- that may be bigger, or x's when it is no constructor
def Pat.fields (g : Guard) (j : Nat) (p : Pat) (π : List Bool) (x : Term) :
    Except (List Bool) Ordering :=
  if g.at j π x then .ok .eq else
  match p, x with
  | .pair a b, Tup q x y =>
    let o := if Quan.live q then Pat.cmp g j a (false :: π) x
      else if g.at j (false :: π) x then .eq else .gt
    match o with
    | .gt => .error (false :: π)
    | o => (Pat.fields g j b (true :: π) y).map o.then
  | _, _ => .error π
termination_by 2 * sizeOf p

-- x is no bigger than a field on the chain q at ρ, other than the one
-- that failed: as bend2, only the constructor's fields are tried, not its
-- tag or the pairs that chain them
def Pat.visit (g : Guard) (j : Nat) (bad : List Bool) (q : Pat) (ρ : List Bool)
    (x : Term) : Bool :=
  match q with
  | .pair a b =>
    (bad != false :: ρ && Pat.cmp g j a (false :: ρ) x != .gt) || Pat.visit g j bad b (true :: ρ) x
  | .hole => false
termination_by 2 * sizeOf q
end



def Arg.cmp (g : Guard) (j : Nat) : Arg → Ordering
  | (q, x) =>
    if g.cols[j]? != some (Quan.live q) then
      .gt
    else if Quan.live q then
      Pat.cmp g j (g.pat j) [] x
    else
      .eq



def Arg.descend (g : Guard) : Nat → List Arg → Ordering
  | _, [] => .eq
  | j, x :: xs =>
    match Arg.cmp g j x with
    | .eq => Arg.descend g (j + 1) xs
    | o   => o



-- a live call names an earlier def, or its own def on a descent
def Term.called (g : Guard) (t : Term) : Bool :=
  match Term.unspine t [] with
  | (Ref k, xs) =>
    match Book.index g.book k with
    | some j => j < g.self || (j == g.self && Arg.descend g 0 xs == .lt)
    | none   => false
  | _ => true



-- the live check of a term; top is false on the head of an App
def Term.live (g : Guard) : Bool → Term → Bool
  | top, App q f x =>
    let s := !top || Term.called g (App q f x)
    let f := Term.live g false f
    let x := !Quan.live q || Term.live g true x
    s && f && x
  | top, Ref k => !top || Term.called g (Ref k)
  | _, Ann x _ => Term.live g true x
  | _, Let q v f =>
    let a := Quan.allows q (Term.uses f 0)
    let v := !Quan.live q || Term.live g true v
    let f := Term.live (Guard.bind g none) true f
    a && v && f
  | _, Lam q f =>
    let a := Quan.allows q (Term.uses f 0)
    let f := Term.live (Guard.bind g none) true f
    a && f
  | _, Tup q a b =>
    let a := !Quan.live q || Term.live g true a
    let b := Term.live g true b
    a && b
  | _, Prj h => Term.live g true h
  | _, Mat _ h m =>
    let h := Term.live g true h
    let m := Term.live g true m
    h && m
  | _, Rwt e _ f =>
    let e := Term.live g true e
    let f := Term.live g true f
    e && f
  | _, Min a b =>
    let a := Term.live g true a
    let b := Term.live g true b
    a && b
  | _, _ => true



-- the live check of a def's case tree: ps are the pending arguments
def Term.tree (g : Guard) (ps : List Tag) : Term → Bool
  | Lam q f =>
    let (p, g, ps) := Guard.next g ps (Quan.live q)
    let a := Quan.allows q (Term.uses f 0)
    let f := Term.tree (Guard.bind g p) ps f
    a && f
  | Prj h =>
    let (p, g, ps) := Guard.next g ps true
    let a := p.map (fun (j, π) => (j, false :: π))
    let b := p.map (fun (j, π) => (j, true :: π))
    Term.tree g (a :: b :: ps) h
  | Mat k h m =>
    let (p, g, ps) := Guard.next g ps true
    let hits := p.toList.map (·, k) ++ g.hits
    let h := Term.tree { g with hits := hits } ps h
    let m := Term.tree g (p :: ps) m
    h && m
  | Efq => true
  | App q f (Var v) =>
    if Term.takes (Term.unspine f []).1 then
      Term.tree g ((g.tags[v]?).join :: ps) f
    else
      Term.live g true (App q f (Var v))
  | t => Term.live g true t



-- CLAIMS
-- ======
--
-- Part 2 states what Part 1's check guarantees. First the declarative
-- theory: parallel reduction (Par), its closure (Pars), conversion (Conv),
-- subsumption (Fits) and typing (Typed); the rules mirror the checker's,
-- one for one. Then the run-time semantics the proof uses: Data, values
-- (Value), the walk of a call through its def's case tree (Walk) and
-- call-by-value evaluation (Eval). Eval never runs a dead part, fires a
-- call only when its arguments walk the whole tree, and checks at run
-- time what types promise (a q=2 copy is Data, a λ-match gets a live
-- pair or label). The measure of the termination proof needs no types,
-- since these checks are in Eval; progress shows typed terms pass them.
-- Part 2 ignores the opaque flag: an opaque def unfolds to its model.

-- Reduction
-- ---------

def Term.Closed (t : Term) : Prop :=
  ∀ s : Subst, Term.sub s t = t



-- every def's body is closed
def Book.Closed (bk : Book) : Prop :=
  ∀ k d, Book.get bk k = some d → Term.Closed d.v



-- δ unfolds only a closed body, so Par commutes with substitution
inductive Par (bk : Book) : Term → Term → Prop
  | var   : Par bk (Var i) (Var i)
  | ref   : Par bk (Ref k) (Ref k)
  | ann   : Par bk x x' → Par bk T T' → Par bk (Ann x T) (Ann x' T')
  | lett  : Par bk v v' → Par bk f f' → Par bk (Let q v f) (Let q v' f')
  | typ   : Par bk q q' → Par bk (Typ q) (Typ q')
  | min   : Par bk a a' → Par bk b b' → Par bk (Min a b) (Min a' b')
  | all   : Par bk A A' → Par bk B B' → Par bk (All q A B) (All q A' B')
  | lam   : Par bk f f' → (p = q ∨ p = q.lin) → Par bk (Lam q f) (Lam p f')
  | app   : Par bk f f' → Par bk x x' → Par bk (App q f x) (App q f' x')
  | sig   : Par bk A A' → Par bk B B' → Par bk (Sig q A B) (Sig q A' B')
  | tup   : Par bk a a' → Par bk b b' → Par bk (Tup q a b) (Tup q a' b')
  | prj   : Par bk h h' → Par bk (Prj h) (Prj h')
  | enu   : Par bk (Enu ks) (Enu ks)
  | lab   : Par bk (Lab k) (Lab k)
  | mat   : Par bk h h' → Par bk m m' → Par bk (Mat k h m) (Mat k h' m')
  | efq   : Par bk Efq Efq
  | eql   : Par bk a a' → Par bk b b' → Par bk T T' →
            Par bk (Eql a b T) (Eql a' b' T')
  | rfl   : Par bk Rfl Rfl
  | rwt   : Par bk e e' → Par bk P P' → Par bk f f' →
            Par bk (Rwt e P f) (Rwt e' P' f')
  | delta : Book.get bk k = some d → Term.Closed d.v → Par bk (Ref k) d.v
  | unann : Par bk x x' → Par bk (Ann x T) x'
  | unlet : Par bk v v' → Par bk f f' → Par bk (Let q v f) (Term.inst f' v')
  | beta  : Par bk f f' → Par bk x x' →
            Par bk (App q (Lam p f) x) (Term.inst f' x')
  | split : Par bk h h' → Par bk a a' → Par bk b b' →
            Par bk (App q (Prj h) (Tup r a b))
              (App q (App (Quan.fld r q) h' a') b')
  | hit   : Par bk h h' → Par bk (App q (Mat k h m) (Lab k)) h'
  | miss  : j ≠ k → Par bk m m' →
            Par bk (App q (Mat k h m) (Lab j)) (App q m' (Lab j))
  | cast  : Par bk f f' → Par bk (Rwt Rfl P f) f'
  | meet  : Par bk a a' → Par bk b b' → Par bk (Min a b) (Term.qmin a' b')



inductive Pars (bk : Book) : Term → Term → Prop
  | refl : Pars bk t t
  | step : Par bk t u → Pars bk u v → Pars bk t v



def Conv (bk : Book) (a b : Term) : Prop :=
  ∃ c, Pars bk a c ∧ Pars bk b c



-- every def is closed, and its case tree passed the live check at its
-- index
def Book.Live (bk : Book) : Prop :=
  Book.Closed bk ∧ ∀ k i d, Book.index bk k = some i → Book.get bk k = some d →
    Term.tree ⟨bk, i, [], [], []⟩ [] d.v = true



-- a live term outside the book: it may call any def
def Term.Live (bk : Book) (t : Term) : Prop :=
  Term.live ⟨bk, bk.length, [], [], []⟩ true t = true



-- Evaluation
-- ----------

-- Data: the live part holds labels, proofs and pairs, no λ, no call
inductive Data : Term → Prop
  | lab : Data (Lab k)
  | rfl : Data Rfl
  | tup : (q.live = true → Data a) → Data b → Data (Tup q a b)



-- a def's case tree walked on a spine, with an environment e for the
-- variables its λs bind: some leaf (under e, on the rest of the spine)
-- when it leaves the tree, none when it needs more arguments; the
-- walk never enters a substituted term, and never runs a dead part
inductive Walk (bk : Book) : Term → Env → List Arg → Option Term → Prop
  | lam  : p.live = q.live → (p = Q2 → Data x) →
           Walk bk f (x :: e) xs o → Walk bk (Lam p f) e ((q, x) :: xs) o
  | prj  : q.live = true →
           Walk bk h e ((Quan.fld r q, a) :: (q, b) :: xs) o →
           Walk bk (Prj h) e ((q, Tup r a b) :: xs) o
  | hit  : q.live = true → Walk bk h e xs o →
           Walk bk (Mat k h m) e ((q, Lab k) :: xs) o
  | miss : q.live = true → j ≠ k → Walk bk m e ((q, Lab j) :: xs) o →
           Walk bk (Mat k h m) e ((q, Lab j) :: xs) o
  | app  : Term.node (App q f (Var v)) = true →
           Walk bk f e ((q, Env.sub e v) :: xs) o →
           Walk bk (App q f (Var v)) e xs o
  | need : Term.takes t = true → Walk bk t e [] none
  | done : Term.node t = false →
           Walk bk t e xs (some (Term.spine (Term.sub (Env.sub e) t) xs))



mutual

inductive Value (bk : Book) : Term → Prop
  | lam  : Value bk (Lam q f)
  | prj  : Value bk (Prj h)
  | mat  : Value bk (Mat k h m)
  | efq  : Value bk Efq
  | lab  : Value bk (Lab k)
  | rfl  : Value bk Rfl
  | typ  : Value bk (Typ q)
  | all  : Value bk (All q A B)
  | sig  : Value bk (Sig q A B)
  | enu  : Value bk (Enu ks)
  | eql  : Value bk (Eql a b T)
  | tup  : (q.live = true → Value bk a) → Value bk b → Value bk (Tup q a b)
  | call : Book.get bk k = some d → Values bk xs → Walk bk d.v [] xs none →
           Value bk (Term.spine (Ref k) xs)

-- every live argument is a value
inductive Values (bk : Book) : List Arg → Prop
  | nil  : Values bk []
  | cons : (q.live = true → Value bk x) → Values bk xs →
           Values bk ((q, x) :: xs)

end



-- call-by-value evaluation of the live part
inductive Eval (bk : Book) : Term → Term → Prop
  | ann   : Eval bk (Ann x T) x
  | app_f : Eval bk f f' → Eval bk (App q f x) (App q f' x)
  | app_x : Value bk f → q.live = true → Eval bk x x' →
            Eval bk (App q f x) (App q f x')
  | beta  : p.live = q.live → (q.live = true → Value bk x) →
            (p = Q2 → Data x) → Eval bk (App q (Lam p f) x) (Term.inst f x)
  | split : q.live = true → Value bk (Tup r a b) →
            Eval bk (App q (Prj h) (Tup r a b))
              (App q (App (Quan.fld r q) h a) b)
  | hit   : q.live = true → Eval bk (App q (Mat k h m) (Lab k)) h
  | miss  : q.live = true → j ≠ k →
            Eval bk (App q (Mat k h m) (Lab j)) (App q m (Lab j))
  | call  : Book.get bk k = some d → Values bk xs → Walk bk d.v [] xs (some t) →
            Eval bk (Term.spine (Ref k) xs) t
  | lett  : q.live = true → Eval bk v v' → Eval bk (Let q v f) (Let q v' f)
  | unlet : (q.live = true → Value bk v) → (q = Q2 → Data v) →
            Eval bk (Let q v f) (Term.inst f v)
  | tup_a : q.live = true → Eval bk a a' → Eval bk (Tup q a b) (Tup q a' b)
  | tup_b : (q.live = true → Value bk a) → Eval bk b b' →
            Eval bk (Tup q a b) (Tup q a b')
  | rwt   : Eval bk e e' → Eval bk (Rwt e P f) (Rwt e' P f)
  | cast  : Eval bk (Rwt Rfl P f) f
  | min_a : Eval bk a a' → Eval bk (Min a b) (Min a' b)
  | min_b : Value bk a → Eval bk b b' → Eval bk (Min a b) (Min a b')
  | meet  : i ∈ QS → j ∈ QS → Eval bk (Min (Lab i) (Lab j)) (Term.qmin (Lab i) (Lab j))



-- parallel reduction is confluent (Takahashi)
def Claim.confluent : Prop :=
  ∀ bk a b c, Pars bk a b → Pars bk a c → ∃ d, Pars bk b d ∧ Pars bk c d



-- live evaluation terminates; no types needed
def Claim.halts : Prop :=
  ∀ bk t, Book.Live bk → Term.Closed t → Term.Live bk t →
    Acc (fun u t => Eval bk t u) t



-- PROOF
-- =====
--
-- The route has no logical relation, no step index and no universe:
-- Takahashi confluence, syntactic subject reduction and progress, and an
-- untyped measure for live evaluation. Type : Type is harmless, since
-- nothing here asks a type to normalize: conversion is joinability, and
-- termination measures the live term, not its type.
--
-- Why the measure works. A live term is affine (Term.live), and Eval
-- never enters a dead part. Each Eval step either removes a redex node
-- (β, split, hit, miss, let, ann, cast, meet) without copying a call,
-- since a q=1 value lands in at most one live place and a q=2 value is
-- Data (no λ, no call, no redex); or it fires a call, which replaces one call
-- label (def index, sizes of its columns) by the labels of the reached
-- branch: calls to earlier defs (a smaller index), and self-calls whose
-- columns are, left to right, no bigger and then smaller. Labels live in
-- a Dershowitz–Manna multiset, where each redex node adds the least
-- label. A dead region may hold Girard's paradox: it is never run, and
-- never measured.
--
-- Sections, and their key lemmas:
--   S1 Syntax             ren and sub compose (sub_sub)
--   S2 Confluence         Takahashi's complete development (confluent)
--   S3 Evaluator          wnf is a Pars step, conv a join (wnf_pars, conv_sound)
--   S4 Typing             typing survives substitution (typed_sub)
--   S5 Checker            each checker rule lands on its Typed rule (chk)
--   S6 Subject reduction  Par keeps the type (sr, eval_pars)
--   S7 Progress           canonical forms, the tree walk (progress, empty)
--   S8 Termination        a call becomes smaller calls (hcl, tp, halts)
--   S9 Assembly           consistent
--
-- Where the checker's side conditions are used:
--   live scrutinee (prj, mat, efq)  progress: Eval fires only on a live one
--   q=2 binder needs Data           canon_data: a q=2 copy holds no λ
--   uses (affinity)                 halts: β copies no call
--   called (order, descent)         hcl, tp, label_wf, dm_wf

-- Syntax
-- ------

theorem up_sub_ren : Subst.up σ ∘ Ren.up r = Subst.up (σ ∘ r) := by
  funext i; cases i <;> rfl



theorem sub_ren (t : Term) : sub σ (ren r t) = sub (σ ∘ r) t := by
  induction t generalizing σ r <;> simp [ren, sub, up_sub_ren, *]



theorem up_ren_sub : ren (Ren.up r) ∘ Subst.up σ = Subst.up (ren r ∘ σ) := by
  funext i; cases i; rfl; simp [Subst.up, ren_ren]; rfl



theorem ren_sub (t : Term) :
    ren r (sub σ t) = sub (ren r ∘ σ) t := by
  induction t generalizing σ r <;> simp [ren, sub, ← up_ren_sub, *]



theorem up_sub : sub (Subst.up τ) ∘ Subst.up σ = Subst.up (sub τ ∘ σ) := by
  funext i; cases i; rfl; simp [Subst.up, sub_ren, ren_sub]; rfl



theorem sub_sub (t : Term) :
    sub τ (sub σ t) = sub (sub τ ∘ σ) t := by
  induction t generalizing σ τ <;> simp [sub, ← up_sub, *]



theorem up_var : Subst.up Var = Var := by
  funext i; cases i <;> rfl



theorem sub_var (t : Term) : sub Var t = t := by
  induction t <;> simp [sub, up_var, *]



theorem ren_as_sub (t : Term) : ren r t = sub (Var ∘ r) t := by
  rw [← sub_ren, sub_var]



-- a term that r fixes is fixed by s, if s fixes r's fixed points
theorem ren_fix (t : Term) : ren r t = t → (∀ i, r i = i → s i = Var i) →
    sub s t = t := by
  have hu {r s} (h : ∀ i, r i = i → s i = Var i) i : Ren.up r i = i → Subst.up s i = Var i := by
    cases i <;> simp_all [Ren.up, Subst.up, ren]
  induction t generalizing r s <;> simp [ren, sub] <;> intros <;> apply_rules [hu, And.intro]



-- the closedness test of Def.check
theorem ren_closed : ren Nat.succ t = t → Closed t :=
  fun h _ => ren_fix t h fun i e => absurd e (Nat.succ_ne_self i)



theorem inst_sub : sub σ (inst f v) =
    inst (sub (Subst.up σ) f) (sub σ v) := by
  simp only [inst, sub_sub]; congr 1; funext i
  cases i; rfl; simp [Subst.up, sub_ren]; exact (sub_var _).symm



theorem sub_succ : sub (Subst.up σ) (ren Nat.succ t) = ren Nat.succ (sub σ t) := by
  rw [sub_ren, ren_sub]; rfl



theorem pick_inst : inst (ren (Ren.pick i) T) (Var i) = T := by
  have : Subst.one (Var i) ∘ Ren.pick i = Var := by
    funext j; simp [Ren.pick]; split <;> simp_all [Subst.one]
  rw [inst, sub_ren, this, sub_var]



theorem unspine_spine : unspine (spine t xs) [] = unspine t xs := by
  induction xs generalizing t; rfl; apply_assumption



-- a checker context, declaratively: a let variable is its value
def Ctx.drop : Ctx → Subst
  | [] => Var
  | (_, some v) :: c => Term.sub (Ctx.drop c) ∘ Subst.one v
  | (_, none) :: c => Subst.up (Ctx.drop c)



def Ctx.decl : Ctx → List Term
  | [] => []
  | (_, some _) :: c => Ctx.decl c
  | (A, none) :: c => Term.sub (Ctx.drop c) A :: Ctx.decl c



theorem drop_sub (c : Ctx) : sub (Ctx.drop c) ∘ Ctx.sub c = Ctx.drop c := by
  induction c; rfl
  rename_i e c ih; funext i; obtain ⟨_, _ | v⟩ := e <;> cases i <;> simp [Ctx.sub, sub_ren]; rfl
  exact (ren_sub _).symm.trans (congrArg _ (congrFun ih _))
  exact (sub_sub _).trans (congrArg (sub · v) ih)
  exact congrFun ih _



-- the checker's zeta vanishes under Ctx.drop
theorem zeta_drop : sub (Ctx.drop c) (Ctx.zeta c t) = sub (Ctx.drop c) t := by
  unfold Ctx.zeta; split <;> simp [sub_sub, drop_sub]



-- Confluence
-- ----------

-- the complete development: every redex of t, at once
open Classical in
noncomputable def Term.dev (bk : Book) : Term → Term
  | Ref k =>
    match Book.get bk k with
    | some d => if Closed d.v then d.v else Ref k
    | none   => Ref k
  | Ann x _ => dev bk x
  | Let _ v f => inst (dev bk f) (dev bk v)
  | All q A B => All q (dev bk A) (dev bk B)
  | Lam q f => Lam q.lin (dev bk f)
  | App _ (Lam _ f) x => inst (dev bk f) (dev bk x)
  | App q (Prj h) (Tup r a b) =>
    App q (App (Quan.fld r q) (dev bk h) (dev bk a)) (dev bk b)
  | App q (Mat k h m) (Lab j) =>
    if j = k then dev bk h else App q (dev bk m) (Lab j)
  | App q f x => App q (dev bk f) (dev bk x)
  | Sig q A B => Sig q (dev bk A) (dev bk B)
  | Tup q a b => Tup q (dev bk a) (dev bk b)
  | Prj h => Prj (dev bk h)
  | Mat k h m => Mat k (dev bk h) (dev bk m)
  | Eql a b T => Eql (dev bk a) (dev bk b) (dev bk T)
  | Typ q => Typ (dev bk q)
  | Min a b => qmin (dev bk a) (dev bk b)
  | Rwt Rfl _ f => dev bk f
  | Rwt e P f => Rwt (dev bk e) (dev bk P) (dev bk f)
  | t => t



theorem par_refl {t : Term} : Par bk t t := by
  induction t <;> constructor <;> first | assumption | exact .inl rfl



theorem pars_trans : Pars bk a b → Pars bk b c → Pars bk a c
  | .refl, g => g
  | .step s h, g => .step s (pars_trans h g)



-- Pars is a congruence where Par is one
theorem pars_map (C : Term → Term) (hC : ∀ {a b}, Par bk a b → Par bk (C a) (C b)) :
    Pars bk a b → Pars bk (C a) (C b)
  | .refl => .refl
  | .step s h => .step (hC s) (pars_map C hC h)



theorem pars2 (C : Term → Term → Term)
    (hC : ∀ {a a' b b'}, Par bk a a' → Par bk b b' → Par bk (C a b) (C a' b')) :
    Pars bk a a' → Pars bk b b' → Pars bk (C a b) (C a' b') := fun ha hb =>
  pars_trans (pars_map (C · b) (hC · par_refl) ha) (pars_map (C a') (hC par_refl) hb)



theorem pars3 (C : Term → Term → Term → Term)
    (hC : ∀ {a a' b b' c c'}, Par bk a a' → Par bk b b' → Par bk c c' → Par bk (C a b c) (C a' b' c')) :
    Pars bk a a' → Pars bk b b' → Pars bk c c' → Pars bk (C a b c) (C a' b' c') := fun ha hb hc =>
  pars_trans (pars2 (C · · c) (hC · · par_refl) ha hb) (pars_map (C a' b') (hC par_refl par_refl) hc)



theorem ren_inst : ren r (inst f v) =
    inst (ren (Ren.up r) f) (ren r v) := by
  simp [ren_as_sub, inst_sub, ← up_sub_ren, up_var]



-- qmin forces .Q2 and .Q0 on either side; else it is the meet itself
theorem qmin_eq : qmin (Lab "Q2") x = x ∧ qmin x (Lab "Q2") = x ∧
    qmin (Lab "Q0") x = Lab "Q0" ∧ qmin x (Lab "Q0") = Lab "Q0" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold qmin <;> split <;> simp_all



theorem qmin_view (a b : Term) : qmin a b = Min a b ∨ (a = Lab "Q2" ∧ qmin a b = b) ∨
    (b = Lab "Q2" ∧ qmin a b = a) ∨ ((a = Lab "Q0" ∨ b = Lab "Q0") ∧ qmin a b = Lab "Q0") ∨
    (a = Lab "Q1" ∧ b = Lab "Q1" ∧ qmin a b = Lab "Q1") := by
  unfold qmin; split <;> simp_all



-- a map that keeps labels and meets keeps a forced meet
theorem qmin_map (f : Term → Term) (hl : ∀ k, f (Lab k) = Lab k) :
    qmin a b = Min a b ∨ f (qmin a b) = qmin (f a) (f b) := by
  rcases qmin_view a b with e | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl | rfl, e⟩ | ⟨rfl, rfl, e⟩ <;> simp [e, hl, qmin_eq]



theorem par_ren : Par bk t u → Par bk (ren r t) (ren r u) := by
  intro h; induction h generalizing r <;> simp [ren, ren_inst]
  case delta hk hc => rw [ren_as_sub, hc]; exact .delta hk hc
  case meet => rcases qmin_map (ren r) (fun _ => rfl) with e | e <;> rw [e] <;> constructor <;> apply_assumption
  all_goals first | apply Par.split | apply Par.miss | constructor
  all_goals first | assumption | apply_assumption



theorem par_sub : Par bk t u → (∀ i, Par bk (σ i) (τ i)) →
    Par bk (sub σ t) (sub τ u) := by
  have U {σ τ} (h : ∀ i, Par bk (σ i) (τ i)) : ∀ i, Par bk (Subst.up σ i) (Subst.up τ i)
    | 0 => .var | _ + 1 => par_ren (h _)
  intro h hs; induction h generalizing σ τ <;> simp [sub, inst_sub]
  case delta hk hc => rw [hc]; exact .delta hk hc
  case meet => rcases qmin_map (sub τ) (fun _ => rfl) with e | e <;> rw [e] <;> constructor <;> apply_assumption <;> exact hs
  all_goals first | exact hs _ | apply Par.split | apply Par.miss | constructor
  all_goals first | assumption | (apply_assumption; (repeat apply U); exact hs)



theorem par_inst (hf : Par bk f f') (hv : Par bk v v') :
    Par bk (inst f v) (inst f' v') :=
  par_sub hf fun | 0 => hv | _ + 1 => .var



theorem qmin_par (ha : Par bk a A) (hb : Par bk b B) : Par bk (qmin a b) (qmin A B) := by
  have L {k c} (h : Par bk (Lab k) c) : c = Lab k := by cases h; rfl
  rcases qmin_view a b with e | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl | rfl, e⟩ | ⟨rfl, rfl, e⟩ <;> rw [e]
  · exact .meet ha hb
  all_goals (try cases L ha) <;> (try cases L hb) <;> (try simp only [qmin_eq]) <;> first
    | assumption | exact .lab | exact e ▸ .lab



-- Takahashi: dev t is a Par reduct of every Par reduct of t
theorem triangle (h : Par bk t u) : Par bk u (dev bk t) := by
  induction h
  case ref => (conv => arg 3; whnf); split <;> (try split) <;> constructor <;> assumption
  case delta hk hc => (conv => arg 3; whnf); simp [hk, hc, par_refl]
  case app h1 h2 ih1 ih2 =>
    cases h1 <;> try exact .app ih1 ih2
    case lam => cases ih1; exact .beta ‹_› ih2
    all_goals cases h2 <;> try exact .app ih1 ih2
    all_goals cases ih1
    · cases ih2; exact .split ‹_› ‹_› ‹_›
    · show Par _ _ (ite ..); split; subst_vars; exact .hit ‹_›; exact .miss ‹_› ‹_›
  case rwt h1 _ _ _ _ ih => cases h1 <;> first | exact .rwt ‹_› ‹_› ‹_› | exact .cast ih
  case split ih1 ih2 ih3 => exact .app (.app ih1 ih2) ih3
  case hit => show Par _ _ (ite ..); simpa
  case miss hne _ ih => show Par _ _ (ite ..); simp only [hne]; exact .app ih .lab
  all_goals first | assumption | (first | constructor | apply par_inst | apply qmin_par) <;>
    first | assumption | (rcases ‹_ ∨ _› with rfl | rfl <;> simp)



-- the strip lemma, from the triangle
theorem strip : Par bk a b → Pars bk a c → ∃ d, Pars bk b d ∧ Par bk c d := by
  intro h p; induction p generalizing b with
  | refl => exact ⟨_, .refl, h⟩
  | step s _ ih => exact (ih (triangle s)).imp fun _ h' => ⟨.step (triangle h) h'.1, h'.2⟩



theorem confluent : Claim.confluent := by
  intro bk a b c p q; induction p generalizing c with
  | refl => exact ⟨c, q, .refl⟩
  | step s _ ih => have ⟨_, h1, h2⟩ := strip s q; exact (ih _ h1).imp fun _ h => ⟨h.1, .step h2 h.2⟩



theorem conv_sub : Conv bk a b → Conv bk (sub σ a) (sub σ b) := fun ⟨_, h1, h2⟩ =>
  ⟨_, pars_map _ (par_sub · fun _ => par_refl) h1, pars_map _ (par_sub · fun _ => par_refl) h2⟩



-- the former of a type or value; 0 for a redex, variable or call
def Term.former : Term → Nat
  | Typ _     => 1
  | All _ _ _ => 2
  | Sig _ _ _ => 3
  | Enu _     => 4
  | Eql _ _ _ => 5
  | Lam _ _   => 6
  | Prj _     => 7
  | Mat _ _ _ => 8
  | Efq       => 9
  | Tup _ _ _ => 10
  | Lab _     => 11
  | Rfl       => 12
  | _         => 0



-- Evaluator
-- ---------

theorem par_spine : Par bk a b → Par bk (spine a xs) (spine b xs) :=
  match xs with
  | [] => id
  | _ :: _ => fun h => (par_spine (.app h par_refl) :)



theorem env_nil : Env.sub [] = Var := funext fun _ => rfl



theorem env_inst : sub (Env.sub (x :: e)) f =
    inst (sub (Subst.up (Env.sub e)) f) x := by
  simp only [inst, sub_sub]; congr 1; funext i
  cases i; rfl; simp [Subst.up, sub_ren]; exact (sub_var _).symm



-- the checker's book ck holds bk's defs, up to their opaque flags, and
-- their bodies are closed
def Sees (ck : Book) (bk : Book) : Prop :=
  ∀ k d, Book.get ck k = some d → ∃ o, Book.get bk k = some { d with o } ∧ Closed d.v



-- one strong induction on fuel for wnf, run, fire and val
theorem wnf_pars (hb : Sees ck bk) :
    Pars bk (spine t xs) (wnf ck cl n t xs).1 ∧
    (∀ {e u}, (run ck cl n t e xs).1 = some u → Pars bk (spine (sub (Env.sub e) t) xs) u) ∧
    (∀ {e u e' ys k}, fire ck cl n t e xs = (some (u, e', ys), k) →
      Pars bk (spine (sub (Env.sub e) t) xs) (spine (sub (Env.sub e') u) ys)) ∧
    ∀ {q v k}, val ck cl n q t = (v, k) → Pars bk t v := by
  induction n using Nat.strongRecOn generalizing t xs
  rename_i n ih
  have S {a b c} xs (p : Pars bk a b) (s : Par bk b c) :=
    pars_map (spine · xs) par_spine (pars_trans p (.step s .refl))
  have W {m a t xs} (p : Pars bk a (spine t xs)) (h : m < n := by omega) := pars_trans p (ih _ h).1
  have V {m x v k} (ex : wnf ck cl m x [] = (v, k)) (h : m < n := by omega) :=
    ex ▸ (ih _ h (t := x) (xs := [])).1
  have L {m q x v k} (ex : val ck cl m q x = (v, k)) (h : m < n := by omega) := (ih _ h (xs := [])).2.2.2 ex
  have R1 {m t e xs u} (h : (run ck cl m t e xs).1 = some u) (l : m < n := by omega) := (ih _ l).2.1 h
  have F {m t e xs u e' ys k} (ex : fire ck cl m t e xs = (some (u, e', ys), k)) (h : m < n := by omega) :=
    (ih _ h).2.2.1 ex
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold wnf; split <;> (try split) <;> (try split) <;> try exact .refl
    · exact W (S xs .refl (.unann par_refl))
    · exact W (S xs (pars2 (Let _) .lett (L ‹_›) .refl) (.unlet par_refl par_refl))
    · exact W .refl
    · exact W (S xs (pars3 Rwt .rwt (V ‹_›) .refl .refl) (.cast par_refl))
    · exact S xs (pars3 Rwt .rwt (V ‹_›) .refl .refl) par_refl
    · rename_i ha _ _ _ hb; exact S xs (pars2 Min .min (V ha) (V hb)) (.meet par_refl par_refl)
    · rename_i _ _ _ hd _ _ _ hr; have ⟨_, hd, hc⟩ := hb _ _ hd
      have := R1 (by rw [hr]); rw [env_nil, sub_var] at this
      exact W (.step (par_spine (.delta hd hc)) this)
    · rename_i hf; exact W (by simpa [env_nil, sub_var] using F hf)
  · unfold run at h
    split at h <;> (try split at h) <;> (try split at h) <;> (try cases h) <;> try exact .refl
    · exact (R1 h :)
    · exact pars_trans (F ‹_›) (R1 h)
  · unfold fire at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
    · rw [env_inst]; exact S _ (pars2 (App _) .app .refl (L ‹_›)) (.beta par_refl par_refl)
    all_goals refine S _ (pars2 (App _) .app .refl (V ‹_›)) ?_
    · exact .split par_refl par_refl par_refl
    · cases beq_iff_eq.1 ‹_›; exact .hit par_refl
    · exact .miss (by simp_all) par_refl
  · unfold val at h; split at h; split at h
    · split at h; split at h; cases h; exact pars_trans (V ‹_›) (pars2 (Tup _) .tup (L ‹_›) (L ‹_›))
    · exact V h
    · cases h; exact .refl



-- conv's fold: a true result passed every pair
theorem fold_true {g : Nat → Term → Term → Bool × Nat} : ∀ {s},
    (List.foldl (fun (r : Bool × Nat) (p : Term × Term) => if r.1 then g r.2 p.1 p.2 else r) s ps).1 = true →
    s.1 = true ∧ ∀ p ∈ ps, ∃ m, (g m p.1 p.2).1 = true := by
  induction ps <;> intro s h; exact ⟨h, nofun⟩
  rename_i ih; have ⟨h1, h2⟩ := ih h; simp only at h1; split at h1 <;> simp_all; exact ⟨_, h1⟩



theorem wnf_nil (hb : Sees ck bk) (e : wnf ck cl n t [] = (u, k)) : Pars bk t u :=
  (e ▸ (wnf_pars (t := t) (xs := []) hb).1 :)



-- the Prj motive commutes with a lifted substitution
theorem tup_sub : sub (Subst.up (Subst.up σ)) (sub (Subst.tup r) P) =
    sub (Subst.tup r) (sub (Subst.up σ) P) := by
  simp only [sub_sub]; congr 1; funext i; cases i; rfl
  show ren _ (ren _ _) = sub _ (ren _ _); rw [ren_ren, sub_ren, ren_as_sub]; rfl



theorem kindof_sub : sub σ (kindof q K) = kindof q (sub σ K) := by
  cases q <;> rfl



-- Checker
-- -------

section



-- the checker's monad, read as facts (local simp lemmas)
theorem ok_bind {x : Res α} {f : α → Res β} : (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]



theorem ok_map {x : Res α} : (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]



theorem ok_pure : (pure a : Res α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]



theorem ok_unit {P : Unit → Prop} : (∃ x, P x) ↔ P () := by grind



theorem ok_need : Res.need b e = .ok a ↔ b = true := by
  cases b <;> simp [Res.need] <;> rfl



theorem ok_fail : Ctx.fail c x o = .ok a ↔ False := ⟨nofun, nofun⟩



theorem ok_cneed : Ctx.need c r x o = .ok a ↔ r.1 = true := by
  rcases r with ⟨_ | _, _ | _⟩ <;> simp [Ctx.need, ok_fail] <;> rfl



theorem ok_if [Decidable p] {x y : Res Unit} :
    (if p then x >>= (fun _ => y) else y) = .ok () ↔ (p → x = .ok ()) ∧ y = .ok () := by
  by_cases hp : p <;> simp [hp, ok_bind, ok_unit]



attribute [local simp] ok_bind ok_map ok_pure ok_unit ok_need ok_cneed ok_fail ok_if



theorem table_at : ((Book.table n ds)[k]?).map (·.1) = (ds.findIdx? (·.k == k)).map (· + n) ∧
    ((Book.table n ds)[k]?).map (·.2) = ds.find? (·.k == k) := by
  induction ds generalizing n with
  | nil => simp [Book.table]
  | cons d ds ih =>
    have := @ih (n + 1)
    by_cases h : d.k = k <;> simp_all [Book.table, Std.HashMap.getElem?_insert, List.findIdx?_cons,
      Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]



theorem get_find : Book.get bk k = bk.defs.find? (·.k == k) := by
  simpa [Book.get, bk.ok] using (table_at (n := 0)).2



theorem index_find : Book.index bk k = bk.defs.findIdx? (·.k == k) := by
  simpa [Book.index, bk.ok] using (table_at (n := 0)).1



theorem index_lt (h : Book.index bk k = some j) : j < bk.length := by
  rw [index_find] at h; exact (List.findIdx?_eq_some_iff_findIdx_eq.1 h).1


end



-- Subject reduction
-- -----------------

theorem pconv (h : Par bk a b) : Conv bk a b := ⟨b, .step h .refl, .refl⟩



-- the former of a value's type
def Term.tform : Term → Nat
  | Typ _ | All .. | Sig .. | Enu _ | Eql .. => 1
  | Tup .. => 3
  | Lab _ => 4
  | Rfl => 5
  | _ => 2



-- a walk that needs more arguments reduces the spine to a λ or a λ-match
theorem walk_pars' (w : Walk bk t e xs o) : ∃ v,
    Pars bk (spine (sub (Env.sub e) t) xs) v ∧ (o = some v ∨ o = none ∧ takes v) := by
  induction w
  case app ih => exact ih
  case need t _ h => exact ⟨_, .refl, .inr ⟨rfl, by cases t <;> simp_all [takes, sub, spine]⟩⟩
  case done => exact ⟨_, .refl, .inl rfl⟩
  all_goals rename_i ih; have ⟨v, p, h⟩ := ih; refine ⟨v, .step ?_ p, h⟩; try rw [env_inst]
  all_goals refine par_spine (a := App ..) ?_; first | apply Par.beta | apply Par.split | apply Par.hit | apply Par.miss
  all_goals first | assumption | exact par_refl



theorem eval_pars : Book.Closed bk → Eval bk t u → Pars bk t u := by
  intro hc h; induction h
  case call e _ w =>
    obtain ⟨_, p, h | ⟨h, _⟩⟩ := walk_pars' w <;> cases h
    rw [env_nil, sub_var] at p; exact .step (par_spine (.delta e (hc _ _ e))) p
  all_goals first
    | (first | apply pars2 _ .app | apply pars2 _ .tup | apply pars2 _ .lett | apply pars2 _ .min | apply pars3 _ .rwt) <;>
      first | assumption | exact .refl
    | refine .step ?_ .refl; first | apply Par.split | apply Par.miss | constructor
  all_goals first | assumption | exact par_refl



-- Progress
-- --------

theorem spine_ft (h : t.former = 0 ∧ t.tform = 2) :
    (spine t xs).former = 0 ∧ (spine t xs).tform = 2 := by
  induction xs generalizing t with
  | nil => exact h
  | cons _ _ ih => exact ih ⟨rfl, rfl⟩



theorem spine_append : spine t (xs ++ ys) = spine (spine t xs) ys := by
  induction xs generalizing t <;> first | rfl | apply_assumption



theorem spine_snoc : spine t (xs ++ [(q, x)]) = App q (spine t xs) x := spine_append



theorem spine_head (e : t = spine (Ref k) xs) : unspine t [] = (Ref k, xs) := by
  rw [e, unspine_spine]; rfl



theorem values_snoc : Values bk (xs ++ [(q, x)]) ↔ Values bk xs ∧ (q.live → Value bk x) := by
  induction xs with
  | nil => exact ⟨fun | .cons h .nil => ⟨.nil, h⟩, fun ⟨_, h⟩ => .cons h .nil⟩
  | cons _ _ ih => exact ⟨fun | .cons h hs => (ih.1 hs).imp_left (.cons h),
      fun ⟨.cons h hs, hx⟩ => .cons h (ih.2 ⟨hs, hx⟩)⟩



-- a walk that needs more arguments needed them before the last one
theorem walk_init (w : Walk bk t e zs o) : zs = xs ++ [p] → o = none → Walk bk t e xs none := by
  induction w generalizing xs <;> intro h n
  case app hn _ ih => exact .app hn (ih (congrArg _ h) n)
  case need => cases xs <;> cases h
  case done => cases n
  all_goals
    cases xs; exact .need rfl
    cases h; constructor <;> first | assumption | (apply_assumption <;> first | rfl | exact n)



-- a value that is no former is a call
theorem value_inv (v : Value bk t) (e : t.former = 0) : ∃ k d xs, t = spine (Ref k) xs ∧
    Book.get bk k = some d ∧ Values bk xs ∧ Walk bk d.v [] xs none := by
  cases v <;> first | exact ⟨_, _, _, rfl, ‹_›, ‹_›, ‹_›⟩ | nomatch e



theorem value_app (v : Value bk (App q f x)) : Value bk f ∧ (q.live → Value bk x) := by
  have ⟨k, d, xs, e, hk, vs, w⟩ := value_inv v rfl
  rcases xs.eq_nil_or_concat with rfl | ⟨ys, ⟨q', x'⟩, rfl⟩; cases e
  simp only [List.concat_eq_append, spine_snoc] at e vs w; cases e
  exact (values_snoc.1 vs).imp_left (.call hk · (walk_init w rfl rfl))



theorem value_tup (v : Value bk (Tup q a b)) : (q.live → Value bk a) ∧ Value bk b := by
  generalize e : Tup q a b = t at v
  cases v <;> first
    | (cases e <;> exact ⟨‹_›, ‹_›⟩)
    | exact nomatch (congrArg former e).trans (spine_ft ⟨rfl, rfl⟩).1



theorem node_takes : takes t = true → node t = true := by
  cases t <;> simp_all [node, takes]



-- a walk that leaves the tree never needs more arguments
theorem walk_sn (w : Walk bk t e xs o) (w' : Walk bk t e xs none) : o = none := by
  induction w <;> cases w' <;> first
    | exact nomatch ‹node _ = false›.symm.trans (node_takes ‹_›)
    | simp_all [node, takes]



theorem eval_value : Eval bk t u → Value bk t → False := by
  intro h v; induction h
  case app_f ih => exact ih (value_app v).1
  case app_x l _ ih => exact ih ((value_app v).2 l)
  case tup_a l _ ih => exact ih ((value_tup v).1 l)
  case tup_b ih => exact ih (value_tup v).2
  case call hk _ w =>
    have ⟨_, _, _, e, hk', _, w'⟩ := value_inv v (spine_ft ⟨rfl, rfl⟩).1
    cases (spine_head e).symm.trans (spine_head rfl); cases hk.symm.trans hk'; exact nomatch walk_sn w w'
  all_goals have ⟨_, _, _, e, _⟩ := value_inv v rfl; simpa [unspine] using spine_head e



theorem tform_call : (spine (Ref k) xs).tform = 2 := (spine_ft ⟨rfl, rfl⟩).2



theorem inst_succ : inst (Typ (ren Nat.succ g)) v = Typ g := congrArg Typ ((sub_ren g).trans (sub_var g))



theorem index_of_get (h : Book.get bk k = some d) : ∃ i, Book.index bk k = some i :=
  Option.isSome_iff_exists.1 (by simpa [Book.index, Book.get] using congrArg Option.isSome h)



-- what a closed typed λ or λ-match needs of its argument x at q
def Fire (q : Quan) (x : Term) : Term → Prop
  | Lam p _   => p.live = q.live ∧ (p = Q2 → Data x)
  | Prj _     => q.live ∧ ∃ r a b, x = Tup r a b
  | Mat _ _ _ => q.live ∧ ∃ j, x = Lab j
  | Efq       => False
  | _         => True



-- an env entry is a value, unused, or a variable
def EnvOk (bk : Book) (e : List Term) (t : Term) : Prop :=
  ∀ i, Value bk (Env.sub e i) ∨ uses t i = 0 ∨ ∃ w, Env.sub e i = Var w



theorem live_or (ih : Quan.live q = true → Value bk x ∨ ∃ u, Eval bk x u) :
    (Quan.live q = true → Value bk x) ∨ ∃ u, Quan.live q = true ∧ Eval bk x u := by grind



-- Termination
-- -----------

-- unfolds the live check into props
syntax "lv" (Lean.Parser.Tactic.location)? : tactic


macro_rules
  | `(tactic| lv $[$l]?) =>
    `(tactic| simp only [Live, Term.live, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] $[$l]?)



-- the size of a term's live part
def Term.size : Term → Nat
  | Ann x _ => size x + 1
  | Let q v f => (if q.live then size v else 0) + size f + 1
  | Lam _ f => size f + 1
  | App q f x => size f + (if q.live then size x else 0) + 1
  | Tup q a b => (if q.live then size a else 0) + size b + 1
  | Prj h => size h + 1
  | Mat _ h m => size h + size m + 1
  | Rwt e _ f => size e + size f + 1
  | _ => 1



-- a column's size: a closed value's live size, 0 when dead, none (ω)
-- when not yet a closed value
open Classical in
noncomputable def Arg.size (bk : Book) : Arg → Option Nat
  | (q, x) =>
    if q.live then
      if Value bk x ∧ Term.Closed x then some (Term.size x) else none
    else
      some 0



-- a call's label: its def's index + 1, and the sizes of its first n
-- arguments, where n bounds the columns of the def's tree; a redex
-- node's label is (0, []), below every call's
abbrev Label := Nat × List (Option Nat)



-- the first n entries of l, padded with none
def Pad : Nat → List (Option Nat) → List (Option Nat)
  | 0, _ => []
  | n + 1, l => l.headD none :: Pad n l.tail



noncomputable def Term.label (bk : Book) (k : String) (xs : List Arg) : Label :=
  let i := (Book.index bk k).getD 0 + 1
  let n := ((Book.get bk k).map (fun d => size d.v)).getD 0
  (i, Pad n (xs.map (Arg.size bk)))



-- the labels of the live calls and redex nodes of a term; top is false
-- on an App head
noncomputable def Term.labels (bk : Book) : Bool → Term → List Label
  | top, App q f x =>
    let s :=
      match top, unspine (App q f x) [] with
      | true, (Ref k, xs) => [label bk k xs]
      | _,    _           => []
    let f := labels bk false f
    let x := if q.live then labels bk true x else []
    s ++ f ++ x
  | top, Ref k => if top then [label bk k []] else []
  | _, Ann x _ => (0, []) :: labels bk true x
  | _, Let q v f =>
    let v := if q.live then labels bk true v else []
    (0, []) :: v ++ labels bk true f
  | _, Lam _ f => (0, []) :: labels bk true f
  | _, Tup q a b =>
    let a := if q.live then labels bk true a else []
    a ++ labels bk true b
  | _, Prj h => (0, []) :: labels bk true h
  | _, Mat _ h m => (0, []) :: labels bk true h ++ labels bk true m
  | _, Rwt e _ f => (0, []) :: labels bk true e ++ labels bk true f
  | _, Min a b => (0, []) :: labels bk true a ++ labels bk true b
  | _, _ => []



def Size.lt : Option Nat → Option Nat → Prop
  | some a, some b => a < b
  | some _, none   => True
  | none,   _      => False



-- lexicographic order on lists of one length
inductive Lex (r : α → α → Prop) : List α → List α → Prop
  | head : r a b → as.length = bs.length → Lex r (a :: as) (b :: bs)
  | tail : Lex r as bs → Lex r (a :: as) (a :: bs)



def Label.lt (l m : Label) : Prop :=
  l.1 < m.1 ∨ (l.1 = m.1 ∧ Lex Size.lt l.2 m.2)



-- Dershowitz–Manna: replace one element by any number of smaller ones
def DM1 (r : α → α → Prop) (M N : List α) : Prop :=
  ∃ X x ys, List.Perm N (x :: X) ∧ List.Perm M (ys ++ X) ∧ ∀ y ∈ ys, r y x



def DM (r : α → α → Prop) : List α → List α → Prop :=
  Relation.TransGen (DM1 r)



def DMle (r : α → α → Prop) (M N : List α) : Prop :=
  List.Perm M N ∨ DM r M N



theorem dm1_perm (h : DM1 r M N) (hm : List.Perm M M') (hn : List.Perm N N') : DM1 r M' N' :=
  let ⟨_, _, _, h1, h2, h3⟩ := h; ⟨_, _, _, hn.symm.trans h1, hm.symm.trans h2, h3⟩



theorem acc_perm (h : Acc (DM1 r) M) (hp : List.Perm M M') : Acc (DM1 r) M' :=
  ⟨_, fun _ d => h.inv (dm1_perm d (.refl _) hp.symm)⟩



-- the classic proof: accessibility of each element lifts to
-- accessibility of the lists built from it (Nipkow's formulation)
theorem dm_wf : WellFounded r → WellFounded (DM r) := by
  intro hr; classical
  refine WellFounded.transGen ⟨fun M => ?_⟩
  induction M with
  | nil => exact ⟨_, fun _ ⟨_, _, _, h, _⟩ => nomatch h.length_eq⟩
  | cons a M ih =>
    revert M
    induction a using hr.induction with
    | _ a iha =>
    have hZ (Z : List _) : (∀ z ∈ Z, r z a) → ∀ N, Acc (DM1 r) N → Acc (DM1 r) (Z ++ N) :=
      Z.rec (fun _ _ => id) fun z _ ih hz N h => iha z (hz z (.head _)) _ (ih (fun y hy => hz y (.tail _ hy)) N h)
    intro M hM
    induction hM with
    | intro M hM ihM =>
    refine ⟨_, fun M' ⟨X, x, ys, h1, h2, h3⟩ => ?_⟩
    by_cases e : a = x
    · subst e; exact acc_perm (hZ ys h3 _ ⟨_, hM⟩) ((h1.cons_inv.append_left ys).trans h2.symm)
    · have hX := List.perm_cons_erase ((List.mem_cons.1 (h1.subset (.head _))).resolve_left e)
      exact acc_perm (ihM _ ⟨_, x, ys, (h1.trans ((hX.cons x).trans (.swap _ _ _))).cons_inv, .refl _, h3⟩)
        ((List.perm_middle.symm.trans (hX.append_left ys).symm).trans h2.symm)



theorem lex_len : Lex r a b → a.length = b.length := by
  intro h; induction h <;> simp_all



-- Nat.lt, then Lex over Size.lt on lists of one length, by
-- induction on the length
theorem label_wf : WellFounded Label.lt := by
  have hn : ∀ n, Acc Size.lt (some n) := fun n => Nat.strongRecOn n fun n ih => ⟨_, fun | some b, hb => ih b hb⟩
  have hs : WellFounded Size.lt := ⟨fun _ => ⟨_, fun | some b, _ => hn b⟩⟩
  have hl : ∀ n (l : List (Option Nat)), l.length = n → Acc (Lex Size.lt) l := by
    intro n; induction n with
    | zero => rintro (_ | _) ⟨⟩; exact ⟨_, nofun⟩
    | succ n ih =>
      rintro (_ | ⟨b, l⟩) hl <;> simp at hl
      induction b using hs.induction generalizing l with | _ b ihb =>
      induction ih l hl with | intro l _ ihl =>
      exact ⟨_, fun | _, .head h e' => ihb _ h _ (e'.trans hl) | _, .tail h => ihl _ h ((lex_len h).trans hl)⟩
  exact Subrelation.wf (Prod.lex_def.2 ·) (Prod.lex Nat.lt_wfRel ⟨_, ⟨fun l => hl _ l rfl⟩⟩).wf



theorem dm_app (h : DM r M N) : DM r (M ++ P) (N ++ P) := by
  have : ∀ {M N}, DM1 r M N → DM1 r (M ++ P) (N ++ P) := fun ⟨X, x, ys, h1, h2, h3⟩ =>
    ⟨X ++ P, x, ys, h1.append_right P, by simpa using h2.append_right P, h3⟩
  induction h; exact .single (this ‹_›); exact .tail ‹_› (this ‹_›)



theorem dm_perm (h : DM r M N) (hm : List.Perm M M') (hn : List.Perm N N') : DM r M' N' := by
  induction h generalizing N' with
  | single h => exact .single (dm1_perm h hm hn)
  | tail _ h ih => exact .tail (ih (.refl _)) (dm1_perm h (.refl _) hn)



theorem le_dm (h1 : DMle r M N) (h2 : DM r N P) : DM r M P :=
  h1.elim (fun p => dm_perm h2 p.symm (.refl _)) (·.trans h2)



theorem le_le (h1 : DMle r M N) (h2 : DMle r N P) : DMle r M P :=
  h2.elim (fun p => h1.elim (fun q => .inl (q.trans p)) (fun d => .inr (dm_perm d (.refl _) p)))
    (fun d => .inr (le_dm h1 d))



theorem dm_left (h : DM r N N') : DM r (P ++ N) (P ++ N') :=
  dm_perm (dm_app h) List.perm_append_comm List.perm_append_comm



-- DM is monotone: DMle on a part, DM on another, gives DM on the sum
theorem dm_mono : DMle r M M' → DM r N N' → DM r (M ++ N) (M' ++ N') :=
  fun h1 h2 => h1.elim (fun p => dm_perm (dm_left h2) (.refl _) (p.append_right _))
    fun d => (dm_left h2).trans (dm_app d)



theorem le_app (h1 : DMle r M M') (h2 : DMle r N N') : DMle r (M ++ N) (M' ++ N') :=
  h2.elim (fun p => le_le (h1.elim (fun q => .inl (q.append_right _)) (fun d => .inr (dm_app d)))
    (.inl (p.append_left _))) (fun d => .inr (dm_mono h1 d))



theorem le_rfl : DMle r M M := .inl (.refl _)



theorem dm_repl (h : DMle r M N) (ho : ∀ y ∈ O, r y x) : DM r (O ++ M) (x :: N) :=
  le_dm (le_app le_rfl h) (.single ⟨N, x, O, .refl _, .refl _, ho⟩)



theorem dm_cons (h : DMle r M N) : DM r M (x :: N) := dm_repl (O := []) h nofun



theorem le_nil : DMle r [] N := by
  induction N; exact le_rfl; exact .inr (dm_cons ‹_›)



-- Labels
-- ------

def Size.le (a b : Option Nat) : Prop := a = b ∨ Size.lt a b



-- pointwise ≤ on size lists; the right one may be shorter (ω after it)
inductive SL : List (Option Nat) → List (Option Nat) → Prop
  | nil : SL l []
  | cons : Size.le a b → SL l m → SL (a :: l) (b :: m)



abbrev ArgsLe (bk : Book) (xs ys : List Arg) : Prop :=
  SL (xs.map (Arg.size bk)) (ys.map (Arg.size bk))



-- the label of a spine's head
noncomputable def Term.hd (bk : Book) : Term × List Arg → List Label
  | (Ref k, xs) => [label bk k xs]
  | _ => []



noncomputable def Args.labels (bk : Book) : List Arg → List Label
  | [] => []
  | (q, x) :: xs => (if q.live then Term.labels bk true x else []) ++ Args.labels bk xs



theorem size_le_none : Size.le a none := by
  cases a <;> simp [Size.le, Size.lt]



theorem sl_app : SL (l ++ m) l := by
  induction l; exact .nil; exact .cons (.inl rfl) ‹_›



theorem sl_refl : SL l l := by simpa using sl_app (l := l) (m := [])



theorem pad_len : (Pad n l).length = n := by
  induction n generalizing l <;> simp_all [Pad]



theorem label_le (h : ArgsLe bk xs ys) : DMle Label.lt [label bk k xs] [label bk k ys] := by
  have P {n A B} (h : SL A B) : Pad n A = Pad n B ∨ Lex Size.lt (Pad n A) (Pad n B) := by
    induction n generalizing A B with | zero => exact .inl rfl | succ n ih => ?_
    obtain ⟨e | e, h⟩ : Size.le (A.headD none) (B.headD none) ∧ SL A.tail B.tail := by
      cases h <;> simp [size_le_none, SL.nil, *]
    · rcases ih h with e' | e' <;> simp only [Pad, e, e', true_or]; exact .inr (.tail e')
    · exact .inr (.head e (by simp [pad_len]))
  simp only [label]; exact (P h).elim (fun e => .inl (by rw [e]))
    fun e => .inr (dm_repl (O := [_]) le_nil fun y hy => List.mem_singleton.1 hy ▸ .inr ⟨rfl, e⟩)



theorem hd_le (h : ArgsLe bk xs ys) : DMle Label.lt (Term.hd bk (t, xs)) (Term.hd bk (t, ys)) := by
  cases t <;> first | exact le_rfl | exact label_le h



theorem unspine_app : unspine t xs = ((unspine t []).1, (unspine t []).2 ++ xs) := by
  induction t generalizing xs with
  | App q f x ihf _ => simp only [unspine]; rw [ihf, ihf (xs := [(q, x)])]; simp
  | _ => rfl



theorem labels_app : labels bk false (App q f x) =
    labels bk false f ++ (if q.live then labels bk true x else []) := by
  simp [labels]



theorem labels_top (t : Term) :
    labels bk true t = Term.hd bk (unspine t []) ++ labels bk false t := by
  cases t <;> try rfl
  simp only [labels]; split <;> simp_all [Term.hd]



theorem labels_spine (t : Term) (es : List Arg) : labels bk true (spine t es) =
    Term.hd bk (unspine t es) ++ labels bk false t ++ Args.labels bk es := by
  induction es generalizing t <;> simp [spine, Args.labels, labels_top, unspine, labels_app, *]



theorem args_append : Args.labels bk (xs ++ ys) = Args.labels bk xs ++ Args.labels bk ys := by
  induction xs <;> simp [Args.labels, *]



theorem hd_ext : DMle Label.lt (Term.hd bk (unspine u es)) (Term.hd bk (unspine u [])) := by
  rw [unspine_app (xs := es)]; exact hd_le (by simpa [ArgsLe] using sl_app)



-- extra arguments only lower the head's label
theorem labels_ext (u : Term) (es : List Arg) : DMle Label.lt (labels bk true (spine u es))
    (labels bk true u ++ Args.labels bk es) := by
  rw [labels_spine, labels_top]; exact le_app (le_app hd_ext le_rfl) le_rfl



theorem size_sub : Size.le (Arg.size bk (q, sub σ y)) (Arg.size bk (q, y)) := by
  by_cases h : Value bk y ∧ Closed y
  · rw [h.2 σ]; exact .inl rfl
  · simp only [Arg.size, h]; split <;> first | exact size_le_none | exact .inl rfl



-- Closed terms, uses
-- ------------------

theorem closed_ren (h : Closed t) : ren r t = t := by
  rw [ren_as_sub]; exact h _



theorem closed_iff : Closed t ↔ ren Nat.succ t = t :=
  ⟨closed_ren, ren_closed⟩



-- splits a closed term into its closed parts
macro "cl" t:term : tactic => `(tactic| simpa [closed_iff, ren] using $t)



-- Par keeps the terms that a renaming fixes, so Pars keeps Closed
theorem par_fix (h : Par bk t u) : ren r t = t → ren r u = u := by
  induction h generalizing r <;> simp_all [ren, ren_inst, closed_ren]
  case meet => intros; rcases qmin_map (ren r) (fun _ => rfl) with e | e <;> rw [e] <;> simp_all [ren]



theorem pars_closed (p : Pars bk t u) (c : Closed t) : Closed u := by
  induction p with | refl => exact c | step s _ ih => exact ih (ren_closed (par_fix s (closed_ren c)))



theorem closed_spine : Closed (spine t as) ↔ Closed t ∧ ∀ a ∈ as, Closed a.2 := by
  induction as generalizing t with
  | nil => simp [spine]
  | cons a as ih => simp [spine, ih, closed_iff, ren, and_assoc]



theorem closed_uses (h : Closed y) : uses y i = 0 := by
  have (t : Term) : ∀ {r i}, (∀ v, i ≠ r v) → uses (ren r t) i = 0 := by
    induction t <;> intro r i h <;> simp_all [ren, uses] <;> apply_assumption <;> rintro (_ | _) <;> simp [Ren.up, h]
  exact closed_ren (r := (· + i + 1)) h ▸ this y fun v => by omega



-- τ keeps each variable below n, and sends the others to closed terms
-- or to variables from n on
def UH (τ : Subst) (n : Nat) : Prop :=
  ∀ v, (v < n → τ v = Var v) ∧ (n ≤ v → (∃ w, n ≤ w ∧ τ v = Var w) ∨ Closed (τ v))



theorem uh_up (h : UH τ n) : UH (Subst.up τ) (n + 1) := by
  rintro (_ | v)
  · exact ⟨fun _ => rfl, by omega⟩
  have ⟨h1, h2⟩ := h v
  refine ⟨fun e => by simp [Subst.up, h1 (by omega), ren], fun e => ?_⟩
  rcases h2 (by omega) with ⟨w, hw, e'⟩ | hc <;> simp [Subst.up, ren, closed_ren, *]



theorem uses_sub (t : Term) : UH τ n → i < n → uses (sub τ t) i = uses t i := by
  induction t generalizing τ n i <;> intro h hi
  case Var v =>
    obtain ⟨h1, h2⟩ := h v
    by_cases e : v < n
    · simp [sub, h1 e]
    · rcases h2 (by omega) with ⟨w, hw, e'⟩ | hc <;>
        simp [sub, uses, closed_uses, *, show i ≠ v by omega] <;> omega
  all_goals simp only [sub, uses] <;> (try split) <;> (try refine congr (congrArg HAdd.hAdd ?_) ?_) <;>
    first | rfl | apply_assumption <;> first | exact h | exact uh_up h | omega



-- Live terms
-- ----------

def RefOK (bk : Book) (u : Term) : Prop :=
  ∀ k, (unspine u []).1 = Ref k → (Book.index bk k).isSome



theorem called_ok : called g u = true → RefOK g.book u := by
  intro h k e; unfold called at h; split at h <;> (try split at h) <;> simp_all
  rename_i H; exact (H _ _ (Prod.ext e rfl)).elim



theorem ok_called (hi : g.self = g.book.length) (h : RefOK g.book u) : called g u = true := by
  simp only [called]; split
  next k _ e => obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (h k (by rw [e])); simp [hj, hi, index_lt hj]
  next => rfl



theorem live_call (h : Term.live g true t = true) (e : unspine t [] = (Ref k, ys)) :
    ∃ j, Book.index g.book k = some j ∧ (j < g.self ∨ (j = g.self ∧ Arg.descend g 0 ys = .lt)) := by
  have c : called g t = true := by cases t <;> simp_all [Term.live, unspine]
  simp only [called, e] at c; split at c <;> simp_all



theorem live_ok : Term.live g true u = true → RefOK g.book u :=
  fun h _ e => let ⟨_, hj, _⟩ := live_call h (Prod.ext e rfl); by simp [hj]



theorem live_mono : Term.live g true u = true → Term.live g false u = true := by
  cases u <;> simp_all [Term.live]



-- σ's used values are closed and live at any outer guard
def LiveV (bk : Book) (σ : Subst) (t : Term) : Prop :=
  ∀ v, (∃ w, σ v = Var w) ∨ (Closed (σ v) ∧ (uses t v ≠ 0 →
    ∀ G : Guard, G.book = bk → G.self = bk.length → Term.live G true (σ v) = true))



theorem livev_mono (h : LiveV bk σ t)
    (hu : ∀ v, uses t' v ≠ 0 → uses t v ≠ 0 := by intro v n; simp_all [uses]) :
    LiveV bk σ t' :=
  fun v => (h v).imp_right fun ⟨c, u⟩ => ⟨c, fun n => u (hu v n)⟩



theorem livev_up (h : LiveV bk σ t) (hu : ∀ v, uses f (v + 1) ≠ 0 → uses t v ≠ 0) :
    LiveV bk (Subst.up σ) f := by
  rintro (_ | v)
  · exact .inl ⟨0, rfl⟩
  rcases h v with ⟨w, e⟩ | ⟨c, u⟩ <;> simp [Subst.up, ren, closed_ren, *]
  exact .inr fun n => u (hu v n)



theorem uh_live (h : LiveV bk σ t) : UH (Subst.up σ) 1 :=
  uh_up fun v => ⟨by omega, fun _ => (h v).imp (fun ⟨w, e⟩ => ⟨w, by omega, e⟩) And.left⟩



theorem qlive {q : Quan} (h : q.live = false ∨ A) (ih : q.live = true → A → B) : q.live = false ∨ B := by grind



theorem head_used (h : (unspine t []).1 = Var v) : uses t v ≠ 0 := by
  induction t with
  | App q f x ih => rw [unspine, unspine_app] at h; simp [uses, ih h]
  | Var => simp_all [unspine, uses]
  | _ => simp [unspine] at h



theorem ok_app : RefOK bk (App q t x) ↔ RefOK bk t := by
  simp only [RefOK, unspine]; rw [unspine_app]



theorem ref_sub (h : RefOK bk t) (hv : ∀ v, (unspine t []).1 = Var v → RefOK bk (σ v)) :
    RefOK bk (sub σ t) := by
  induction t with
  | App q f x ih _ =>
    refine ok_app.2 (ih (ok_app.1 h) fun v e => hv v ?_)
    rwa [unspine, unspine_app]
  | Var v => exact hv v rfl
  | _ => first | exact h | intro k hk; cases hk



theorem live_sub (t : Term) : ∀ {g G : Guard} {σ top}, G.book = g.book → G.self = G.book.length →
    LiveV G.book σ t → Term.live g top t = true → Term.live G top (sub σ t) = true := by
  induction t <;> intro g G σ top hb hi hv h <;> simp only [sub] <;> lv at h ⊢
  case Var v =>
    rcases hv v with ⟨w, e⟩ | ⟨_, h⟩
    · simp [e, Term.live]
    · have := h (by simp [uses]) G rfl hi
      exact top.rec (live_mono this) this
  case Ref => exact h.imp_right fun c => ok_called hi (hb ▸ called_ok c)
  case App q f x ihf ihx =>
    refine ⟨⟨h.1.1.imp_right fun c => ok_called hi ?_, ihf hb hi (livev_mono hv) h.1.2⟩,
      qlive h.2 fun hq => ihx hb hi (livev_mono hv)⟩
    refine ref_sub (t := App q f x) (hb ▸ called_ok c) fun v e => ?_
    rcases hv v with ⟨w, e'⟩ | ⟨_, u⟩
    · intro k hk; simp [e', unspine] at hk
    · exact live_ok (u (head_used e) G rfl hi)
  case Lam f ih =>
    exact ⟨uses_sub f (uh_live hv) Nat.one_pos ▸ h.1,
      ih (g := g.bind none) (G := G.bind none) hb hi (livev_up hv fun _ n => n) h.2⟩
  case Let f ihv ihf =>
    exact ⟨⟨uses_sub f (uh_live hv) Nat.one_pos ▸ h.1.1,
      qlive h.1.2 fun hq => ihv hb hi (livev_mono hv)⟩,
      ihf (g := g.bind none) (G := G.bind none) hb hi (livev_up hv fun _ n => by simp [uses, n]) h.2⟩
  case Tup iha ihb =>
    exact ⟨qlive h.1 fun hq => iha hb hi (livev_mono hv), ihb hb hi (livev_mono hv) h.2⟩
  case Mat iha ihb | Rwt iha _ ihb | Min iha ihb =>
    exact ⟨iha hb hi (livev_mono hv) h.1, ihb hb hi (livev_mono hv) h.2⟩
  case Prj ih | Ann ih _ => exact ih hb hi (livev_mono hv) h



theorem live_up (h : Term.live g top u = true) (hb : G.book = g.book) (hi : G.self = G.book.length) :
    Term.live G top u = true :=
  sub_var u ▸ live_sub u hb hi (fun v => .inl ⟨v, rfl⟩) h



theorem live_top (hi : g.self = g.book.length) :
    Term.live g true u = true ↔ RefOK g.book u ∧ Term.live g false u = true := by
  refine ⟨fun h => ⟨live_ok h, live_mono h⟩, fun ⟨h1, h2⟩ => ?_⟩
  cases u <;> simp_all [Term.live]
  case App | Ref => exact ok_called hi h1



theorem live_spine : Live bk (spine t as) ↔
    Live bk t ∧ ∀ a ∈ as, a.1.live = true → Live bk a.2 := by
  induction as generalizing t with
  | nil => simp [spine]
  | cons a as ih =>
    obtain ⟨q, x⟩ := a
    rw [spine, ih]
    cases hq : q.live <;> simp [Live, live_top (g := ⟨bk, bk.length, [], [], []⟩) rfl, Term.live,
      Iff.intro called_ok (ok_called (g := ⟨bk, bk.length, [], [], []⟩) rfl), ok_app, and_assoc, hq]



theorem uses_unspine (m : a ∈ (unspine t []).2) (hq : a.1.live = true) : uses a.2 v ≤ uses t v := by
  induction t with
  | App q f x ih =>
    rw [unspine, unspine_app] at m; simp at m
    rcases m with m | rfl
    · exact Nat.le_trans (ih m) (by simp [uses])
    · simp [uses, hq]
  | _ => simp [unspine] at m



-- Budgets
-- -------

-- a binder's view of ls: its own variable has no labels
def Bud.up (ls : Nat → List Label) : Nat → List Label
  | 0 => []
  | v + 1 => ls v



-- the labels that t's live variables get from ls, once per live use
def Term.bud (ls : Nat → List Label) : Term → List Label
  | Var i => ls i
  | Ann x _ => bud ls x
  | Let q v f => (if q.live then bud ls v else []) ++ bud (Bud.up ls) f
  | Lam _ f => bud (Bud.up ls) f
  | App q f x => bud ls f ++ (if q.live then bud ls x else [])
  | Tup q a b => (if q.live then bud ls a else []) ++ bud ls b
  | Prj h => bud ls h
  | Mat _ h m => bud ls h ++ bud ls m
  | Rwt e _ f => bud ls e ++ bud ls f
  | Min a b => bud ls a ++ bud ls b
  | _ => []



-- no labels in, none out
theorem bud_nil (t : Term) : ∀ {ls : Nat → List Label}, (∀ v, ls v = []) → bud ls t = [] := by
  induction t <;> intro ls h <;> simp_all [bud] <;> apply_assumption <;> rintro (_ | _) <;> simp [Bud.up, h]



theorem le_sub' : DMle r N (M ++ N) := le_app le_nil le_rfl



theorem le_sub : DMle r M (M ++ N) := le_le le_sub' (.inl List.perm_append_comm)



-- two parts, each below its rest and a leftover: the rests, then the
-- leftovers
theorem once2 (h1 : DMle r A (A' ++ X)) (h2 : DMle r B (B' ++ Y)) (h3 : DMle r (X ++ Y) Z) :
    DMle r (A ++ B) (A' ++ B' ++ Z) :=
  le_le (le_app h1 h2)
    (le_le (.inl (by simp [List.perm_append_left_iff, List.perm_append_comm_assoc])) (le_app le_rfl h3))



-- the leftovers of two parts' a and b uses fit in one: a variable used
-- twice has no labels
theorem once_add (h : 2 ≤ a + b → l = []) :
    DMle r ((if a = 0 then [] else l) ++ (if b = 0 then [] else l)) (if a + b = 0 then [] else l) := by
  by_cases hu : 2 ≤ a + b; simpa [h hu] using le_rfl
  exact .inl (.of_eq (by split <;> split <;> simp_all <;> omega))



-- a dead part adds no labels and no uses
theorem once_if {q : Quan} (h : q.live = true → DMle r A (A' ++ (if u = 0 then [] else l))) :
    DMle r (if q.live then A else [])
      ((if q.live then A' else []) ++ (if (if q.live then u else 0) = 0 then [] else l)) := by
  cases hq : q.live <;> simp [le_rfl, h, hq]



-- a variable used once, or of no labels, gives its labels once
theorem bud_once (t : Term) : ∀ {ls : Nat → List Label} {i}, (2 ≤ uses t i → ls i = []) →
    DMle Label.lt (bud ls t)
      (bud (fun v => if v = i then [] else ls v) t ++ (if uses t i = 0 then [] else ls i)) := by
  have up : ∀ {ls : Nat → List Label} {i}, Bud.up (fun v => if v = i then [] else ls v) =
      fun v => if v = i + 1 then [] else Bud.up ls v := funext fun v => by cases v <;> simp [Bud.up]
  induction t <;> intro ls i h <;> simp only [bud, uses, up] at h ⊢
  case Var j => by_cases e : j = i <;> simp [e, Ne.symm] <;> exact le_rfl
  case App ihf ihx =>
    exact once2 (ihf fun e => h (by omega)) (once_if fun hq => ihx fun e => h (by simp [hq]; omega)) (once_add h)
  case Let iha ihb | Tup iha ihb =>
    exact once2 (once_if fun hq => iha fun e => h (by simp [hq]; omega)) (ihb fun e => h (by omega)) (once_add h)
  case Mat iha ihb | Rwt iha _ ihb | Min iha ihb =>
    exact once2 (iha fun e => h (by omega)) (ihb fun e => h (by omega)) (once_add h)
  case Lam ih | Prj ih | Ann ih _ => exact ih h
  all_goals exact le_nil



-- the image of a substitution under the labels, and its used budget
def Good (L : Label) (P : Prop) (A B C : List Label) : Prop :=
  ∃ O, DMle Label.lt A (O ++ B) ∧ DMle Label.lt O C ∧ (P → ∀ l ∈ O, Label.lt l L)



theorem good_nil : Good L P [] B [] := ⟨[], le_nil, le_rfl, by simp⟩



theorem good_app (h1 : Good L P A1 B1 C1) (h2 : Good L P A2 B2 C2) :
    Good L P (A1 ++ A2) (B1 ++ B2) (C1 ++ C2) :=
  let ⟨O1, a1, b1, c1⟩ := h1; let ⟨O2, a2, b2, c2⟩ := h2
  ⟨O1 ++ O2, once2 a1 a2 le_rfl, le_app b1 b2,
    fun p l hl => (List.mem_append.1 hl).elim (c1 p l) (c2 p l)⟩



theorem good_cons (hL : 0 < L.1) (h : Good L P A B C) : Good L P ((0, []) :: A) B ((0, []) :: C) :=
  good_app (B1 := []) ⟨[(0, [])], by simpa using le_rfl, le_rfl, fun _ l hl => List.mem_singleton.1 hl ▸ .inl hL⟩ h



theorem good_mono (h : Good L P A B C) (hp : P' → P) : Good L P' A B C :=
  let ⟨O, a, b, c⟩ := h; ⟨O, a, b, fun p => c (hp p)⟩



-- Frames
-- ------

-- a call of def k (index i, body d) on xs, inside a spine that adds zs;
-- cs are the columns its walk made so far
structure Frame where
  bk : Book
  k : String
  i : Nat
  d : Def
  xs : List Arg
  zs : List Arg
  cs : List Bool
  hs : List ((Nat × List Bool) × String)



noncomputable def Frame.L (F : Frame) : Label := Term.label F.bk F.k (F.xs ++ F.zs)



abbrev Frame.g (F : Frame) (ts : List Tag) : Guard := ⟨F.bk, F.i, F.cs, ts, F.hs⟩



-- the args are closed, and live ones are live values
def AOK (bk : Book) (as : List Arg) : Prop :=
  ∀ a ∈ as, Closed a.2 ∧ (a.1.live = true → Value bk a.2 ∧ Live bk a.2)



-- the columns are the liveness of the first args
def CS (xs : List Arg) (cs : List Bool) : Prop :=
  cs = (xs.map (·.1.live)).take cs.length



-- the piece at path π of t: each step, innermost first, takes a pair's
-- live first field (false) or its second (true)
def Term.get : List Bool → Term → Option Term
  | [], t => some t
  | b :: π, t =>
    match Term.get π t with
    | some (Tup r x y) => if b then some y else if r.live then some x else none
    | _ => none



-- the piece at path π of column c
def Arg.at (xs : List Arg) (c : Nat) (π : List Bool) : Option Term :=
  xs[c]?.bind fun a => Term.get π a.2



-- the labels hs recorded are the labels at their paths
def Hits (xs : List Arg) (hs : List ((Nat × List Bool) × String)) : Prop :=
  ∀ c π k, ((c, π), k) ∈ hs → Arg.at xs c π = some (Lab k)



def Frame.ok (F : Frame) : Prop :=
  Book.index F.bk F.k = some F.i ∧ Book.get F.bk F.k = some F.d ∧ AOK F.bk F.xs ∧
  F.cs.length ≤ size F.d.v ∧ CS F.xs F.cs ∧ Hits F.xs F.hs



-- a tagged variable is closed, and a live use of it holds the piece its
-- tag names
def Frame.tags (F : Frame) (ts : List Tag) (σ : Subst) (t : Term) : Prop :=
  ∀ v c π, ts[v]? = some (some (c, π)) → Closed (σ v) ∧
    (uses t v ≠ 0 → Arg.at F.xs c π = some (σ v))



theorem tags_mono {F : Frame} (h : F.tags ts σ t)
    (hu : ∀ v, uses t' v ≠ 0 → uses t v ≠ 0 := by intro v n; simp_all [uses]) :
    F.tags ts σ t' := fun v c o e => (h v c o e).imp_right (· ∘ hu v)



theorem get_val (h : Term.get π X = some Y) (v : Value bk X) : Value bk Y := by
  induction π generalizing Y with
  | nil => cases h; exact v
  | cons b π ih =>
    simp only [Term.get] at h; split at h <;> try cases h
    rename_i e; have := value_tup (ih e)
    split at h <;> (try split at h) <;> cases h
    · exact this.2
    · exact this.1 ‹_›



theorem at_cons (h : Arg.at xs c π = some (Tup r x y)) :
    Arg.at xs c (true :: π) = some y ∧ (r.live = true → Arg.at xs c (false :: π) = some x) := by
  simp only [Arg.at, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨a, ha, h⟩ := h
  exact ⟨⟨a, ha, by simp [Term.get, h]⟩, fun l => ⟨a, ha, by simp [Term.get, h, l]⟩⟩



-- t's head call, under σ and on es, is below the frame's call
def Frame.hc (F : Frame) (σ : Subst) (t : Term) (es : List Arg) : Prop :=
  ∀ k ys, Term.unspine t [] = (Ref k, ys) →
    Label.lt (Term.label F.bk k (ys.map (fun a => (a.1, sub σ a.2)) ++ es)) F.L



theorem values_mem (h : Values bk xs) (m : a ∈ xs) (hl : a.1.live = true) : Value bk a.2 := by
  induction xs <;> cases h <;> cases m; exact ‹_ → _› hl; exact ‹Values bk _ → _ ∈ _ → _› ‹_› ‹_›



-- under σ, x is a closed value k or more smaller than the piece at π of X
def Below (bk : Book) (σ : Subst) (X : Term) (π : List Bool) (x : Term) (k : Nat) : Prop :=
  ∃ y, Term.get π X = some y ∧ Value bk (sub σ x) ∧ Closed (sub σ x) ∧
    size (sub σ x) + k ≤ size y



-- a piece's parent is bigger by one
theorem below_up (h : Below bk σ X (b :: π) x k) : Below bk σ X π x (k + 1) := by
  obtain ⟨_, g, v, c, s⟩ := h; simp only [Term.get] at g; split at g <;> try cases g
  refine ⟨_, ‹_›, v, c, ?_⟩
  split at g <;> (try split at g) <;> cases g <;> simp only [size] <;> split <;> omega



theorem below_le (h : Below bk σ X π x k) (e : k' ≤ k) : Below bk σ X π x k' :=
  let ⟨y, g, v, c, s⟩ := h; ⟨y, g, v, c, by omega⟩



-- a pair's first part is below its piece, or dead and closed under σ
theorem below_tup (h0 : Below bk σ X (false :: π) x k0 ∨ q.live = false ∧ Closed (sub σ x) ∧ k0 = 0)
    (h1 : Below bk σ X (true :: π) y k1) : Below bk σ X π (Tup q x y) (k0 + k1) := by
  obtain ⟨yb, gb, vb, cb, sb⟩ := h1
  simp only [Term.get] at gb; split at gb <;> simp at gb
  rename_i r u w e; subst gb
  rcases h0 with ⟨ya, ga, va, ca, sa⟩ | ⟨l, ca, rfl⟩
  · simp only [Term.get, e] at ga; simp at ga; obtain ⟨lr, rfl⟩ := ga
    refine ⟨_, e, .tup (fun _ => va) vb, by simp only [sub]; cl And.intro ca cb, ?_⟩
    simp [sub, size, lr]; split <;> omega
  · refine ⟨_, e, .tup (by simp [l]) vb, by simp only [sub]; cl And.intro ca cb, ?_⟩
    simp [sub, size, l]; omega



-- what each step of the comparison shows, under σ, of x against the
-- piece of column c of value X it is compared to: a result other than gt
-- makes x a closed value no bigger than that piece, and lt makes it smaller
theorem pat_below {F : Frame} (ho : F.ok) (ha : F.xs[c]? = some (qa, X)) (hv : Value F.bk X) (n : Nat) :
    (∀ p π x, 2 * sizeOf p + 1 ≤ n → F.tags ts σ x → Pat.cmp (F.g ts) c p π x ≠ .gt →
      Below F.bk σ X π x (if Pat.cmp (F.g ts) c p π x = .lt then 1 else 0)) ∧
    (∀ p π x o, 2 * sizeOf p ≤ n → F.tags ts σ x →
      Pat.fields (F.g ts) c p π x = .ok o → Below F.bk σ X π x (if o = .lt then 1 else 0)) ∧
    (∀ bad q ρ x, 2 * sizeOf q ≤ n → F.tags ts σ x →
      Pat.visit (F.g ts) c bad q ρ x = true → Below F.bk σ X ρ x 0) := by
  have A : ∀ {π}, Arg.at F.xs c π = Term.get π X := by simp [Arg.at, ha]
  induction n using Nat.strongRecOn with | _ n ih =>
  have I {m} (h : m < n) := ih m h
  refine ⟨fun p π x hn ht hg => ?_, fun p π x o hn ht h => ?_, fun bad q ρ x hn ht h => ?_⟩
  · generalize e : Pat.cmp (F.g ts) c p π x = o at hg ⊢
    unfold Pat.cmp at e
    split at e
    · subst e; exact (I (m := 2 * sizeOf p) (by omega)).2.1 _ _ _ _ (Nat.le_refl _) ht ‹_›
    split at e
    · rename_i b _; simp only [Pat.pair.sizeOf_spec] at hn
      split at e <;> subst e
      · exact below_up ((I (m := 2 * sizeOf b) (by omega)).2.2 _ _ _ _ (Nat.le_refl _) ht ‹_›)
      · exact absurd rfl hg
    · subst e; exact absurd rfl hg
  · unfold Pat.fields at h
    split at h
    · rename_i hx; cases h; simp only [reduceCtorEq, ite_false]
      unfold Guard.at at hx; split at hx
      · rename_i v; have ⟨hc, h⟩ := ht v c π (by simpa using hx)
        have h := A ▸ h (by simp [uses])
        exact ⟨_, h, get_val h hv, hc, by simp [sub]⟩
      · rename_i k; exact ⟨_, A ▸ ho.2.2.2.2.2 c π k (by simpa using hx), .lab, fun _ => rfl, by simp [sub]⟩
      · cases hx
    split at h
    · rename_i a b q x0 x1 _; simp only [Pat.pair.sizeOf_spec] at hn
      generalize eo : (if q.live then Pat.cmp (F.g ts) c a (false :: π) x0
        else if (F.g ts).at c (false :: π) x0 then Ordering.eq else .gt) = o0 at h
      have C0 (g : o0 ≠ .gt) : Below F.bk σ X (false :: π) x0 (if o0 = .lt then 1 else 0) ∨
          q.live = false ∧ Closed (sub σ x0) ∧ (if o0 = .lt then 1 else 0) = 0 := by
        split at eo
        · subst eo; exact .inl ((I (m := 2 * sizeOf a + 1) (by omega)).1 _ _ _ (Nat.le_refl _) (tags_mono ht) g)
        rename_i hl; split at eo <;> subst eo
        · rename_i hx; refine .inr ⟨by simpa using hl, ?_, rfl⟩
          unfold Guard.at at hx; split at hx
          · simpa [sub] using (ht _ _ _ (by simpa using hx)).1
          · exact fun _ => rfl
          · cases hx
        · exact absurd rfl g
      simp only at h; split at h
      · cases h
      rename_i hc0
      cases hf : Pat.fields (F.g ts) c b (true :: π) x1 <;> simp [hf, Except.map] at h
      have h1 := (I (m := 2 * sizeOf b) (by omega)).2.1 _ _ _ _ (Nat.le_refl _) (tags_mono ht) hf
      refine below_le (below_tup (C0 hc0) h1) ?_
      subst h; revert hc0; cases o0 <;> rename_i o2 <;> cases o2 <;> simp [Ordering.then]
    · cases h
  · unfold Pat.visit at h
    split at h
    · rename_i a b; simp only [Pat.pair.sizeOf_spec] at hn
      simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne] at h
      rcases h with ⟨-, h⟩ | h
      · exact below_le (below_up ((I (m := 2 * sizeOf a + 1) (by omega)).1 _ _ _ (Nat.le_refl _) ht h)) (Nat.zero_le _)
      · exact below_le (below_up ((I (m := 2 * sizeOf b) (by omega)).2.2 _ _ _ _ (Nat.le_refl _) ht h))
          (Nat.zero_le _)
    · cases h



-- a descent from column j on: column by column, the call's sizes are
-- no bigger than B's until one is smaller
theorem desc_lex {F : Frame} (ho : F.ok) (ys : List Arg) :
    ∀ j n (B : List (Option Nat)), (∀ a ∈ ys, a.1.live = true → F.tags ts σ a.2) →
    Arg.descend (F.g ts) j ys = .lt → F.cs.length ≤ j + n →
    (∀ c a, F.xs[j + c]? = some a → B[c]? = some (Arg.size F.bk a)) →
    Lex Size.lt (Pad n ((ys.map (fun a => (a.1, sub σ a.2)) ++ es).map (Arg.size F.bk))) (Pad n B) := by
  induction ys with
  | nil => simp [Arg.descend]
  | cons y ys ih =>
    obtain ⟨q, y⟩ := y
    intro j n B hu d hn hB
    simp only [Arg.descend] at d
    have e : F.cs[j]? = some q.live := Classical.byContradiction fun e => by simp [Arg.cmp, e] at d
    obtain ⟨⟨qa, xa⟩, ha, hl⟩ : ∃ a : Arg, F.xs[j]? = some a ∧ a.1.live = q.live := by
      rw [ho.2.2.2.2.1] at e; simp [List.getElem?_take] at e; simpa using e.2
    -- an eq arg is no bigger than column j's, a lt arg is smaller
    have C : (Arg.cmp (F.g ts) j (q, y) = .eq → Size.le (Arg.size F.bk (q, sub σ y)) (Arg.size F.bk (qa, xa))) ∧
        (Arg.cmp (F.g ts) j (q, y) = .lt → Size.lt (Arg.size F.bk (q, sub σ y)) (Arg.size F.bk (qa, xa))) := by
      simp only [Arg.cmp, e, bne_self_eq_false, Bool.false_eq_true, ite_false]
      cases hq : q.live
      · simp [Arg.size, hq, hl, Size.le]
      have ⟨c2, v2⟩ := ho.2.2.1 _ (List.mem_of_getElem? ha)
      have v2 := (v2 (hl.trans hq)).1
      simp only [ite_true, Arg.size, hl, hq, v2, c2, and_self]
      have B := (pat_below ho ha v2 (2 * sizeOf ((F.g ts).pat j) + 1)).1 _ [] _ (Nat.le_refl _) (hu _ (.head _) hq)
      constructor <;> intro h <;> obtain ⟨_, g, v, c, s⟩ := B (by simp [h]) <;> cases g <;>
        simp [h, v, c, Size.le, Size.lt] at s ⊢ <;> omega
    cases n; have := (List.getElem?_eq_some_iff.1 e).1; omega
    obtain _ | ⟨b, B⟩ := B <;> cases hB 0 _ ha
    cases h : Arg.cmp (F.g ts) j (q, y) <;> rw [h] at d
    · exact .head (C.2 h) (by simp [pad_len])
    · rcases C.1 h with s | s
      · simp only [Pad, List.map_cons, List.cons_append, s]
        exact .tail (ih (j + 1) _ B (fun a m => hu a (.tail _ m)) d (by omega)
          fun c a e => by simpa using hB (c + 1) a (by rw [← e]; congr 1; omega))
      · exact .head s (by simp [pad_len])
    · cases d



-- the live check at the def's guard puts a live call below the frame's
theorem hcl {F : Frame} (ho : F.ok) (h : Term.live (F.g ts) true t = true) (ht : F.tags ts σ t) :
    F.hc σ t es := by
  intro k ys e
  obtain ⟨j, hj, hlt | ⟨rfl, hdesc⟩⟩ := live_call h e
  · left; simpa [Frame.L, label, hj, ho.1]
  obtain rfl : k = F.k := by
    have h1 := hj; have h2 := ho.1; rw [index_find] at h1 h2
    have ⟨_, a, _⟩ := List.findIdx?_eq_some_iff_getElem.1 h1; have ⟨_, b, _⟩ := List.findIdx?_eq_some_iff_getElem.1 h2
    simp_all
  refine .inr ⟨rfl, ?_⟩
  simp only [Frame.L, label, ho.2.1, Option.map_some, Option.getD_some]
  refine desc_lex ho ys 0 _ _ (fun a m hq => tags_mono ht fun v n => ?_) hdesc (by simpa using ho.2.2.2.1)
    fun c a e => by
      simp at e; rw [List.getElem?_map, List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1, e]; rfl
  have := uses_unspine (v := v) (by rw [e]; exact m) hq; omega



-- The substitution lemma
-- ----------------------

-- the labels of t under σ, on extra args es, but the top-level App's
noncomputable def Lhs (bk : Book) (σ : Subst) (t : Term) (es : List Arg) : List Label :=
  Term.hd bk (unspine (sub σ t) es) ++ labels bk false (sub σ t)



theorem lhs_nil : labels bk true (sub σ t) = Lhs bk σ t [] := labels_top _



-- σ is a variable, or a closed term
def VM (σ : Subst) : Prop := ∀ v, (∃ w, σ v = Var w) ∨ Closed (σ v)



theorem vm_up (h : VM σ) : VM (Subst.up σ) ∧
    (fun v => labels bk true (Subst.up σ v)) = Bud.up (fun v => labels bk true (σ v)) := by
  refine ⟨?_, funext ?_⟩ <;> rintro (_ | v) <;> first | exact .inl ⟨0, rfl⟩ | rfl |
    rcases h v with ⟨w, e⟩ | hc <;> simp [Subst.up, ren, labels, Bud.up, closed_ren, *]



theorem tags_up {F : Frame} (h : F.tags ts σ t)
    (hu : ∀ v, uses f (v + 1) ≠ 0 → uses t v ≠ 0 := by intro v n; simp_all [uses]) :
    F.tags (none :: ts) (Subst.up σ) f := by
  rintro (_ | v) c π e; cases e
  have ⟨hc, r⟩ := h v c π e
  rw [Subst.up, closed_ren hc]; exact ⟨hc, r ∘ hu v⟩



theorem good_if {q : Quan} (h : q.live = true → Good L P A B C) :
    Good L P (if q.live then A else []) (if q.live then B else []) (if q.live then C else []) := by
  cases hq : q.live <;> simp [good_nil, h, hq]



-- a child at a top position: its tags come from the parent's
theorem good_ch {F : Frame} (ih : Good F.L (F.ok ∧ Term.live (F.g ts) false c = true ∧
      F.tags ts σ c ∧ F.hc σ c []) A B C)
    (hu : ∀ v, uses c v ≠ 0 → uses t v ≠ 0 := by intro v n; simp_all [uses])
    (hl : Term.live (F.g ts) false t = true → Term.live (F.g ts) true c = true :=
      by intro l; simp_all [Term.live]) :
    Good F.L (F.ok ∧ Term.live (F.g ts) false t = true ∧ F.tags ts σ t ∧ F.hc σ t es) A B C :=
  good_mono ih fun ⟨o, l, tg, _⟩ => have l := hl l; have tg := tags_mono tg hu; ⟨o, live_mono l, tg, hcl o l tg⟩



theorem gsl (F : Frame) (t : Term) : ∀ {ts : List Tag} {σ : Subst} {es es₀ : List Arg},
    VM σ → ArgsLe F.bk es es₀ →
    Good F.L (F.ok ∧ Term.live (F.g ts) false t = true ∧ F.tags ts σ t ∧ F.hc σ t es)
      (Lhs F.bk σ t es) (bud (fun v => labels F.bk true (σ v)) t) (Lhs F.bk Var t es₀) := by
  have hL : 0 < F.L.1 := Nat.succ_pos _
  induction t <;> intro ts σ es es₀ hv hE
  case Var =>
    refine ⟨[], ?_, le_nil, by simp⟩
    simp only [Lhs, sub, bud, List.nil_append]
    exact le_le (le_app hd_ext le_rfl) (.inl (by rw [labels_top]))
  case Ref k =>
    simp [Lhs, sub, unspine, Term.hd, labels, bud]
    exact ⟨_, le_sub, label_le hE,
      fun ⟨_, _, _, h⟩ l hl => List.mem_singleton.1 hl ▸ by simpa using h k [] rfl⟩
  case App q f x ihf ihx =>
    have e (σ es) : Lhs F.bk σ (App q f x) es =
        Lhs F.bk σ f ((q, sub σ x) :: es) ++ (if q.live then Lhs F.bk σ x [] else []) := by
      simp [Lhs, sub, unspine, labels_app, labels_top]
    rw [e, e, sub_var]
    refine good_app (good_mono (ihf (ts := ts) hv (.cons size_sub hE)) ?_)
      (good_if fun hq => good_ch (ihx hv .nil))
    rintro ⟨o, l, tg, hc⟩
    lv at l
    refine ⟨o, l.1.2, tags_mono tg, fun k ys e' => ?_⟩
    simpa using hc k (ys ++ [(q, x)]) (by show unspine f [(q, x)] = _; rw [unspine_app, e'])
  all_goals try simp only [Lhs, sub, unspine, Term.hd, labels, List.nil_append] <;> simp only [lhs_nil]
  case Lam ih | Let ihv ih =>
    rw [up_var]
    have ⟨V, E⟩ := vm_up (bk := F.bk) hv; have := E ▸ ih (ts := none :: ts) (es := []) (es₀ := []) V .nil
    first
      | refine good_cons hL (good_mono this ?_)
      | refine good_cons hL (good_app (good_if fun hq => good_ch (ihv hv .nil)) (good_mono this ?_))
    exact fun ⟨o, l, tg, _⟩ => by lv at l; exact ⟨o, live_mono l.2, tags_up tg, hcl o l.2 (tags_up tg)⟩
  case Tup iha ihb => exact good_app (good_if fun hq => good_ch (iha hv .nil)) (good_ch (ihb hv .nil))
  case Mat iha ihb | Rwt iha _ ihb | Min iha ihb =>
    exact good_cons hL (good_app (good_ch (iha hv .nil)) (good_ch (ihb hv .nil)))
  case Prj ih | Ann ih _ => exact good_cons hL (good_ch (ih hv .nil))
  all_goals exact good_nil



theorem data_labels (h : Data v) : labels bk true v = [] := by
  induction h <;> simp_all [labels]



-- The tree walk
-- -------------

def Ren.lift : Nat → Ren
  | 0 => Nat.succ
  | n + 1 => Ren.up (Ren.lift n)



theorem lift_fix : Ren.lift n v = v → v < n := by
  induction n generalizing v <;> cases v <;> simp_all [Ren.lift, Ren.up]



theorem env_var (h : e.length ≤ v) : Env.sub e v = Var (v - e.length) := by
  induction e generalizing v <;> cases v <;> simp_all [Env.sub]



theorem tree_leaf (h : node t = false) : tree g ps t = Term.live g true t := by
  cases t <;> simp_all [node, takes, tree]; cases ‹Term› <;> simp_all [tree, takes]



theorem fld_live {q : Quan} (h : q.live = true) : (Quan.fld r q).live = r.live := by
  cases r <;> cases q <;> simp_all [Quan.fld, Quan.live]



theorem allows_live {q : Quan} (h : Quan.allows q n = true) (hn : n ≠ 0) : q.live = true := by
  cases q <;> simp_all [Quan.allows, Quan.live]



theorem allows_two {q : Quan} (h : Quan.allows q n = true) (hn : 2 ≤ n) : q = Q2 := by
  cases q <;> simp_all [Quan.allows] <;> omega



-- the pending args carry their tags' relation
inductive PR (xs : List Arg) : List Tag → List Arg → Prop
  | nil : PR xs [] []
  | cons : (∀ c π, p = some (c, π) → a.1.live = true → Arg.at xs c π = some a.2) → PR xs ps as →
      PR xs (p :: ps) (a :: as)



-- the next argument of the walk: a pending one, or a new column
theorem next_ok (hq : q.live = l) (hpe : (q, x) :: as' = pend ++ xs.drop cs.length)
    (hp : PR xs ps pend) (hcs : CS xs cs) :
    ∃ pt cs' ps' pend', Guard.next ⟨bk, i, cs, ts, hs⟩ ps l = (pt, ⟨bk, i, cs', ts, hs⟩, ps') ∧
      as' = pend' ++ xs.drop cs'.length ∧ PR xs ps' pend' ∧
      (∀ c π, pt = some (c, π) → q.live = true → Arg.at xs c π = some x) ∧ CS xs cs' ∧
      cs'.length ≤ cs.length + 1 := by
  cases hp
  case cons h hp => cases hpe; exact ⟨_, cs, _, _, rfl, rfl, hp, h, hcs, by omega⟩
  have h1 := congrArg (·[0]?) hpe; have h2 := congrArg List.tail hpe; simp at h1 h2
  refine ⟨_, cs ++ [l], [], [], rfl, by simp [h2], .nil, fun _ _ e _ => ?_, ?_, by simp⟩
  · cases e; simp [Arg.at, ← h1, Term.get]
  rw [CS] at *; simp [List.take_add_one, ← hcs, ← h1, hq]



-- the walk's invariant at tree node t with env e and args as
-- the env's entries are closed, and used ones are live values
def EOK (bk : Book) (e : List Term) (t : Term) : Prop :=
  ∀ v, v < e.length → Closed (Env.sub e v) ∧
    (uses t v ≠ 0 → Value bk (Env.sub e v) ∧ Live bk (Env.sub e v))



theorem eok_mono (h : EOK bk e t) (hu : ∀ v, uses t' v ≤ uses t v := by intro v; simp [uses]) :
    EOK bk e t' :=
  fun v l => let ⟨c, u⟩ := h v l; ⟨c, fun n => u (by have := hu v; omega)⟩



def WInv (bk : Book) (k : String) (i : Nat) (d : Def) (xs : List Arg) (t : Term) (e : List Term)
    (as : List Arg) (ts : List Tag) (cs : List Bool) (hs : List ((Nat × List Bool) × String))
    (ps : List Tag) : Prop :=
  tree ⟨bk, i, cs, ts, hs⟩ ps t = true ∧ ren (Ren.lift e.length) t = t ∧ EOK bk e t ∧
  Frame.tags ⟨bk, k, i, d, xs, [], cs, hs⟩ ts (Env.sub e) t ∧
  (∃ pend, as = pend ++ xs.drop cs.length ∧ PR xs ps pend) ∧
  cs.length + size t ≤ size d.v ∧ CS xs cs ∧ AOK bk as ∧
  DMle Label.lt (bud (fun v => labels bk true (Env.sub e v)) t ++ Args.labels bk as)
    (Args.labels bk xs) ∧ Hits xs hs



-- a call's walk: the reached leaf, under the env, is live, and its
-- labels are below the call's
theorem tp (hk : Book.index bk k = some i) (hd : Book.get bk k = some d) (hx : AOK bk xs)
    (w : Walk bk t e as o) : ∀ ts cs ls ps r, o = some r → WInv bk k i d xs t e as ts cs ls ps →
    Live bk r ∧ ∀ zs, DM Label.lt (labels bk true (spine r zs))
      (label bk k (xs ++ zs) :: (Args.labels bk xs ++ Args.labels bk zs)) := by
  induction w <;> rintro ts cs ls ps r0 ⟨⟩ ⟨ht, hr, hE, htg, ⟨pend, hpe, hp⟩, hsz, hcs, ha, hbud, hh⟩
  all_goals (try simp only [size] at hsz); try
    obtain ⟨pt, cs', ps', pend', hn, hpe', hp', hx', hcs', hlen⟩ :=
      next_ok (by first | assumption | exact .symm (by assumption)) hpe hp hcs
    simp only [tree] at ht; rw [hn] at ht; try simp only [Bool.and_eq_true] at ht
  case lam f e xs' q pl dx w ih =>
    have lq : uses f 0 ≠ 0 → q.live = true := (pl ▸ allows_live ht.1 ·)
    refine ih _ cs' _ _ _ rfl ⟨ht.2, (Lam.inj hr).2,
      fun | 0, _ => (ha _ (.head _)).imp_right (· ∘ lq) | v + 1, hv => hE v (by simpa using hv),
      fun | 0 => fun c o e' => ⟨(ha _ (.head _)).1, hx' c o (Option.some.inj e') ∘ lq⟩ | v + 1 => htg v,
      ⟨pend', hpe', hp'⟩, by omega, hcs', fun a h => ha a (.tail _ h),
      le_le (le_app (le_le (bud_once (i := 0) f fun h => data_labels (dx (allows_two ht.1 h)))
        (le_app (.inl (.of_eq (congrArg (bud · f) (funext fun v => by cases v <;> rfl))))
          (by split; exact le_nil; simp [lq ‹_›]; exact le_rfl))) le_rfl)
        (List.append_assoc .. ▸ hbud), hh⟩
  case prj r q a b xs' hq w ih =>
    obtain ⟨ct, ⟨va, vb⟩, lt⟩ := (ha _ (.head _)).imp_right fun h => (h hq).imp_left value_tup
    have ⟨ca, cb⟩ : Closed a ∧ Closed b := by cl ct
    have fl := fld_live (r := r) hq
    lv at lt
    refine ih _ _ _ _ _ rfl ⟨ht, Prj.inj hr, hE, htg,
      ⟨(Quan.fld r q, a) :: (q, b) :: pend', by simp [hpe'], .cons (fun c o e l => ?_) (.cons (fun c o e _ => ?_) hp')⟩,
      by omega, hcs', fun
        | _, .head _ => ⟨ca, fun l => ⟨va (fl ▸ l), lt.1.resolve_left (by simp [← fl, l])⟩⟩
        | _, .tail _ (.head _) => ⟨cb, fun _ => ⟨vb, lt.2⟩⟩
        | _, .tail _ (.tail _ hy) => ha _ (.tail _ hy),
      by simpa [Args.labels, fl, hq, labels, List.append_assoc, bud] using hbud, hh⟩
    all_goals
      simp at e; obtain ⟨_, _, rfl, rfl, rfl⟩ := e; have := at_cons (hx' _ _ rfl hq)
      first | exact this.1 | exact this.2 (fl ▸ l)
  case hit hq w ih =>
    refine ih _ _ _ _ _ rfl ⟨ht.1, (Mat.inj hr).2.1, eok_mono hE, tags_mono htg,
      ⟨pend', hpe', hp'⟩, by omega, hcs', fun a h => ha a (.tail _ h), le_le (le_app le_sub le_rfl)
      (by simpa [Args.labels, labels, bud] using hbud), fun c π k hm => by
        simp at hm; rcases hm with ⟨_, _, e, ⟨rfl, rfl⟩, rfl⟩ | hm <;> solve_by_elim⟩
  case miss q xs' h hq hj w ih =>
    refine ih _ _ _ _ _ rfl ⟨ht.2, (Mat.inj hr).2.2, eok_mono hE, tags_mono htg,
      ⟨(q, _) :: pend', by simp [hpe'], .cons (fun c o e _ => hx' c o e hq) hp'⟩,
      by omega, hcs', ha, le_le (le_app le_sub' le_rfl) hbud, hh⟩
  case app q f v e xs' hn w ih =>
    simp only [tree, show takes _ = true from hn] at ht; simp [ren] at hr
    have huv : q.live = true → uses (App q f (Var v)) v ≠ 0 := by simp +contextual [uses]
    exact ih _ _ _ _ _ rfl ⟨ht, hr.1, eok_mono hE, tags_mono htg,
      ⟨(q, _) :: pend, by simp [hpe], .cons (fun c o e l => (htg v c o (Option.join_eq_some_iff.1 e)).2 (huv l)) hp⟩,
      by omega, hcs, fun | _, .head _ => (hE v (lift_fix hr.2)).imp_right (· ∘ huv) | _, .tail _ hy => ha _ hy,
      List.append_assoc .. ▸ hbud, hh⟩
  case done t e xs' hn =>
    rw [tree_leaf hn] at ht
    have hV : LiveV bk (Env.sub e) t := fun v => if hv : v < e.length then
      .inr ((hE v hv).imp_right fun h n G hG hi => live_up (h n).2 hG (hG ▸ hi))
      else .inl ⟨_, env_var (by omega)⟩
    refine ⟨live_spine.2 ⟨live_sub t (by rfl) rfl hV ht, fun a h l => ((ha a h).2 l).2⟩, fun zs => ?_⟩
    let F : Frame := ⟨bk, k, i, d, xs, zs, cs, ls⟩
    have hF : F.ok := ⟨hk, hd, hx, Nat.le_of_add_right_le hsz, hcs, hh⟩
    obtain ⟨O, h1, _, h3⟩ := gsl F t (es := xs' ++ zs) (fun v => (hV v).imp_right And.left) sl_refl
    rw [← spine_append, labels_spine, args_append]
    exact le_dm (le_le (le_app h1 le_rfl) (by simp only [List.append_assoc]; exact le_rfl))
      (dm_repl (le_app hbud le_rfl) (h3 ⟨hF, live_mono ht, htg, hcl hF ht htg⟩))



-- Evaluation
-- ----------

theorem sl_mid (h : Size.le a b) : SL (l ++ a :: r) (l ++ b :: r) := by
  induction l; exact .cons h sl_refl; exact .cons (.inl rfl) ‹_›



-- β and let: the body stays live, and x lands in at most one live
-- place, or has no labels
theorem inst_ok {p q : Quan} (ha : Quan.allows p (uses f 0) = true) (pq : p.live = q.live)
    (hf : Term.live ⟨bk, bk.length, [], [none], []⟩ true f = true) (hx : Closed x)
    (hl : q.live = true → Live bk x) (hd : p = Q2 → Data x) :
    Live bk (inst f x) ∧ DMle Label.lt (labels bk true (inst f x))
      (labels bk true f ++ (if q.live then labels bk true x else [])) := by
  refine ⟨live_sub f (by rfl) rfl (fun
    | 0 => .inr ⟨hx, fun n G hG hi => live_up (hl (pq ▸ allows_live ha n)) hG (hG ▸ hi)⟩
    | v + 1 => .inl ⟨v, rfl⟩) hf, ?_⟩
  obtain ⟨_, h1, h2, _⟩ := gsl ⟨bk, "", 0, default, [], [], [], []⟩ f (ts := []) (es₀ := [])
    (σ := Subst.one x) (fun | 0 => .inr hx | v + 1 => .inl ⟨v, rfl⟩) .nil
  rw [← lhs_nil] at h1 h2; rw [sub_var] at h2
  refine le_le h1 (le_app h2 (le_le (bud_once (i := 0) f fun h => data_labels (hd (allows_two ha h))) ?_))
  rw [bud_nil f fun v => by cases v <;> rfl, List.nil_append]
  split; exact le_nil; simp [← pq, allows_live ha ‹_›]; exact le_rfl



theorem live_app : Live bk (App q f x) ↔ Live bk f ∧ (q.live = true → Live bk x) :=
  (live_spine (t := f) (as := [(q, x)])).trans (by simp)



-- a step at a head that is no call lifts to any spine
theorem dm_spine (h : DM Label.lt (labels bk true u) (labels bk true t))
    (ht : ∀ zs, Term.hd bk (unspine t zs) = [] := by exact fun _ => rfl) (zs : List Arg) :
    DM Label.lt (labels bk true (spine u zs)) (labels bk true (spine t zs)) := by
  rw [labels_top t, ht] at h
  exact le_dm (labels_ext u zs) (by rw [labels_spine, ht]; exact dm_app h)



-- each step keeps Live, and lowers the labels in any spine
theorem ev (hb : Book.Live bk) (h : Eval bk t u) : ren Nat.succ t = t → Live bk t → Live bk u ∧
    ∀ zs, DM Label.lt (labels bk true (spine u zs)) (labels bk true (spine t zs)) := by
  induction h <;> intro hc hl <;> (try exact ⟨hl, dm_spine (dm_cons le_rfl)⟩) <;>
    (try obtain ⟨lf, lx⟩ := live_app.1 hl) <;> (try lv at hl) <;> (try lv at lf) <;> try simp [ren] at hc
  case app_f ih =>
    have ⟨l, dd⟩ := ih hc.1 lf
    exact ⟨live_app.2 ⟨l, lx⟩, fun zs => dd ((_, _) :: zs)⟩
  case app_x f x x' q vf hq hx ih =>
    have ⟨l, dd⟩ := ih hc.2 (lx hq)
    refine ⟨live_app.2 ⟨lf, fun _ => l⟩, fun zs => ?_⟩
    erw [labels_spine f ((q, x') :: zs), labels_spine f ((q, x) :: zs), unspine_app (xs := _ :: zs),
      unspine_app (xs := _ :: zs)]
    simp only [Args.labels, hq]
    exact dm_mono (le_app (hd_le (by
      simp only [ArgsLe, List.map_append, List.map_cons, Arg.size, hq,
        show ¬(Value bk x ∧ Closed x) from fun h => eval_value hx h.1]
      exact sl_mid size_le_none)) le_rfl) (dm_app (dd []))
  case beta =>
    have ⟨li, di⟩ := inst_ok lf.1 ‹_› lf.2 (ren_closed hc.2) lx ‹_›
    exact ⟨li, dm_spine (dm_cons di)⟩
  case split r a b q h hq vt =>
    have lt := lx hq; have fl := fld_live (r := r) hq; lv at lt
    exact ⟨live_app.2 ⟨live_app.2 ⟨lf, fun l => lt.1.resolve_left (by simp [← fl, l])⟩,
      fun _ => lt.2⟩, dm_spine (dm_cons (le_le (labels_ext _ [(_, _), (_, _)])
        (.inl (.of_eq (by simp [Args.labels, fl, hq, labels])))))⟩
  case hit => exact ⟨lf.1, dm_spine (dm_cons (le_le le_sub le_sub))⟩
  case miss =>
    exact ⟨live_app.2 ⟨lf.2, fun _ => rfl⟩, dm_spine (dm_cons (le_le (labels_ext _ [(_, _)])
      (le_app le_sub' (.inl (.of_eq (List.append_nil _))))))⟩
  case call k d xs t hd hv w =>
    obtain ⟨i, hk⟩ := index_of_get hd
    have hx : AOK bk xs := fun a h =>
      ⟨(closed_spine.1 (ren_closed hc)).2 a h, fun l => ⟨values_mem hv h l, (live_spine.1 hl).2 a h l⟩⟩
    have ⟨l, dd⟩ := tp hk hd hx w [] [] [] [] t rfl ⟨hb.2 k i d hk hd, closed_ren (hb.1 k d hd),
      nofun, nofun, ⟨[], rfl, .nil⟩, by simp,
      rfl, hx, by rw [bud_nil]; exact le_rfl; exact fun _ => rfl, nofun⟩
    refine ⟨l, fun zs => ?_⟩
    rw [← spine_append, labels_spine (Ref k), args_append]
    simpa [unspine, Term.hd, labels] using dd zs
  case lett hq _ ih =>
    have ⟨l, dd⟩ := ih hc.1 (hl.1.2.resolve_left (by simp [hq]))
    refine ⟨by lv; exact ⟨⟨hl.1.1, .inr l⟩, hl.2⟩, dm_spine ?_⟩
    simp only [labels, hq]; exact dm_left (P := [(0, [])]) (dm_app (dd []))
  case unlet =>
    have ⟨li, di⟩ := inst_ok hl.1.1 rfl hl.2 (ren_closed hc.1) (fun h => hl.1.2.resolve_left (by simp [h])) ‹_›
    exact ⟨li, dm_spine (dm_cons (le_le di (.inl List.perm_append_comm)))⟩
  case tup_a hq _ ih =>
    have ⟨l, dd⟩ := ih hc.1 (hl.1.resolve_left (by simp [hq]))
    refine ⟨by lv; exact ⟨.inr l, hl.2⟩, dm_spine ?_⟩
    simp only [labels, hq]; exact dm_app (dd [])
  case tup_b ih | min_b ih =>
    have ⟨l, dd⟩ := ih hc.2 hl.2
    exact ⟨by lv; exact ⟨hl.1, l⟩, dm_spine (dm_left (dd []))⟩
  case rwt ih | min_a ih =>
    have ⟨l, dd⟩ := ih hc.1 hl.1
    exact ⟨by lv; exact ⟨l, hl.2⟩, dm_spine (dm_app (dm_left (P := [(0, [])]) (dd [])))⟩
  case meet i j hi hj =>
    obtain ⟨k, e⟩ : ∃ k, qmin (Lab i) (Lab j) = Lab k := by
      simp only [QS, List.mem_cons, List.not_mem_nil, or_false] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    rw [e]; exact ⟨by simp [Live, Term.live], dm_spine (dm_cons (.inl (by simp [labels])))⟩



-- DM Label.lt on labels is well founded (dm_wf, label_wf); a step keeps Closed
-- (pars_closed) and Live, and lowers the labels (ev)
theorem halts : Claim.halts := by
  intro bk t hb hc hl
  induction (InvImage.wf (labels bk true) (dm_wf label_wf)).apply t; rename_i ih
  exact ⟨_, fun u h => let ⟨l, d⟩ := ev hb h (closed_ren hc) hl; ih u (d []) (pars_closed (eval_pars hb.1 h) hc) l⟩

end

-- Source section: ConversionDesign
section

open Quan Term



namespace ConversionDesign



-- These are requirements on an untyped equality, not a kernel change.
variable {bk : Book} (E : Term → Term → Prop)


variable (old : ∀ {a b}, Par bk a b → E a b)


variable (sym : ∀ {a b}, E a b → E b a)


variable (trans : ∀ {a b c}, E a b → E b c → E a c)


variable (eta : ∀ q f, E (Lam q (App q (ren Nat.succ f) (Var 0))) f)


variable (app : ∀ {f g}, E f g → ∀ p x, E (App p f x) (App p g x))



-- Keep quantities on function types, pair types, and pair values.
def erase : Term → Term
  | Var i => Var i
  | Ref k => Ref k
  | Ann x T => Ann (erase x) (erase T)
  | Let q v f => Let q (erase v) (erase f)
  | Typ q => Typ (erase q)
  | Term.Min a b => Term.Min (erase a) (erase b)
  | All q A B => All q (erase A) (erase B)
  | Lam _ f => Lam Q1 (erase f)
  | App _ f x => App Q1 (erase f) (erase x)
  | Sig q A B => Sig q (erase A) (erase B)
  | Tup q a b => Tup q (erase a) (erase b)
  | Prj h => Prj (erase h)
  | Enu ks => Enu ks
  | Lab k => Lab k
  | Mat k h m => Mat k (erase h) (erase m)
  | Efq => Efq
  | Eql a b T => Eql (erase a) (erase b) (erase T)
  | Rfl => Rfl
  | Rwt e P f => Rwt (erase e) (erase P) (erase f)



theorem erase_ren (t : Term) : erase (ren r t) = ren r (erase t) := by
  induction t generalizing r <;> simp [erase, ren, *]



theorem erase_up : erase ∘ Subst.up σ = Subst.up (erase ∘ σ) := by
  funext i
  cases i <;> simp [Subst.up, erase, erase_ren]



-- Erasure commutes with substitution in live and dead positions.
theorem erase_sub (t : Term) : erase (sub σ t) = sub (erase ∘ σ) (erase t) := by
  induction t generalizing σ <;> simp [erase, sub, *, erase_up]



theorem erase_keeps_former (t : Term) : (erase t).former = t.former := by
  cases t <;> rfl



end ConversionDesign

end

-- Source section: ConversionSpec
section

open Quan Term



namespace ConversionSpec



-- An equational specification. This is not a consistency theorem.
inductive Equation (bk : Book) : Term → Term → Prop
  | old : Par bk a b → Equation bk a b
  | refl : Equation bk a a
  | symm : Equation bk a b → Equation bk b a
  | trans : Equation bk a b → Equation bk b c → Equation bk a c
  | ann : Equation bk x y → Equation bk T U → Equation bk (Ann x T) (Ann y U)
  | lett : Equation bk v w → Equation bk f g → Equation bk (Let q v f) (Let q w g)
  | typ : Equation bk q p → Equation bk (Typ q) (Typ p)
  | min : Equation bk a c → Equation bk b d → Equation bk (Min a b) (Min c d)
  | all : Equation bk A C → Equation bk B D → Equation bk (All q A B) (All q C D)
  | lam : Equation bk f g → Equation bk (Lam q f) (Lam p g)
  | app : Equation bk f g → Equation bk x y → Equation bk (App q f x) (App p g y)
  | sig : Equation bk A C → Equation bk B D → Equation bk (Sig q A B) (Sig q C D)
  | tup : Equation bk a c → Equation bk b d → Equation bk (Tup q a b) (Tup q c d)
  | prj : Equation bk h g → Equation bk (Prj h) (Prj g)
  | mat : Equation bk h g → Equation bk m n → Equation bk (Mat k h m) (Mat k g n)
  | eql : Equation bk a c → Equation bk b d → Equation bk T U →
      Equation bk (Eql a b T) (Eql c d U)
  | rwt : Equation bk e d → Equation bk P Q → Equation bk f g →
      Equation bk (Rwt e P f) (Rwt d Q g)
  | eta : Equation bk (Lam p (App q (ren Nat.succ f) (Var 0))) f



theorem old_steps (h : Pars bk a b) : Equation bk a b := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .trans (.old h) ih



-- This rule justifies comparison of a lambda body with an applied function.
theorem compare_lambda_left
    (h : Equation bk a (App Q1 (ren Nat.succ f) (Var 0))) :
    Equation bk (Lam q a) f :=
  .trans (.lam (p := q) h) .eta



theorem compare_lambda_right
    (h : Equation bk (App Q1 (ren Nat.succ f) (Var 0)) a) :
    Equation bk f (Lam q a) :=
  .symm (compare_lambda_left (.symm h))



theorem ordinary_parts_sound (h : Term.parts a b = some ps)
    (H : ∀ p ∈ ps, Equation bk p.1 p.2) : Equation bk a b := by
  unfold Term.parts at h
  split at h <;> (try split at h) <;> cases h <;> subst_vars <;> simp at H
  all_goals first
    | exact .refl
    | exact .all H.1 H.2
    | exact .lam H
    | exact .app H.1 H.2
    | exact .sig H.1 H.2
    | exact .tup H.1 H.2
    | exact .prj H
    | exact .typ H
    | exact .min H.1 H.2
    | exact .mat H.1 H.2
    | exact .eql H.1 H.2.1 H.2.2
    | exact .rwt H.1 H.2.1 H.2.2



def parts (a b : Term) : Option (List (Term × Term)) :=
  match a, b with
  | Lam _ f, Lam _ g => some [(f, g)]
  | Lam _ f, g => some [(f, App Q1 (ren Nat.succ g) (Var 0))]
  | f, Lam _ g => some [(App Q1 (ren Nat.succ f) (Var 0), g)]
  | App _ f x, App _ g y => some [(f, g), (x, y)]
  | _, _ => Term.parts a b



theorem parts_sound (h : parts a b = some ps)
    (H : ∀ p ∈ ps, Equation bk p.1 p.2) : Equation bk a b := by
  unfold parts at h
  split at h
  · cases h; simp at H; exact .lam H
  · cases h; simp at H; exact compare_lambda_left H
  · cases h; simp at H; exact compare_lambda_right H
  · cases h; simp at H; exact .app H.1 H.2
  · exact ordinary_parts_sound h H



def childClosed (cl : Bool) (a b : Term) : Bool :=
  match a, b with
  | Lam .., _ | _, Lam .. => false
  | _, _ => cl && !Term.binds a



-- The diagnostic comparison rules, expressed through one decomposition.
def compare (ck : Book) (cl : Bool) : Nat → Term → Term → Bool × Nat
  | 0, _, _ => (false, 0)
  | n + 1, a, b =>
    if a = b then
      (true, n)
    else
      let (a, m) := Term.wnf ck cl n a []
      let (b, m) := Term.wnf ck cl (min m n) b []
      match parts a b with
      | some ps =>
        let go := fun (r : Bool × Nat) (p : Term × Term) =>
          if r.1 then compare ck (childClosed cl a b) (min r.2 n) p.1 p.2 else r
        ps.foldl go (true, min m n)
      | none => (false, m)



-- A true result satisfies the specification. No safety claim follows here.
theorem compare_sound (hb : Sees ck bk) :
    (compare ck cl n a b).1 = true → Equation bk a b := by
  induction n using Nat.strongRecOn generalizing a b cl
  rename_i n ih
  unfold compare
  split
  · nofun
  split
  · intro _; subst_vars; exact .refl
  split; split; split
  · intro h
    rename_i hps
    have ⟨_, hf⟩ := fold_true (g := fun m x y => compare ck _ (min m _) x y) h
    have he := parts_sound hps fun p hm =>
      have ⟨_, hp⟩ := hf p hm
      ih _ (by omega) hp
    exact .trans (old_steps (wnf_nil hb ‹_›))
      (.trans he (.symm (old_steps (wnf_nil hb ‹_›))))
  · nofun



def diagnosticParts : Term → Term → Option (List (Term × Term))
  | All q A B, All p C D => if q = p then some [(A, C), (B, D)] else none
  | Lam _ f,   Lam _ g   => some [(f, g)]
  | App _ f x, App _ g y => some [(f, g), (x, y)]
  | Sig q A B, Sig p C D => if q = p then some [(A, C), (B, D)] else none
  | Tup q a b, Tup p c d => if q = p then some [(a, c), (b, d)] else none
  | Prj h,     Prj g     => some [(h, g)]
  | Typ q,     Typ p     => some [(q, p)]
  | Term.Min a b, Term.Min c d => some [(a, c), (b, d)]
  | Mat k h m, Mat j g n => if k = j then some [(h, g), (m, n)] else none
  | Eql a b T, Eql c d U => some [(a, c), (b, d), (T, U)]
  | Rwt e P f, Rwt d Q g => some [(e, d), (P, Q), (f, g)]
  | a,         b         => if a = b then some [] else none



-- This has the diagnostic converter's explicit lambda branches.
def diagnosticCompare (ck : Book) (cl : Bool) : Nat → Term → Term → Bool × Nat
  | 0, _, _ => (false, 0)
  | n + 1, a, b =>
    if a = b then
      (true, n)
    else
      let (a, m) := Term.wnf ck cl n a []
      let (b, m) := Term.wnf ck cl (min m n) b []
      match a, b with
      | Lam _ f, Lam _ g => diagnosticCompare ck false (min m n) f g
      | Lam _ f, g => diagnosticCompare ck false (min m n) f (App Q1 (ren Nat.succ g) (Var 0))
      | f, Lam _ g => diagnosticCompare ck false (min m n) (App Q1 (ren Nat.succ f) (Var 0)) g
      | _, _ =>
        match diagnosticParts a b with
        | some ps =>
          let go := fun (r : Bool × Nat) (p : Term × Term) =>
            if r.1 then diagnosticCompare ck (cl && !Term.binds a) (min r.2 n) p.1 p.2 else r
          ps.foldl go (true, min m n)
        | none => (false, m)



theorem compare_eq_diagnostic : compare ck cl n a b = diagnosticCompare ck cl n a b := by
  induction n using Nat.strongRecOn generalizing a b cl
  rename_i n ih
  unfold compare diagnosticCompare
  split
  · rfl
  rename_i n
  split
  · rfl
  generalize ha : Term.wnf ck cl n a [] = aw
  rcases aw with ⟨a', m⟩
  generalize hb : Term.wnf ck cl (min m n) b [] = bw
  rcases bw with ⟨b', m'⟩
  have H : ∀ cl m a b, compare ck cl (min m n) a b = diagnosticCompare ck cl (min m n) a b :=
    fun cl m a b => ih _ (by omega)
  simp only [hb]
  cases a' <;> cases b' <;>
    simp only [parts, diagnosticParts, Term.parts, childClosed, List.foldl, ↓reduceIte,
      Nat.min_assoc, Nat.min_self, H]



theorem diagnostic_sound (hb : Sees ck bk) :
    (diagnosticCompare ck cl n a b).1 = true → Equation bk a b := by
  rw [← compare_eq_diagnostic]
  exact compare_sound hb



end ConversionSpec

end

-- Source section: ErasedReduction
section

open Quan Term ConversionDesign



namespace ErasedReduction



abbrev EBook := String → Option Term



def eraseBook (bk : Book) : EBook := fun k => (Book.get bk k).map (erase ∘ Def.v)



-- This relation is only for comparison. It does not replace runtime Eval.
inductive EPar (bk : EBook) : Term → Term → Prop
  | var : EPar bk (Var i) (Var i)
  | ref : EPar bk (Ref k) (Ref k)
  | ann : EPar bk x x' → EPar bk T T' → EPar bk (Ann x T) (Ann x' T')
  | lett : EPar bk v v' → EPar bk f f' → EPar bk (Let q v f) (Let q v' f')
  | typ : EPar bk q q' → EPar bk (Typ q) (Typ q')
  | min : EPar bk a a' → EPar bk b b' → EPar bk (Min a b) (Min a' b')
  | all : EPar bk A A' → EPar bk B B' → EPar bk (All q A B) (All q A' B')
  | lam : EPar bk f f' → EPar bk (Lam Q1 f) (Lam Q1 f')
  | app : EPar bk f f' → EPar bk x x' → EPar bk (App Q1 f x) (App Q1 f' x')
  | sig : EPar bk A A' → EPar bk B B' → EPar bk (Sig q A B) (Sig q A' B')
  | tup : EPar bk a a' → EPar bk b b' → EPar bk (Tup q a b) (Tup q a' b')
  | prj : EPar bk h h' → EPar bk (Prj h) (Prj h')
  | enu : EPar bk (Enu ks) (Enu ks)
  | lab : EPar bk (Lab k) (Lab k)
  | mat : EPar bk h h' → EPar bk m m' → EPar bk (Mat k h m) (Mat k h' m')
  | efq : EPar bk Efq Efq
  | eql : EPar bk a a' → EPar bk b b' → EPar bk T T' →
      EPar bk (Eql a b T) (Eql a' b' T')
  | rfl : EPar bk Rfl Rfl
  | rwt : EPar bk e e' → EPar bk P P' → EPar bk f f' →
      EPar bk (Rwt e P f) (Rwt e' P' f')
  | delta : bk k = some v → Closed v → EPar bk (Ref k) v
  | unann : EPar bk x x' → EPar bk (Ann x T) x'
  | unlet : EPar bk v v' → EPar bk f f' → EPar bk (Let q v f) (inst f' v')
  | beta : EPar bk f f' → EPar bk x x' →
      EPar bk (App Q1 (Lam Q1 f) x) (inst f' x')
  | split : EPar bk h h' → EPar bk a a' → EPar bk b b' →
      EPar bk (App Q1 (Prj h) (Tup r a b)) (App Q1 (App Q1 h' a') b')
  | hit : EPar bk h h' → EPar bk (App Q1 (Mat k h m) (Lab k)) h'
  | miss : j ≠ k → EPar bk m m' →
      EPar bk (App Q1 (Mat k h m) (Lab j)) (App Q1 m' (Lab j))
  | cast : EPar bk f f' → EPar bk (Rwt Rfl P f) f'
  | meet : EPar bk a a' → EPar bk b b' → EPar bk (Min a b) (qmin a' b')
  | eta : EPar bk f f' →
      EPar bk (Lam Q1 (App Q1 (ren Nat.succ f) (Var 0))) f'



inductive EPars (bk : EBook) : Term → Term → Prop
  | refl : EPars bk t t
  | step : EPar bk t u → EPars bk u v → EPars bk t v



def EJoin (bk : EBook) (a b : Term) : Prop :=
  ∃ c, EPars bk a c ∧ EPars bk b c



theorem erase_inst : erase (inst f v) = inst (erase f) (erase v) := by
  unfold inst
  rw [erase_sub]
  congr 1
  funext i
  cases i <;> rfl



theorem erase_closed (hc : Closed t) : Closed (erase t) := by
  apply ren_closed
  rw [← erase_ren, ren_as_sub, hc]



theorem erase_qmin : erase (qmin a b) = qmin (erase a) (erase b) := by
  cases a <;> cases b <;> simp [qmin, erase]
  all_goals split <;> simp_all [erase]



def Canonical (t : Term) : Prop := erase t = t



def EBook.Canonical (bk : EBook) : Prop := ∀ k v, bk k = some v → ErasedReduction.Canonical v



theorem erase_idem (t : Term) : erase (erase t) = erase t := by
  induction t <;> simp [erase, *]



theorem eraseBook_canonical : EBook.Canonical (eraseBook bk) := by
  intro k v h
  unfold eraseBook at h
  cases hg : Book.get bk k <;> simp [hg] at h
  subst h
  exact erase_idem _



theorem canonical_sub (ht : Canonical t) (hs : ∀ i, Canonical (σ i)) :
    Canonical (sub σ t) := by
  unfold Canonical at *
  rw [erase_sub, ht]
  have he : erase ∘ σ = σ := funext hs
  rw [he]



theorem canonical_shift (ht : Canonical (ren Nat.succ t)) : Canonical t := by
  unfold Canonical at *
  rw [erase_ren] at ht
  have he := congrArg (sub (Subst.one Rfl)) ht
  simp only [sub_ren] at he
  change sub Var (erase t) = sub Var t at he
  simpa only [sub_var] using he



theorem epar_canonical (hb : EBook.Canonical bk) (h : EPar bk a b) :
    Canonical a → Canonical b := by
  induction h
  case delta hk _ => intro _; exact hb _ _ hk
  case eta f f' h ih =>
    intro ht
    have hs : Canonical (ren Nat.succ f) := by simpa [Canonical, erase] using ht
    exact ih (canonical_shift hs)
  all_goals intro ht; simp_all [Canonical, erase, erase_inst, erase_qmin]



theorem epar_refl_erase (t : Term) : EPar bk (erase t) (erase t) := by
  induction t <;> simp only [erase] <;> constructor <;> assumption



theorem epar_refl (ht : Canonical t) : EPar bk t t := by
  rw [← ht]
  exact epar_refl_erase _



theorem epar_ren (h : EPar bk t u) : EPar bk (ren r t) (ren r u) := by
  induction h generalizing r <;> simp [ren, ren_inst]
  case delta hk hc => rw [ren_as_sub, hc]; exact .delta hk hc
  case meet =>
    rcases qmin_map (ren r) (fun _ => rfl) with e | e <;> rw [e] <;>
      constructor <;> apply_assumption
  case eta h ih =>
    simpa only [ren_ren, Function.comp_def, Ren.up] using EPar.eta (ih (r := r))
  all_goals first | apply EPar.split | apply EPar.miss | constructor
  all_goals first | assumption | apply_assumption



-- Substitution preserves every comparison step, including eta.
theorem epar_sub (h : EPar bk t u) (hs : ∀ i, EPar bk (σ i) (τ i)) :
    EPar bk (sub σ t) (sub τ u) := by
  have U {σ τ} (h : ∀ i, EPar bk (σ i) (τ i)) : ∀ i, EPar bk (Subst.up σ i) (Subst.up τ i)
    | 0 => .var
    | _ + 1 => epar_ren (h _)
  induction h generalizing σ τ <;> simp [sub, inst_sub]
  case delta hk hc => rw [hc]; exact .delta hk hc
  case meet =>
    rcases qmin_map (sub τ) (fun _ => rfl) with e | e <;> rw [e] <;>
      constructor <;> apply_assumption <;> exact hs
  case eta h ih =>
    simp only [sub_succ]
    exact .eta (ih hs)
  all_goals first | exact hs _ | apply EPar.split | apply EPar.miss | constructor
  all_goals first | assumption | (apply_assumption; (repeat apply U); exact hs)



theorem epars_sub (h : EPars bk t u) (hs : ∀ i, Canonical (σ i)) :
    EPars bk (sub σ t) (sub σ u) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (epar_sub h (fun i => epar_refl (hs i))) ih



theorem ejoin_sub (h : EJoin bk a b) (hs : ∀ i, Canonical (σ i)) :
    EJoin bk (sub σ a) (sub σ b) := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨sub σ c, epars_sub ha hs, epars_sub hb hs⟩



def expand (f : Term) : Term := Lam Q1 (App Q1 (ren Nat.succ f) (Var 0))



theorem eta_join (hf : Canonical f) : EJoin bk (expand f) f :=
  ⟨f, .step (.eta (epar_refl hf)) .refl, .refl⟩



-- Each old parallel step has one comparison step after erasure.
theorem erase_par (h : Par bk a b) : EPar (eraseBook bk) (erase a) (erase b) := by
  induction h <;> simp only [erase, erase_inst, erase_qmin]
  case delta hk hc =>
    exact .delta (by simp [eraseBook, hk]) (erase_closed hc)
  all_goals first | apply EPar.split | apply EPar.miss | constructor
  all_goals assumption



theorem erase_pars (h : Pars bk a b) : EPars (eraseBook bk) (erase a) (erase b) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (erase_par h) ih



theorem erase_conv (h : Conv bk a b) : EJoin (eraseBook bk) (erase a) (erase b) := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨erase c, erase_pars ha, erase_pars hb⟩



def Rigid (t : Term) : Prop := t.former ∈ [1, 2, 3, 4, 5]



-- Eta can change a function head. It does not change a rigid type head.
theorem epar_rigid (h : EPar bk a b) (ha : Rigid a) : b.former = a.former := by
  cases h <;> simp_all [Rigid, former]



theorem epars_rigid (h : EPars bk a b) (ha : Rigid a) : b.former = a.former := by
  induction h with
  | refl => rfl
  | step h _ ih =>
    have e := epar_rigid h ha
    exact (ih (by simpa only [Rigid, e] using ha)).trans e



theorem ejoin_rigid (h : EJoin bk a b) (ha : Rigid a) (hb : Rigid b) :
    a.former = b.former := by
  obtain ⟨c, h₁, h₂⟩ := h
  exact (epars_rigid h₁ ha).symm.trans (epars_rigid h₂ hb)



theorem epar_all (h : EPar bk (All q A B) t) :
    ∃ C D, t = All q C D ∧ EPar bk A C ∧ EPar bk B D := by
  cases h with | all hA hB => exact ⟨_, _, rfl, hA, hB⟩



theorem epars_all (h : EPars bk s t) : s = All q A B →
    ∃ C D, t = All q C D ∧ EPars bk A C ∧ EPars bk B D := by
  induction h generalizing q A B with
  | refl => intro e; subst e; exact ⟨_, _, rfl, .refl, .refl⟩
  | step h _ ih =>
    intro e; subst e
    obtain ⟨C, D, rfl, hA, hB⟩ := epar_all h
    obtain ⟨C', D', rfl, hC, hD⟩ := ih rfl
    exact ⟨_, _, rfl, .step hA hC, .step hB hD⟩



theorem ejoin_all (h : EJoin bk (All p A B) (All q C D)) :
    p = q ∧ EJoin bk A C ∧ EJoin bk B D := by
  obtain ⟨t, h₁, h₂⟩ := h
  obtain ⟨A', B', rfl, hA, hB⟩ := epars_all h₁ rfl
  obtain ⟨C', D', e, hC, hD⟩ := epars_all h₂ rfl
  cases e
  exact ⟨rfl, ⟨_, hA, hC⟩, ⟨_, hB, hD⟩⟩



end ErasedReduction

end

-- Source section: CriticalPairs
section

open Quan Term ConversionDesign ErasedReduction



namespace CriticalPairs



theorem ren_injective (r : Nat → Nat) (hr : Function.Injective r) :
    Function.Injective (ren r) := by
  classical
  intro a b h
  let s : Nat → Term := fun i => if hi : ∃ j, r j = i then Var (Classical.choose hi) else Rfl
  have hs : s ∘ r = Var := by
    funext i
    simp only [Function.comp_def, s, dite_eq_left (show ∃ j, r j = r i from ⟨i, rfl⟩)]
    congr 1
    exact hr (Classical.choose_spec (show ∃ j, r j = r i from ⟨i, rfl⟩))
  have he := congrArg (sub s) h
  simpa only [sub_ren, hs, sub_var] using he



theorem epar_ren_fix (h : EPar bk t u) :
    ren r t = t → ren r u = u := by
  induction h generalizing r <;> simp only [ren] <;> intro ht
  case var => exact ht
  case ref => trivial
  case delta hk hc => exact (ren_as_sub _).trans (hc _)
  case unann ih => exact ih (Term.Ann.inj ht).1
  case unlet hv hf ihv ihf =>
    obtain ⟨_, hv, hf⟩ := Term.Let.inj ht
    rw [ren_inst, ihv hv, ihf hf]
  case beta hf hx ihf ihx =>
    obtain ⟨_, hf, hx⟩ := Term.App.inj ht
    rw [ren_inst, ihf (Term.Lam.inj hf).2, ihx hx]
  case split hh ha hb ihh iha ihb =>
    obtain ⟨_, hh, ht⟩ := Term.App.inj ht
    obtain ⟨_, ha, hb⟩ := Term.Tup.inj ht
    simp only [ihh (Term.Prj.inj hh), iha ha, ihb hb]
  case hit hh ihh =>
    have hh := (Term.App.inj ht).2.1
    exact ihh (Term.Mat.inj hh).2.1
  case miss hne hm ihm =>
    have hm := (Term.Mat.inj (Term.App.inj ht).2.1).2.2
    simp only [ihm hm]
  case cast hf ihf => exact ihf (Term.Rwt.inj ht).2.2
  case meet ha hb iha ihb =>
    obtain ⟨ha, hb⟩ := Term.Min.inj ht
    rcases qmin_map (ren r) (fun _ => rfl) with he | he
    · rw [he]; simp only [ren, iha ha, ihb hb]
    · rw [he, iha ha, ihb hb]
  case eta f f' hf ihf =>
    have he := (Term.App.inj (Term.Lam.inj ht).2).2.1
    have hr : ren r f = f := by
      apply ren_injective Nat.succ (fun _ _ h => Nat.succ.inj h)
      simpa only [ren_ren, Function.comp_def, Ren.up] using he
    exact ihf hr
  all_goals simp_all only [Term.Ann.injEq, Term.Let.injEq, Term.Typ.injEq,
    Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq,
    Term.Sig.injEq, Term.Tup.injEq, Term.Prj.injEq, Term.Mat.injEq,
    Term.Eql.injEq, Term.Rwt.injEq]



theorem qmin_epar (ha : EPar bk a A) (hb : EPar bk b B) :
    EPar bk (qmin a b) (qmin A B) := by
  have L {k c} (h : EPar bk (Lab k) c) : c = Lab k := by cases h; rfl
  rcases qmin_view a b with e | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl | rfl, e⟩ | ⟨rfl, rfl, e⟩ <;> rw [e]
  · exact .meet ha hb
  all_goals (try cases L ha) <;> (try cases L hb) <;> (try simp only [qmin_eq]) <;> first
    | assumption | exact .lab | exact e ▸ .lab



end CriticalPairs

end

-- Source section: EtaPeak
section

open Quan Term ConversionDesign ErasedReduction CriticalPairs



namespace EtaPeak



def skipZero : Nat → Nat
  | 0 => 1
  | i + 1 => i + 1



theorem unshift_retract (h : ren skipZero t = t) :
    ren Nat.succ (sub (Subst.one Rfl) t) = t := by
  rw [ren_sub]
  apply ren_fix t h
  intro i hi
  cases i with
  | zero => simp [skipZero] at hi
  | succ i => rfl



-- Every reduct of a shifted term has a unique unshifted representative.
theorem epar_unshift (h : EPar bk (ren Nat.succ f) t) :
    ∃ g, EPar bk f g ∧ t = ren Nat.succ g := by
  have hs : ren skipZero (ren Nat.succ f) = ren Nat.succ f := by
    rw [ren_ren]
    rfl
  have ht := epar_ren_fix h hs
  refine ⟨sub (Subst.one Rfl) t, ?_, (unshift_retract ht).symm⟩
  have hh := epar_sub h (σ := Subst.one Rfl) (τ := Subst.one Rfl)
    (fun i => by cases i <;> constructor)
  rw [sub_ren] at hh
  change EPar bk (sub Var f) (sub (Subst.one Rfl) t) at hh
  simpa only [sub_var] using hh



theorem inst_shift_under (t : Term) :
    inst (ren (Ren.up Nat.succ) t) (Var 0) = t := by
  simp only [inst, sub_ren]
  have hs : Subst.one (Var 0) ∘ Ren.up Nat.succ = Var := by
    funext i
    cases i <;> rfl
  rw [hs, sub_var]



-- Classify all one-step reducts of an eta expansion, including inner beta.
theorem expansion_reduct (h : EPar bk (expand f) t) :
    ∃ g, EPar bk f g ∧ (t = g ∨ t = expand g) := by
  generalize hs : expand f = s at h
  cases h <;> simp [expand] at hs
  case lam body body' h =>
    subst body
    generalize ha : App Q1 (ren Nat.succ f) (Var 0) = a at h
    cases h <;> simp at ha
    case app f0 f1 x0 x1 hf hx =>
      obtain ⟨hf0, hx0⟩ := ha
      subst f0
      subst x0
      cases hx
      obtain ⟨g, hg, rfl⟩ := epar_unshift hf
      exact ⟨g, hg, .inr rfl⟩
    case beta body body' x x' hf hx =>
      obtain ⟨he, hx0⟩ := ha
      subst x
      cases hx
      have hp : EPar bk (ren Nat.succ f) (Lam Q1 body') := by
        rw [he]
        exact .lam hf
      obtain ⟨g, hg, he'⟩ := epar_unshift hp
      cases g <;> simp [ren] at he'
      case Lam q g =>
        obtain ⟨rfl, rfl⟩ := he'
        exact ⟨_, hg, .inl (congrArg (Lam Q1) (inst_shift_under g))⟩
  case eta g h =>
    have e : f = g := ren_injective Nat.succ (fun _ _ h => Nat.succ.inj h) hs
    subst g
    exact ⟨t, h, .inl rfl⟩



def DiamondAt (bk : EBook) (f : Term) : Prop :=
  ∀ a b, EPar bk f a → EPar bk f b → ∃ c, EPar bk a c ∧ EPar bk b c



-- A complete outer-eta peak reduces to a peak of the unexpanded function.
theorem expansion_diamond (hd : DiamondAt bk f) : DiamondAt bk (expand f) := by
  intro a b ha hb
  obtain ⟨g, hg, he⟩ := expansion_reduct ha
  obtain ⟨h, hh, hf⟩ := expansion_reduct hb
  obtain ⟨c, hgc, hhc⟩ := hd g h hg hh
  refine ⟨c, ?_, ?_⟩
  · rcases he with rfl | rfl
    · exact hgc
    · exact .eta hgc
  · rcases hf with rfl | rfl
    · exact hhc
    · exact .eta hhc



end EtaPeak

end

-- Source section: PrimitivePeaks
section

open Quan Term ConversionDesign ErasedReduction CriticalPairs EtaPeak



namespace PrimitivePeaks



-- Definition bodies can be recursive. This peak only needs a canonical body.
theorem ref_diamond (hbk : EBook.Canonical bk) : DiamondAt bk (Ref k) := by
  intro a b ha hb
  cases ha with
  | ref =>
    cases hb with
    | ref => exact ⟨Ref k, .ref, .ref⟩
    | delta hk hc => exact ⟨_, .delta hk hc, epar_refl (hbk _ _ hk)⟩
  | delta hk hc =>
    cases hb with
    | ref => exact ⟨_, epar_refl (hbk _ _ hk), .delta hk hc⟩
    | delta hk' hc' =>
      have he := Option.some.inj (hk.symm.trans hk')
      subst he
      exact ⟨_, epar_refl (hbk _ _ hk), epar_refl (hbk _ _ hk)⟩



theorem min_diamond (ha : DiamondAt bk a) (hb : DiamondAt bk b) :
    DiamondAt bk (Min a b) := by
  intro x y hx hy
  cases hx with
  | min hax hbx =>
    cases hy with
    | min hay hby =>
      obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
      obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
      exact ⟨qmin A B, .meet hAx hBx, .meet hAy hBy⟩
    | meet hay hby =>
      obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
      obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
      exact ⟨qmin A B, .meet hAx hBx, qmin_epar hAy hBy⟩
  | meet hax hbx =>
    cases hy with
    | min hay hby =>
      obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
      obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
      exact ⟨qmin A B, qmin_epar hAx hBx, .meet hAy hBy⟩
    | meet hay hby =>
      obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
      obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
      exact ⟨qmin A B, qmin_epar hAx hBx, qmin_epar hAy hBy⟩



theorem rwt_diamond (he : DiamondAt bk e) (hP : DiamondAt bk P)
    (hf : DiamondAt bk f) : DiamondAt bk (Rwt e P f) := by
  intro x y hx hy
  cases hx with
  | rwt hex hPx hfx =>
    cases hy with
    | rwt hey hPy hfy =>
      obtain ⟨E, hEx, hEy⟩ := he _ _ hex hey
      obtain ⟨Q, hQx, hQy⟩ := hP _ _ hPx hPy
      obtain ⟨F, hFx, hFy⟩ := hf _ _ hfx hfy
      exact ⟨Rwt E Q F, .rwt hEx hQx hFx, .rwt hEy hQy hFy⟩
    | cast hfy =>
      cases hex
      obtain ⟨F, hFx, hFy⟩ := hf _ _ hfx hfy
      exact ⟨F, .cast hFx, hFy⟩
  | cast hfx =>
    cases hy with
    | rwt hey hPy hfy =>
      cases hey
      obtain ⟨F, hFx, hFy⟩ := hf _ _ hfx hfy
      exact ⟨F, hFx, .cast hFy⟩
    | cast hfy => exact hf _ _ hfx hfy



theorem split_diamond (hh : DiamondAt bk h) (ha : DiamondAt bk a)
    (hb : DiamondAt bk b) : DiamondAt bk (App Q1 (Prj h) (Tup q a b)) := by
  intro x y hx hy
  cases hx with
  | app hpx htx =>
    cases hpx with | prj hhx =>
      cases htx with | tup hax hbx =>
        cases hy with
        | app hpy hty =>
          cases hpy with | prj hhy =>
            cases hty with | tup hay hby =>
              obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
              obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
              obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
              exact ⟨App Q1 (App Q1 H A) B, .split hHx hAx hBx, .split hHy hAy hBy⟩
        | split hhy hay hby =>
          obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
          obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
          obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
          exact ⟨App Q1 (App Q1 H A) B, .split hHx hAx hBx, .app (.app hHy hAy) hBy⟩
  | split hhx hax hbx =>
    cases hy with
    | app hpy hty =>
      cases hpy with | prj hhy =>
        cases hty with | tup hay hby =>
          obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
          obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
          obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
          exact ⟨App Q1 (App Q1 H A) B, .app (.app hHx hAx) hBx, .split hHy hAy hBy⟩
    | split hhy hay hby =>
      obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
      obtain ⟨A, hAx, hAy⟩ := ha _ _ hax hay
      obtain ⟨B, hBx, hBy⟩ := hb _ _ hbx hby
      exact ⟨App Q1 (App Q1 H A) B, .app (.app hHx hAx) hBx, .app (.app hHy hAy) hBy⟩



theorem hit_diamond (hh : DiamondAt bk h) :
    DiamondAt bk (App Q1 (Mat k h m) (Lab k)) := by
  intro x y hx hy
  cases hx with
  | app hmx hlx =>
    cases hmx with | mat hhx hmx =>
      cases hlx
      cases hy with
      | app hmy hly =>
        cases hmy with | mat hhy hmy =>
          cases hly
          obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
          exact ⟨H, .hit hHx, .hit hHy⟩
      | hit hhy =>
        obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
        exact ⟨H, .hit hHx, hHy⟩
      | miss hne _ => exact (hne rfl).elim
  | hit hhx =>
    cases hy with
    | app hmy hly =>
      cases hmy with | mat hhy hmy =>
        cases hly
        obtain ⟨H, hHx, hHy⟩ := hh _ _ hhx hhy
        exact ⟨H, hHx, .hit hHy⟩
    | hit hhy => exact hh _ _ hhx hhy
    | miss hne _ => exact (hne rfl).elim
  | miss hne _ => exact (hne rfl).elim



theorem miss_diamond (hne : j ≠ k) (hm : DiamondAt bk m) :
    DiamondAt bk (App Q1 (Mat k h m) (Lab j)) := by
  intro x y hx hy
  cases hx with
  | app hmx hlx =>
    cases hmx with | mat hhx hmx =>
      cases hlx
      cases hy with
      | app hmy hly =>
        cases hmy with | mat hhy hmy =>
          cases hly
          obtain ⟨M, hMx, hMy⟩ := hm _ _ hmx hmy
          exact ⟨App Q1 M (Lab j), .miss hne hMx, .miss hne hMy⟩
      | hit _ => exact (hne rfl).elim
      | miss _ hmy =>
        obtain ⟨M, hMx, hMy⟩ := hm _ _ hmx hmy
        exact ⟨App Q1 M (Lab j), .miss hne hMx, .app hMy .lab⟩
  | hit _ => exact (hne rfl).elim
  | miss _ hmx =>
    cases hy with
    | app hmy hly =>
      cases hmy with | mat hhy hmy =>
        cases hly
        obtain ⟨M, hMx, hMy⟩ := hm _ _ hmx hmy
        exact ⟨App Q1 M (Lab j), .app hMx .lab, .miss hne hMy⟩
    | hit _ => exact (hne rfl).elim
    | miss _ hmy =>
      obtain ⟨M, hMx, hMy⟩ := hm _ _ hmx hmy
      exact ⟨App Q1 M (Lab j), .app hMx .lab, .app hMy .lab⟩



end PrimitivePeaks

end

-- Source section: BetaEtaPeak
section

open Quan Term ConversionDesign ErasedReduction CriticalPairs EtaPeak



namespace BetaEtaPeak



theorem epar_inst (hf : EPar bk f f') (hx : EPar bk x x') :
    EPar bk (inst f x) (inst f' x') := by
  exact epar_sub hf (σ := Subst.one x) (τ := Subst.one x') (by
    intro i
    cases i with
    | zero => exact hx
    | succ i => exact .var)



theorem inst_eta_body (g x : Term) :
    inst (App Q1 (ren Nat.succ g) (Var 0)) x = App Q1 g x := by
  simp only [inst, sub, sub_ren, Subst.one]
  exact congrArg (App Q1 · x) (sub_var g)



-- This joins beta with an eta contraction in the function position.
-- The assumptions concern the original body and original argument.
theorem beta_head_eta_join
    (hb : DiamondAt bk (App Q1 (ren Nat.succ g) (Var 0)))
    (hx : DiamondAt bk x)
    (hf : EPar bk (App Q1 (ren Nat.succ g) (Var 0)) f')
    (hg : EPar bk g g')
    (hxa : EPar bk x xa) (hxb : EPar bk x xb) :
    ∃ c, EPar bk (inst f' xa) c ∧ EPar bk (App Q1 g' xb) c := by
  have he : EPar bk (App Q1 (ren Nat.succ g) (Var 0))
      (App Q1 (ren Nat.succ g') (Var 0)) := .app (epar_ren hg) .var
  obtain ⟨B, hfB, heB⟩ := hb _ _ hf he
  obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
  refine ⟨inst B X, epar_inst hfB hXa, ?_⟩
  rw [← inst_eta_body g' xb]
  exact epar_inst heB hXb



-- This theorem is conditional. It does not prove the three child diamonds.
theorem beta_application_diamond
    (hLam : DiamondAt bk (Lam Q1 f))
    (hf : DiamondAt bk f) (hx : DiamondAt bk x) :
    DiamondAt bk (App Q1 (Lam Q1 f) x) := by
  intro a b ha hb
  cases ha with
  | app hfa hxa =>
    cases hb with
    | app hfb hxb =>
      obtain ⟨F, hFa, hFb⟩ := hLam _ _ hfa hfb
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨App Q1 F X, .app hFa hXa, .app hFb hXb⟩
    | beta hfb hxb =>
      cases hfa with
      | lam hfa =>
        obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
        obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
        exact ⟨inst F X, .beta hFa hXa, epar_inst hFb hXb⟩
      | eta hg =>
        obtain ⟨c, hbc, hac⟩ := beta_head_eta_join hf hx hfb hg hxb hxa
        exact ⟨c, hac, hbc⟩
  | beta hfa hxa =>
    cases hb with
    | app hfb hxb =>
      cases hfb with
      | lam hfb =>
        obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
        obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
        exact ⟨inst F X, epar_inst hFa hXa, .beta hFb hXb⟩
      | eta hg =>
        exact beta_head_eta_join hf hx hfa hg hxa hxb
    | beta hfb hxb =>
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨inst F X, epar_inst hFa hXa, epar_inst hFb hXb⟩



-- Annotation peaks can join after the annotation is removed.
theorem ann_diamond (hx : DiamondAt bk x) : DiamondAt bk (Ann x T) := by
  intro a b ha hb
  cases ha with
  | ann hxa hTa =>
    cases hb with
    | ann hxb hTb =>
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨X, .unann hXa, .unann hXb⟩
    | unann hxb =>
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨X, .unann hXa, hXb⟩
  | unann hxa =>
    cases hb with
    | ann hxb hTb =>
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨X, hXa, .unann hXb⟩
    | unann hxb => exact hx _ _ hxa hxb



theorem let_diamond (hv : DiamondAt bk v) (hf : DiamondAt bk f) :
    DiamondAt bk (Let q v f) := by
  intro a b ha hb
  cases ha with
  | lett hva hfa =>
    cases hb with
    | lett hvb hfb =>
      obtain ⟨V, hVa, hVb⟩ := hv _ _ hva hvb
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      exact ⟨inst F V, .unlet hVa hFa, .unlet hVb hFb⟩
    | unlet hvb hfb =>
      obtain ⟨V, hVa, hVb⟩ := hv _ _ hva hvb
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      exact ⟨inst F V, .unlet hVa hFa, epar_inst hFb hVb⟩
  | unlet hva hfa =>
    cases hb with
    | lett hvb hfb =>
      obtain ⟨V, hVa, hVb⟩ := hv _ _ hva hvb
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      exact ⟨inst F V, epar_inst hFa hVa, .unlet hVb hFb⟩
    | unlet hvb hfb =>
      obtain ⟨V, hVa, hVb⟩ := hv _ _ hva hvb
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      exact ⟨inst F V, epar_inst hFa hVa, epar_inst hFb hVb⟩



theorem lambda_no_eta_diamond (hf : DiamondAt bk f)
    (hne : ∀ g, f ≠ App Q1 (ren Nat.succ g) (Var 0)) :
    DiamondAt bk (Lam Q1 f) := by
  intro a b ha hb
  cases ha with
  | lam hfa =>
    cases hb with
    | lam hfb =>
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      exact ⟨Lam Q1 F, .lam hFa, .lam hFb⟩
    | eta hg => exact (hne _ rfl).elim
  | eta hg => exact (hne _ rfl).elim



end BetaEtaPeak

end

-- Source section: GlobalDiamond
section

open Quan Term ConversionDesign ErasedReduction CriticalPairs EtaPeak PrimitivePeaks BetaEtaPeak



namespace GlobalDiamond



def nodes : Term → Nat
  | Var _ | Ref _ | Enu _ | Lab _ | Efq | Rfl => 1
  | Typ q | Lam _ q | Prj q => nodes q + 1
  | Ann x T | Let _ x T | Term.Min x T | All _ x T | App _ x T |
    Sig _ x T | Tup _ x T | Mat _ x T => nodes x + nodes T + 1
  | Eql a b T | Rwt a b T => nodes a + nodes b + nodes T + 1



theorem nodes_ren (t : Term) : nodes (ren r t) = nodes t := by
  induction t generalizing r <;> simp [ren, nodes, *]



def NoRoot (f x : Term) : Prop :=
  (∀ b, f ≠ Lam Q1 b) ∧
  (∀ h q a b, f = Prj h → x ≠ Tup q a b) ∧
  (∀ k h m j, f = Mat k h m → x ≠ Lab j)



theorem app_no_root (hn : NoRoot f x) (hf : DiamondAt bk f) (hx : DiamondAt bk x) :
    DiamondAt bk (App Q1 f x) := by
  intro a b ha hb
  cases ha with
  | app hfa hxa =>
    cases hb with
    | app hfb hxb =>
      obtain ⟨F, hFa, hFb⟩ := hf _ _ hfa hfb
      obtain ⟨X, hXa, hXb⟩ := hx _ _ hxa hxb
      exact ⟨App Q1 F X, .app hFa hXa, .app hFb hXb⟩
    | beta _ _ => exact (hn.1 _ rfl).elim
    | split _ _ _ => exact (hn.2.1 _ _ _ _ rfl rfl).elim
    | hit _ => exact (hn.2.2 _ _ _ _ rfl rfl).elim
    | miss _ _ => exact (hn.2.2 _ _ _ _ rfl rfl).elim
  | beta _ _ => exact (hn.1 _ rfl).elim
  | split _ _ _ => exact (hn.2.1 _ _ _ _ rfl rfl).elim
  | hit _ => exact (hn.2.2 _ _ _ _ rfl rfl).elim
  | miss _ _ => exact (hn.2.2 _ _ _ _ rfl rfl).elim



theorem diamond (hbk : EBook.Canonical bk) (ht : Canonical t) : DiamondAt bk t := by
  have main : ∀ n t, nodes t = n → Canonical t → DiamondAt bk t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro t hn ht
      subst n
      cases t with
      | Var i => intro a b ha hb; cases ha; cases hb; exact ⟨_, .var, .var⟩
      | Ref k => exact ref_diamond hbk
      | Enu ks => intro a b ha hb; cases ha; cases hb; exact ⟨_, .enu, .enu⟩
      | Lab k => intro a b ha hb; cases ha; cases hb; exact ⟨_, .lab, .lab⟩
      | Efq => intro a b ha hb; cases ha; cases hb; exact ⟨_, .efq, .efq⟩
      | Rfl => intro a b ha hb; cases ha; cases hb; exact ⟨_, .rfl, .rfl⟩
      | Ann x T =>
        have hc : Canonical x ∧ Canonical T := by simpa [Canonical, erase] using ht
        exact ann_diamond (ih _ (by simp [nodes]; omega) _ rfl hc.1)
      | Let q v f =>
        have hc : Canonical v ∧ Canonical f := by simpa [Canonical, erase] using ht
        exact let_diamond (ih _ (by simp [nodes]; omega) _ rfl hc.1)
          (ih _ (by simp [nodes]; omega) _ rfl hc.2)
      | All q A B =>
        have hc : Canonical A ∧ Canonical B := by simpa [Canonical, erase] using ht
        have hA := ih _ (by simp [nodes]; omega) _ rfl hc.1
        have hB := ih _ (by simp [nodes]; omega) _ rfl hc.2
        intro a b ha hb
        cases ha with | all hAa hBa =>
          cases hb with | all hAb hBb =>
            obtain ⟨C, hCa, hCb⟩ := hA _ _ hAa hAb
            obtain ⟨D, hDa, hDb⟩ := hB _ _ hBa hBb
            exact ⟨All q C D, .all hCa hDa, .all hCb hDb⟩
      | Sig q A B =>
        have hc : Canonical A ∧ Canonical B := by simpa [Canonical, erase] using ht
        have hA := ih _ (by simp [nodes]; omega) _ rfl hc.1
        have hB := ih _ (by simp [nodes]; omega) _ rfl hc.2
        intro a b ha hb
        cases ha with | sig hAa hBa =>
          cases hb with | sig hAb hBb =>
            obtain ⟨C, hCa, hCb⟩ := hA _ _ hAa hAb
            obtain ⟨D, hDa, hDb⟩ := hB _ _ hBa hBb
            exact ⟨Sig q C D, .sig hCa hDa, .sig hCb hDb⟩
      | Tup q A B =>
        have hc : Canonical A ∧ Canonical B := by simpa [Canonical, erase] using ht
        have hA := ih _ (by simp [nodes]; omega) _ rfl hc.1
        have hB := ih _ (by simp [nodes]; omega) _ rfl hc.2
        intro a b ha hb
        cases ha with | tup hAa hBa =>
          cases hb with | tup hAb hBb =>
            obtain ⟨C, hCa, hCb⟩ := hA _ _ hAa hAb
            obtain ⟨D, hDa, hDb⟩ := hB _ _ hBa hBb
            exact ⟨Tup q C D, .tup hCa hDa, .tup hCb hDb⟩
      | Mat k A B =>
        have hc : Canonical A ∧ Canonical B := by simpa [Canonical, erase] using ht
        have hA := ih _ (by simp [nodes]; omega) _ rfl hc.1
        have hB := ih _ (by simp [nodes]; omega) _ rfl hc.2
        intro a b ha hb
        cases ha with | mat hAa hBa =>
          cases hb with | mat hAb hBb =>
            obtain ⟨C, hCa, hCb⟩ := hA _ _ hAa hAb
            obtain ⟨D, hDa, hDb⟩ := hB _ _ hBa hBb
            exact ⟨Mat k C D, .mat hCa hDa, .mat hCb hDb⟩
      | Eql A B T =>
        have hc : Canonical A ∧ Canonical B ∧ Canonical T := by simpa [Canonical, erase] using ht
        have hA := ih _ (by simp [nodes]; omega) _ rfl hc.1
        have hB := ih _ (by simp [nodes]; omega) _ rfl hc.2.1
        have hT := ih _ (by simp [nodes]; omega) _ rfl hc.2.2
        intro a b ha hb
        cases ha with | eql hAa hBa hTa =>
          cases hb with | eql hAb hBb hTb =>
            obtain ⟨C, hCa, hCb⟩ := hA _ _ hAa hAb
            obtain ⟨D, hDa, hDb⟩ := hB _ _ hBa hBb
            obtain ⟨U, hUa, hUb⟩ := hT _ _ hTa hTb
            exact ⟨Eql C D U, .eql hCa hDa hUa, .eql hCb hDb hUb⟩
      | Typ q =>
        have hq : DiamondAt bk q := ih (nodes q) (by simp [nodes]) q rfl (by simpa [Canonical, erase] using ht)
        intro a b ha hb
        cases ha with | typ ha =>
          cases hb with | typ hb =>
            obtain ⟨Q, hQa, hQb⟩ := hq _ _ ha hb
            exact ⟨Typ Q, .typ hQa, .typ hQb⟩
      | Prj h =>
        have hh : DiamondAt bk h := ih (nodes h) (by simp [nodes]) h rfl (by simpa [Canonical, erase] using ht)
        intro a b ha hb
        cases ha with | prj ha =>
          cases hb with | prj hb =>
            obtain ⟨H, hHa, hHb⟩ := hh _ _ ha hb
            exact ⟨Prj H, .prj hHa, .prj hHb⟩
      | Min a b =>
        have hc : Canonical a ∧ Canonical b := by simpa [Canonical, erase] using ht
        exact min_diamond (ih _ (by simp [nodes]; omega) _ rfl hc.1)
          (ih _ (by simp [nodes]; omega) _ rfl hc.2)
      | Rwt e P f =>
        have hc : Canonical e ∧ Canonical P ∧ Canonical f := by simpa [Canonical, erase] using ht
        exact rwt_diamond (ih _ (by simp [nodes]; omega) _ rfl hc.1)
          (ih _ (by simp [nodes]; omega) _ rfl hc.2.1)
          (ih _ (by simp [nodes]; omega) _ rfl hc.2.2)
      | Lam q body =>
        have hc : q = Q1 ∧ Canonical body := by simpa [Canonical, erase, eq_comm] using ht
        obtain ⟨rfl, hc⟩ := hc
        by_cases he : ∃ g, body = App Q1 (ren Nat.succ g) (Var 0)
        · obtain ⟨g, rfl⟩ := he
          have hg : Canonical g := canonical_shift (by simpa [Canonical, erase] using hc)
          exact expansion_diamond (ih (nodes g) (by simp [nodes, nodes_ren]; omega) g rfl hg)
        · exact lambda_no_eta_diamond (ih _ (by simp [nodes]) _ rfl hc) (fun g h => he ⟨g, h⟩)
      | App q f x =>
        have hc : q = Q1 ∧ Canonical f ∧ Canonical x := by simpa [Canonical, erase, eq_comm] using ht
        obtain ⟨rfl, hcf, hcx⟩ := hc
        have hf := ih (nodes f) (by simp [nodes]; omega) f rfl hcf
        have hx := ih (nodes x) (by simp [nodes]; omega) x rfl hcx
        cases f with
        | Lam q body =>
          have hc : q = Q1 ∧ Canonical body := by simpa [Canonical, erase, eq_comm] using hcf
          obtain ⟨rfl, hc⟩ := hc
          exact beta_application_diamond hf (ih _ (by simp [nodes]; omega) _ rfl hc) hx
        | Prj h =>
          have hh : DiamondAt bk h := ih _ (by simp [nodes]; omega) _ rfl (by simpa [Canonical, erase] using hcf)
          cases x with
          | Tup q a b =>
            have hc : Canonical a ∧ Canonical b := by simpa [Canonical, erase] using hcx
            exact split_diamond hh (ih _ (by simp [nodes]; omega) _ rfl hc.1)
              (ih _ (by simp [nodes]; omega) _ rfl hc.2)
          | _ => exact app_no_root (by simp [NoRoot]) hf hx
        | Mat k h m =>
          have hc : Canonical h ∧ Canonical m := by simpa [Canonical, erase] using hcf
          cases x with
          | Lab j =>
            by_cases he : j = k
            · subst j; exact hit_diamond (ih _ (by simp [nodes]; omega) _ rfl hc.1)
            · exact miss_diamond he (ih _ (by simp [nodes]; omega) _ rfl hc.2)
          | _ => exact app_no_root (by simp [NoRoot]) hf hx
        | _ => exact app_no_root (by simp [NoRoot]) hf hx
  exact main (nodes t) t rfl ht



theorem strip (hbk : EBook.Canonical bk) (ha : Canonical a)
    (h : EPar bk a b) (p : EPars bk a c) :
    ∃ d, EPars bk b d ∧ EPar bk c d := by
  induction p generalizing b with
  | refl => exact ⟨b, .refl, h⟩
  | step s p ih =>
    obtain ⟨d, hbd, had⟩ := diamond hbk ha _ _ h s
    obtain ⟨e, hde, hce⟩ := ih (epar_canonical hbk s ha) had
    exact ⟨e, .step hbd hde, hce⟩



theorem confluent (hbk : EBook.Canonical bk) (ha : Canonical a)
    (p : EPars bk a b) (q : EPars bk a c) :
    ∃ d, EPars bk b d ∧ EPars bk c d := by
  induction p generalizing c with
  | refl => exact ⟨c, q, .refl⟩
  | step s p ih =>
    obtain ⟨d, hbd, hcd⟩ := strip hbk ha s q
    obtain ⟨e, hbe, hde⟩ := ih (epar_canonical hbk s ha) hbd
    exact ⟨e, hbe, .step hcd hde⟩



theorem epars_trans (h : EPars bk a b) (g : EPars bk b c) : EPars bk a c := by
  induction h with
  | refl => exact g
  | step s _ ih => exact .step s (ih g)



theorem ejoin_trans (hbk : EBook.Canonical bk) (hb : Canonical b)
    (h : EJoin bk a b) (g : EJoin bk b c) : EJoin bk a c := by
  obtain ⟨u, hau, hbu⟩ := h
  obtain ⟨v, hbv, hcv⟩ := g
  obtain ⟨w, huw, hvw⟩ := confluent hbk hb hbu hbv
  exact ⟨w, epars_trans hau huw, epars_trans hcv hvw⟩



end GlobalDiamond

end

-- Source section: EquationBridge
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec



namespace EquationBridge



theorem epars_map (F : Term → Term)
    (hf : ∀ {x y}, EPar bk x y → EPar bk (F x) (F y))
    (h : EPars bk a b) : EPars bk (F a) (F b) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (hf h) ih



theorem ejoin_map (F : Term → Term)
    (hf : ∀ {x y}, EPar bk x y → EPar bk (F x) (F y))
    (h : EJoin bk a b) : EJoin bk (F a) (F b) := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨F c, epars_map F hf ha, epars_map F hf hb⟩



theorem ejoin_map2 (hbk : EBook.Canonical bk) (F : Term → Term → Term)
    (hf : ∀ {a b c d}, EPar bk a b → EPar bk c d → EPar bk (F a c) (F b d))
    (hc : Canonical c) (hb : Canonical b) (hm : Canonical (F b c))
    (h : EJoin bk a b) (g : EJoin bk c d) : EJoin bk (F a c) (F b d) := by
  exact GlobalDiamond.ejoin_trans hbk hm
    (ejoin_map (fun a => F a c) (fun h => hf h (epar_refl hc)) h)
    (ejoin_map (fun c => F b c) (fun h => hf (epar_refl hb) h) g)



theorem ejoin_map3 (hbk : EBook.Canonical bk) (F : Term → Term → Term → Term)
    (hf : ∀ {a b c d e f}, EPar bk a b → EPar bk c d → EPar bk e f →
      EPar bk (F a c e) (F b d f))
    (hb : Canonical b) (hc : Canonical c) (hd : Canonical d) (he : Canonical e)
    (hm : Canonical (F b c e)) (hn : Canonical (F b d e))
    (h : EJoin bk a b) (g : EJoin bk c d) (i : EJoin bk e f) :
    EJoin bk (F a c e) (F b d f) := by
  apply GlobalDiamond.ejoin_trans hbk hm
    (ejoin_map (fun a => F a c e)
      (fun h => hf h (epar_refl hc) (epar_refl he)) h)
  exact GlobalDiamond.ejoin_trans hbk hn
    (ejoin_map (fun c => F b c e)
      (fun h => hf (epar_refl hb) h (epar_refl he)) g)
    (ejoin_map (fun e => F b d e)
      (fun h => hf (epar_refl hb) (epar_refl hd) h) i)



-- Every equation has a common reduct in the erased comparison relation.
theorem equation_join (h : Equation bk a b) :
    EJoin (eraseBook bk) (erase a) (erase b) := by
  induction h <;> (try simp only [erase])
  case old h => exact ⟨_, .step (erase_par h) .refl, .refl⟩
  case refl => exact ⟨_, .refl, .refl⟩
  case symm h ih => obtain ⟨c, ha, hb⟩ := ih; exact ⟨c, hb, ha⟩
  case trans h g ih ih' =>
    exact GlobalDiamond.ejoin_trans eraseBook_canonical (erase_idem _) ih ih'
  case typ h ih => exact ejoin_map Typ EPar.typ ih
  case lam h ih => exact ejoin_map (Lam Q1) EPar.lam ih
  case prj h ih => exact ejoin_map Prj EPar.prj ih
  case eta =>
    simp only [erase_ren]
    exact eta_join (erase_idem _)
  case ann h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical Ann EPar.ann (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case lett h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (Let _) EPar.lett (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case min h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical Term.Min EPar.min (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case all h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (All _) EPar.all (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case app h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (App Q1) EPar.app (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case sig h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (Sig _) EPar.sig (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case tup h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (Tup _) EPar.tup (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case mat h g ih ih' =>
    exact ejoin_map2 eraseBook_canonical (Mat _) EPar.mat (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem]) ih ih'
  case eql h g i ih ih' ih'' =>
    exact ejoin_map3 eraseBook_canonical Eql EPar.eql (erase_idem _) (erase_idem _) (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem])
      (by simp [Canonical, erase, erase_idem]) ih ih' ih''
  case rwt h g i ih ih' ih'' =>
    exact ejoin_map3 eraseBook_canonical Rwt EPar.rwt (erase_idem _) (erase_idem _) (erase_idem _) (erase_idem _)
      (by simp [Canonical, erase, erase_idem])
      (by simp [Canonical, erase, erase_idem]) ih ih' ih''



-- This retains the model-book and closed-body assumptions in Sees.
theorem diagnostic_join (hb : Sees ck bk)
    (h : (diagnosticCompare ck cl n a b).1 = true) :
    EJoin (eraseBook bk) (erase a) (erase b) :=
  equation_join (diagnostic_sound hb h)



-- The result remains a common reduct after every raw substitution.
theorem equation_substitution_join (h : Equation bk a b) (σ : Subst) :
    EJoin (eraseBook bk) (erase (sub σ a)) (erase (sub σ b)) := by
  simp only [erase_sub]
  exact ejoin_sub (equation_join h) (fun _ => erase_idem _)



-- This preserves the proved equality, not the algorithm's acceptance result.
theorem diagnostic_substitution_join (hb : Sees ck bk)
    (h : (diagnosticCompare ck cl n a b).1 = true) (σ : Subst) :
    EJoin (eraseBook bk) (erase (sub σ a)) (erase (sub σ b)) :=
  equation_substitution_join (diagnostic_sound hb h) σ



end EquationBridge

end

-- Source section: Boundary
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge



namespace QuantityBoundary



theorem epars_lab (h : EPars bk s t) : s = Lab k → t = Lab k := by
  induction h with
  | refl => exact id
  | step h _ ih =>
    intro e
    subst e
    cases h
    exact ih rfl



theorem epars_typ (h : EPars bk s t) : s = Typ q →
    ∃ p, t = Typ p ∧ EPars bk q p := by
  induction h generalizing q with
  | refl => intro e; subst e; exact ⟨_, rfl, .refl⟩
  | step h _ ih =>
    intro e; subst e
    cases h with | typ hq =>
      obtain ⟨p, rfl, hp⟩ := ih rfl
      exact ⟨p, rfl, .step hq hp⟩



end QuantityBoundary

end

-- Source section: ExecutableOrder
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond



namespace ExecutableOrder



def Join (bk : Book) (a b : Term) : Prop :=
  EJoin (eraseBook bk) (erase a) (erase b)



theorem join_refl : Join bk a a := ⟨_, .refl, .refl⟩



theorem join_symm (h : Join bk a b) : Join bk b a := by
  obtain ⟨c, ha, hb⟩ := h
  exact ⟨c, hb, ha⟩



theorem join_trans (h : Join bk a b) (g : Join bk b c) : Join bk a c :=
  ejoin_trans eraseBook_canonical (erase_idem _) h g



theorem join_sub (h : Join bk a b) : Join bk (sub σ a) (sub σ b) := by
  unfold Join at *
  simp only [erase_sub]
  exact ejoin_sub h (fun _ => erase_idem _)



theorem join_old (h : Conv bk a b) : Join bk a b := erase_conv h



theorem ejoin_lab_steps (h : EJoin bk a (Lab k)) : EPars bk a (Lab k) := by
  obtain ⟨c, ha, hb⟩ := h
  rw [epars_lab hb rfl] at ha
  exact ha



theorem join_lab_inj (h : Join bk (Lab j) (Lab k)) : k = j :=
  Term.Lab.inj (epars_lab (ejoin_lab_steps h) rfl)



theorem emin_steps (h : EPars bk t c) : ∀ {a b}, t = Min a b → c = Lab "Q2" →
    EPars bk a (Lab "Q2") ∧ EPars bk b (Lab "Q2") := by
  induction h with
  | refl => rintro _ _ rfl ⟨⟩
  | step s hp ih =>
    rintro _ _ rfl rfl
    cases s <;> try (rename_i a' b' _ _; rcases qmin_view a' b' with
      e | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl | rfl, e⟩ | ⟨rfl, rfl, e⟩ <;> rw [e] at hp ih)
    all_goals first
      | exact ⟨.step ‹_› (ih rfl rfl).1, .step ‹_› (ih rfl rfl).2⟩
      | exact ⟨.step ‹_› .refl, .step ‹_› hp⟩
      | exact ⟨.step ‹_› hp, .step ‹_› .refl⟩
      | exact absurd (Term.Lab.inj (epars_lab hp rfl)) (by decide)



theorem join_min2 : Join bk (Min a b) (Lab "Q2") ↔
    Join bk a (Lab "Q2") ∧ Join bk b (Lab "Q2") := by
  constructor
  · intro h
    have ⟨ha, hb⟩ := emin_steps (ejoin_lab_steps h) rfl rfl
    exact ⟨⟨_, ha, .refl⟩, ⟨_, hb, .refl⟩⟩
  · intro ⟨ha, hb⟩
    have hm : Join bk (Min a b) (Min (Lab "Q2") (Lab "Q2")) :=
      ejoin_map2 eraseBook_canonical Min EPar.min (erase_idem _) rfl
        (by simp [Canonical, erase, erase_idem]) ha hb
    exact join_trans hm (join_old (pconv (.meet .lab .lab)))



-- This is the diagnostic qge definition with explicit comparator names.
def diagnosticQge (ck : Book) (cl : Bool) : Nat → Term → Term → Bool × Nat
  | 0, _, _ => (false, 0)
  | n + 1, g, h =>
    let (g, m) := Term.wnf ck cl n g []
    let (h, m) := Term.wnf ck cl (min m n) h []
    match g, h with
    | Term.Min a b, h =>
      let r := diagnosticQge ck cl (min m n) a h
      if r.1 then diagnosticQge ck cl (min r.2 n) b h else r
    | g, Term.Min a b =>
      let r := diagnosticQge ck cl (min m n) g a
      if r.1 then r else diagnosticQge ck cl (min r.2 n) g b
    | g, h =>
      if g == Lab "Q2" || h == Lab "Q0" || h == Lab "Q1" then (true, m)
      else diagnosticCompare ck cl (min m n) g h



theorem diagnostic_qge_sound (hb : Sees ck bk) :
    (diagnosticQge ck cl n g h).1 = true →
    ∀ σ, Join bk (sub σ h) (Lab "Q2") → Join bk (sub σ g) (Lab "Q2") := by
  induction n using Nat.strongRecOn generalizing g h
  rename_i n ih
  unfold diagnosticQge
  split
  · nofun
  rename_i n
  have L {a} : min a n < n + 1 := by omega
  split
  rename_i G _ eg
  split
  rename_i H _ eh
  have E {m x X k σ} (e : wnf ck cl m x [] = (X, k)) :=
    join_old (conv_sub (σ := σ) ⟨_, wnf_nil hb e, .refl⟩)
  split <;> intro hq σ p <;> replace p := join_trans (join_symm (E eh)) p <;>
    refine join_trans (E eg) ?_ <;> (try dsimp only at hq) <;> split at hq
  · rename_i ha
    exact join_min2.2 ⟨ih _ L ha σ p, ih _ L hq σ p⟩
  · simp_all
  · rename_i ha
    exact ih _ L ha σ (join_min2.1 p).1
  · exact ih _ L hq σ (join_min2.1 p).2
  · rename_i e
    simp only [Bool.or_eq_true, beq_iff_eq] at e
    rcases e with ((rfl | rfl) | rfl) <;> first
      | exact join_refl
      | exact absurd (join_lab_inj p) (by decide)
  · exact join_trans (join_sub (diagnostic_join hb hq)) p



-- Each equality position uses the same enlarged comparison relation.
inductive NewFits (bk : Book) : Term → Term → Prop
  | conv : Join bk U T → NewFits bk U T
  | typ : (∀ σ, Join bk (sub σ h) (Lab "Q2") → Join bk (sub σ g) (Lab "Q2")) →
      NewFits bk (Typ g) (Typ h)
  | enu : ks ⊆ js → NewFits bk (Enu ks) (Enu js)
  | all : NewFits bk C A → NewFits bk B D → NewFits bk (All q A B) (All q C D)
  | trans : NewFits bk U M → NewFits bk M T → NewFits bk U T



theorem new_fits_sub (h : NewFits bk A B) : NewFits bk (sub σ A) (sub σ B) := by
  induction h generalizing σ
  case typ s => exact .typ fun τ => by simpa only [sub_sub] using s _
  all_goals solve_by_elim [NewFits.conv, NewFits.enu, NewFits.all, NewFits.trans, join_sub]



def diagnosticFits (ck : Book) (cl : Bool) : Nat → Term → Term → Bool × Nat
  | 0, _, _ => (false, 0)
  | n + 1, U, T =>
    let (U, m) := Term.wnf ck cl n U []
    let (T, m) := Term.wnf ck cl (min m n) T []
    match U, T with
    | Typ g, Typ h => diagnosticQge ck cl (min m n) g h
    | Enu ks, Enu js => (ks.all js.contains, m)
    | All q A B, All p C D =>
      let r := if q == p then diagnosticFits ck cl (min m n) C A else (false, m)
      if r.1 then diagnosticFits ck false (min r.2 n) B D else r
    | U, T => diagnosticCompare ck cl (min m n) U T



-- Actual accepted fits need no embedding of all old semantic Fits proofs.
theorem diagnostic_fits_sound (hb : Sees ck bk)
    (h : (diagnosticFits ck cl n U T).1 = true) : NewFits bk U T := by
  induction n using Nat.strongRecOn generalizing cl U T
  rename_i n ih
  unfold diagnosticFits at h
  split at h
  · simp at h
  rename_i n
  have L {a} : min a n < n + 1 := by omega
  split at h
  rename_i e1
  split at h
  rename_i e2
  refine .trans (.conv (join_old ⟨_, wnf_nil hb e1, .refl⟩))
    (.trans ?_ (.conv (join_old ⟨_, .refl, wnf_nil hb e2⟩)))
  split at h
  · exact .typ (diagnostic_qge_sound hb h)
  · exact .enu fun _ m => by simpa using List.all_eq_true.1 h _ m
  · dsimp only at h
    split at h
    · rename_i e
      cases beq_iff_eq.1 e
      split at h
      · exact .all (ih _ L ‹_›) (ih _ L h)
      · simp_all
    · simp at h
  · exact .conv (diagnostic_join hb h)



end ExecutableOrder

end

-- Source section: RevisedTyping
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open ExecutableOrder



namespace Revised



inductive Typed (bk : Book) : List Term → Term → Term → Prop
  | var  : Γ[i]? = some A → Typed bk Γ (Var i) (Term.ren (· + (i + 1)) A)
  -- any instance of a def's type: a checked def's type is closed
  | ref  : Book.get bk k = some d → Typed bk Γ (Ref k) (Term.sub σ d.T)
  | ann  : Typed bk Γ T T1 → Typed bk Γ x T → Typed bk Γ (Ann x T) T
  | lett : Typed bk Γ v V → (q = Q2 → Typed bk Γ V T2) →
           Typed bk Γ (Term.inst f v) T → Typed bk Γ (Let q v f) T
  | typ  : Typed bk Γ q (Enu QS) → Typed bk Γ (Typ q) T1
  | min  : Typed bk Γ a (Enu QS) → Typed bk Γ b (Enu QS) → Typed bk Γ (Min a b) (Enu QS)
  | all  : Typed bk Γ A (Term.kindof q T1) → Typed bk (A :: Γ) B T1 →
           Typed bk Γ (All q A B) T1
  | lam  : p.live = q.live → (q = Q2 → Typed bk Γ A T2) →
           Typed bk (A :: Γ) f B → Typed bk Γ (Lam q f) (All p A B)
  | app  : Typed bk Γ f (All q A B) → Typed bk Γ x A →
           Typed bk Γ (App q f x) (Term.inst B x)
  | sig  : Typed bk Γ A (Term.kindof q (Typ g)) → Typed bk (A :: Γ) B (Typ (Term.ren Nat.succ g)) →
           Typed bk Γ (Sig q A B) (Typ g)
  | tup  : Typed bk Γ a A → Typed bk Γ b (Term.inst B a) →
           Typed bk Γ (Tup q a b) (Sig q A B)
  | prj  : q.live = true →
           Typed bk Γ h
             (All (Quan.fld r q) A (All q B (Term.sub (Subst.tup r) P))) →
           Typed bk Γ (Prj h) (All q (Sig r A B) P)
  | enu  : Typed bk Γ (Enu ks) T2
  | lab  : k ∈ ks → Typed bk Γ (Lab k) (Enu ks)
  | mat  : q.live = true → k ∈ ks → Typed bk Γ h (Term.inst P (Lab k)) →
           Typed bk Γ m (All q (Enu (ks.erase k)) P) →
           Typed bk Γ (Mat k h m) (All q (Enu ks) P)
  | efq  : q.live = true → Typed bk Γ Efq (All q (Enu []) P)
  | eql  : Typed bk Γ T T1 → Typed bk Γ a T → Typed bk Γ b T →
           Typed bk Γ (Eql a b T) T2
  | rfl  : Join bk a b → Typed bk Γ Rfl (Eql a b T)
  | rwt  : Typed bk Γ e (Eql a b A) →
           Typed bk (Eql (Term.ren Nat.succ a) (Var 0) (Term.ren Nat.succ A) :: A :: Γ) P T1 →
           NewFits bk (Term.inst (Term.inst P (Term.ren Nat.succ e)) b) T →
           Typed bk Γ f (Term.inst (Term.inst P Rfl) a) → Typed bk Γ (Rwt e P f) T
  | conv : Typed bk Γ t U → NewFits bk U T → Typed bk Γ t T



def SubstOk (bk : Book) (Δ : List Term) (σ : Subst) (Γ : List Term) : Prop :=
  ∀ i A, Γ[i]? = some A →
    Typed bk Δ (σ i) (sub σ (ren (· + (i + 1)) A))



-- one induction for renamings and substitutions: K types σ's
-- variables and lifts under a binder
theorem typed_gen (K : List Term → Subst → List Term → Prop)
    (hv : ∀ {Δ σ Γ}, K Δ σ Γ → SubstOk bk Δ σ Γ)
    (hu : ∀ {Δ σ Γ} A, K Δ σ Γ → K (sub σ A :: Δ) (Subst.up σ) (A :: Γ))
    (h : Typed bk Γ t T) : K Δ σ Γ → Typed bk Δ (sub σ t) (sub σ T) := by
  induction h generalizing Δ σ <;> intro k <;> (try simp only [sub, inst_sub, tup_sub, kindof_sub] at *)
  case var h => exact hv k _ _ h
  case ref h => rw [sub_sub]; exact .ref h
  case rwt h _ ih1 ih2 ih3 =>
    exact .rwt (ih1 k) (by simpa only [sub, Subst.up, sub_succ] using ih2 (hu _ (hu _ k)))
      (by simpa only [inst_sub, sub_succ] using new_fits_sub h) (ih3 k)
  case sig => rename_i ih2 ih1; exact .sig (ih1 k) (by simpa only [sub_succ] using ih2 (hu _ k))
  all_goals constructor <;> solve_by_elim [join_sub, new_fits_sub]



-- SubstOk lifts under a binder: typing survives renaming each variable
-- to one of its type, so σ's types weaken
theorem substok_up (k : SubstOk bk Δ σ Γ) :
    SubstOk bk (sub σ A :: Δ) (Subst.up σ) (A :: Γ) := by
  have W {Γ t T X} (h : Typed bk Γ t T) : Typed bk (X :: Γ) (ren Nat.succ t) (ren Nat.succ T) := by
    simp only [ren_as_sub]
    refine typed_gen (fun Δ σ Γ => ∀ i A, Γ[i]? = some A → ∃ j B, σ i = Var j ∧ Δ[j]? = some B ∧
      ren (· + (j + 1)) B = sub σ (ren (· + (i + 1)) A)) ?_ ?_ h ?_
    · exact fun k i A hA => have ⟨_, _, e, hB, e'⟩ := k i A hA; e ▸ e' ▸ .var hB
    · intro _ _ _ _ k i B hB; cases i
      · cases hB; exact ⟨0, _, rfl, rfl, sub_succ.symm⟩
      · have ⟨j, B', e, hB', e'⟩ := k _ B hB
        refine ⟨j + 1, B', by simp [Subst.up, e, ren], hB', ?_⟩
        have := congrArg (ren Nat.succ) e'; simp only [ren_ren, ← sub_succ] at this ⊢; exact this
    · exact fun i B hB => ⟨i + 1, B, rfl, hB, by rw [← ren_as_sub, ren_ren]; rfl⟩
  intro i B hB; rw [sub_ren]; cases i
  · cases hB; exact ren_sub _ ▸ Typed.var rfl
  · exact (sub_ren _ ▸ ren_sub _ ▸ W (k _ B hB) :)



theorem typed_sub : Typed bk Γ t T → SubstOk bk Δ σ Γ →
    Typed bk Δ (sub σ t) (sub σ T) :=
  typed_gen (SubstOk bk) id fun _ => substok_up



theorem typed_inst : Typed bk (A :: Γ) f B → Typed bk Γ v A →
    Typed bk Γ (inst f v) (inst B v) := fun h hv => typed_sub h fun i A' hA => by
  rw [sub_ren]; cases i; (cases hA; exact (sub_var A).symm ▸ hv); exact ren_as_sub _ ▸ Typed.var hA




def WellTyped (bk : Book) : Prop :=
  ∀ k d, Book.get bk k = some d →
    Typed bk [] d.T T1 ∧ Typed bk [] d.v d.T ∧ Term.Closed d.v



end Revised

end

-- Source section: NewFitsInversion
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder



namespace NewFitsInversion



theorem join_rigid (h : Join bk a b) (ha : Rigid a) (hb : Rigid b) :
    a.former = b.former := by
  have he := ejoin_rigid h
    (by simpa only [Rigid, erase_keeps_former] using ha)
    (by simpa only [Rigid, erase_keeps_former] using hb)
  simpa only [erase_keeps_former] using he



theorem join_all (h : Join bk (All p A B) (All q C D)) :
    p = q ∧ Join bk A C ∧ Join bk B D := ejoin_all h



theorem epars_sig_parts (h : EPars bk s t) : s = Sig q A B →
    ∃ C D, t = Sig q C D ∧ EPars bk A C ∧ EPars bk B D := by
  induction h generalizing q A B with
  | refl => intro e; subst e; exact ⟨_, _, rfl, .refl, .refl⟩
  | step h _ ih =>
    intro e; subst e
    cases h with | sig hA hB =>
      obtain ⟨C, D, rfl, hC, hD⟩ := ih rfl
      exact ⟨_, _, rfl, .step hA hC, .step hB hD⟩



theorem join_sig (h : Join bk (Sig p A B) (Sig q C D)) :
    p = q ∧ Join bk A C ∧ Join bk B D := by
  obtain ⟨t, h₁, h₂⟩ := h
  obtain ⟨A', B', rfl, hA, hB⟩ := epars_sig_parts h₁ rfl
  obtain ⟨C', D', e, hC, hD⟩ := epars_sig_parts h₂ rfl
  cases e
  exact ⟨rfl, ⟨_, hA, hC⟩, ⟨_, hB, hD⟩⟩



theorem epars_eql_parts (h : EPars bk s t) : s = Eql a b T →
    ∃ c d U, t = Eql c d U ∧ EPars bk a c ∧ EPars bk b d ∧ EPars bk T U := by
  induction h generalizing a b T with
  | refl => intro e; subst e; exact ⟨_, _, _, rfl, .refl, .refl, .refl⟩
  | step h _ ih =>
    intro e; subst e
    cases h with | eql ha hb hT =>
      obtain ⟨c, d, U, rfl, hc, hd, hU⟩ := ih rfl
      exact ⟨_, _, _, rfl, .step ha hc, .step hb hd, .step hT hU⟩



theorem join_eql (h : Join bk (Eql a b T) (Eql c d U)) :
    Join bk a c ∧ Join bk b d ∧ Join bk T U := by
  obtain ⟨t, h₁, h₂⟩ := h
  obtain ⟨a', b', T', rfl, ha, hb, hT⟩ := epars_eql_parts h₁ rfl
  obtain ⟨c', d', U', e, hc, hd, hU⟩ := epars_eql_parts h₂ rfl
  cases e
  exact ⟨⟨_, ha, hc⟩, ⟨_, hb, hd⟩, ⟨_, hT, hU⟩⟩



theorem epars_enu (h : EPars bk s t) : s = Enu ks → t = Enu ks := by
  induction h with
  | refl => exact id
  | step h _ ih => intro e; subst e; cases h; exact ih rfl



theorem join_enu_inj (h : Join bk (Enu ks) (Enu js)) : ks = js := by
  obtain ⟨_, ha, hb⟩ := h
  exact Term.Enu.inj ((epars_enu ha rfl).symm.trans (epars_enu hb rfl))



theorem join_typ : Join bk (Typ a) (Typ b) ↔ Join bk a b := by
  constructor
  · rintro ⟨_, ha, hb⟩
    obtain ⟨a', rfl, hA⟩ := epars_typ ha rfl
    obtain ⟨b', e, hB⟩ := epars_typ hb rfl
    cases e
    exact ⟨_, hA, hB⟩
  · exact ejoin_map Typ EPar.typ



inductive NewFitsAt (bk : Book) : Term → Term → Prop
  | refl : NewFitsAt bk X X
  | typ : (∀ σ, Join bk (sub σ h) (Lab "Q2") → Join bk (sub σ g) (Lab "Q2")) →
      NewFitsAt bk (Typ g) (Typ h)
  | enu : ks ⊆ js → NewFitsAt bk (Enu ks) (Enu js)
  | all : NewFits bk C A → NewFits bk B D → NewFitsAt bk (All q A B) (All q C D)



theorem at_former (a : NewFitsAt bk X Y) : X.former = Y.former := by cases a <;> rfl



theorem at_trans (h₁ : NewFitsAt bk X Y) (h₂ : NewFitsAt bk Y Z) : NewFitsAt bk X Z := by
  cases h₁ <;> cases h₂ <;> first
    | assumption
    | constructor <;> solve_by_elim [NewFits.trans, List.Subset.trans]



-- Eta can change a lambda head. This inversion only needs rigid type heads.
theorem new_fits_at (h : NewFits bk U T) :
    (∀ X, Join bk T X → Rigid X → ∃ Y, Join bk U Y ∧ NewFitsAt bk Y X) ∧
    (∀ X, Join bk U X → Rigid X → ∃ Y, Join bk T Y ∧ NewFitsAt bk X Y) := by
  induction h <;> refine ⟨fun X c n => ?_, fun X c n => ?_⟩
  case conv.refine_1 h => exact ⟨X, join_trans h c, .refl⟩
  case conv.refine_2 h => exact ⟨X, join_trans (join_symm h) c, .refl⟩
  case trans.refine_1 ih₁ ih₂ =>
    have ⟨Y, c, a⟩ := ih₂.1 X c n
    have ⟨Z, c, a'⟩ := ih₁.1 Y c (by simpa only [Rigid, at_former a] using n)
    exact ⟨Z, c, at_trans a' a⟩
  case trans.refine_2 ih₁ ih₂ =>
    have ⟨Y, c, a⟩ := ih₁.2 X c n
    have ⟨Z, c, a'⟩ := ih₂.2 Y c (by simpa only [Rigid, ← at_former a] using n)
    exact ⟨Z, c, at_trans a a'⟩
  all_goals have e := join_rigid c (by simp [Rigid, former]) n
  all_goals cases X <;> simp [former] at e
  case typ.refine_1.Typ s _ | typ.refine_2.Typ s _ =>
    have e := join_typ.1 c
    refine ⟨_, join_refl, .typ fun σ p => ?_⟩
    first
      | exact s σ (join_trans (join_sub e) p)
      | exact join_trans (join_sub (join_symm e)) (s σ p)
  case enu.refine_1.Enu | enu.refine_2.Enu =>
    cases join_enu_inj c
    exact ⟨_, join_refl, .enu ‹_›⟩
  case all.refine_1.All | all.refine_2.All =>
    obtain ⟨rfl, h₁, h₂⟩ := join_all c
    refine ⟨_, join_refl, .all ?_ ?_⟩ <;> first
      | exact .trans (.conv (join_symm ‹_›)) ‹_›
      | exact .trans ‹_› (.conv ‹_›)



theorem new_fits_all (h : NewFits bk (All p A B) (All q C D)) :
    p = q ∧ NewFits bk C A ∧ NewFits bk B D := by
  have ⟨_, c, a⟩ := (new_fits_at h).1 _ join_refl (by simp [Rigid, former])
  cases a with
  | refl =>
    have ⟨e, hA, hB⟩ := join_all c
    exact ⟨e, .conv (join_symm hA), .conv hB⟩
  | all f g =>
    obtain ⟨rfl, hA, hB⟩ := join_all c
    exact ⟨rfl, .trans f (.conv (join_symm hA)), .trans (.conv hB) g⟩



theorem new_fits_conv (h : NewFits bk U T) (c : Join bk T X)
    (n : X.former ∈ [3, 5]) : Join bk U X := by
  have ⟨_, c', a⟩ := (new_fits_at h).1 X c (by simp_all [Rigid]; omega)
  cases a <;> simp_all [former]



theorem new_fits2 (f : NewFits bk U T2) : Join bk U T2 := by
  have ⟨_, c, a⟩ := (new_fits_at f).1 _ join_refl (by simp [Rigid, former])
  cases a
  · exact c
  · rename_i s
    have he := s Var (by rw [sub_var]; exact join_refl)
    rw [sub_var] at he
    exact join_trans c (join_typ.2 he)



end NewFitsInversion

end

-- Source section: RevisedPreservation
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion BetaEtaPeak



namespace Revised



 theorem old_step_join (h : Par bk a b) : Join bk a b := join_old (pconv h)



 theorem join_inst_right (h : Join bk a b) : Join bk (inst f a) (inst f b) := by
  unfold Join at *
  simp only [erase_inst]
  exact ejoin_map (inst (erase f)) (fun h => epar_inst (epar_refl (erase_idem _)) h) h



-- what the syntax-directed rule of t says about t's type U
def Gen (bk : Book) (Γ : List Term) : Term → Term → Prop
  | Lam q f, U => ∃ p A B, U = All p A B ∧ p.live = q.live ∧
    (q = Q2 → Typed bk Γ A T2) ∧ Typed bk (A :: Γ) f B
  | App q f x, U => ∃ A B, U = inst B x ∧ Typed bk Γ f (All q A B) ∧ Typed bk Γ x A
  | Tup q a b, U => ∃ A B, U = Sig q A B ∧ Typed bk Γ a A ∧ Typed bk Γ b (inst B a)
  | Prj h, U => ∃ q r A B P, U = All q (Sig r A B) P ∧ q.live ∧
    Typed bk Γ h (All (Quan.fld r q) A (All q B (sub (Subst.tup r) P)))
  | Mat k h m, U => ∃ q ks P, U = All q (Enu ks) P ∧ q.live ∧
    Typed bk Γ h (inst P (Lab k)) ∧ Typed bk Γ m (All q (Enu (ks.erase k)) P)
  | Efq, U => ∃ q P, U = All q (Enu []) P ∧ q.live
  | Lab k, U => ∃ ks, U = Enu ks ∧ k ∈ ks
  | Rfl, U => ∃ a b T, U = Eql a b T ∧ Join bk a b
  | Sig q A B, U => ∃ g, U = Typ g ∧ Typed bk Γ A (kindof q U) ∧
    Typed bk (A :: Γ) B (Typ (ren Nat.succ g))
  | Typ _, U | All .., U => U = T1
  | _, _ => True



theorem gen (h : Typed bk Γ t T) :
    ∃ U, Gen bk Γ t U ∧ NewFits bk U T ∧ (t.former ≠ 0 → U.former = t.tform) := by
  induction h
  all_goals first
    | refine ⟨_, ?_, .conv join_refl, by simp [former, tform]⟩; simp only [Gen]
      repeat' first | assumption | refine ⟨_, ?_⟩ | constructor
      done
    | rename_i ih; exact ih.imp fun _ ⟨g, f, e⟩ => ⟨g, .trans f ‹_›, e⟩



theorem ctx_par (h : Typed bk (A :: Γ) t T) (p : Par bk A A') : Typed bk (A' :: Γ) t T := by
  refine sub_var t ▸ sub_var T ▸ typed_sub h fun i B e => ?_
  rw [sub_var]; cases i; cases e; exact .conv (.var rfl) (.conv (join_symm (old_step_join (par_ren p)))); exact .var e



theorem lab_in (h : Typed bk Γ (Lab j) A) (f : NewFits bk A (Enu ks)) : j ∈ ks := by
  obtain ⟨_, ⟨js, rfl, hj⟩, hU, _⟩ := gen h
  have ⟨_, c, a⟩ := (new_fits_at (.trans hU f)).1 _ join_refl (by simp [Rigid, former])
  cases a <;> cases join_enu_inj c; exact hj; rename_i s; exact s hj



theorem split_inst : inst (sub (Subst.up (Subst.one a)) (sub (Subst.tup r) P)) b =
    inst P (Tup r a b) := by
  simp only [inst, sub_sub]; congr 1; funext i; cases i; exact congrArg (Tup r · b) ((sub_ren _).trans (sub_var a)); rfl



-- induction on Typed, inverting the redex by gen
theorem sr (wt : Revised.WellTyped bk) (h : Revised.Typed bk Γ t T)
    (hp : Par bk t u) : Revised.Typed bk Γ u T := by
  have pi := fun {f v v'} (p : Par bk v v') => join_symm (old_step_join (par_inst (par_refl (t := f)) p))
  induction h generalizing u
  case ref e => cases hp with
    | ref => exact .ref e
    | delta e' hc => cases e.symm.trans e'; rw [← hc]; exact typed_sub (wt _ _ e).2.1 nofun
  case ann _ _ ihT ihx => cases hp with
    | ann px pT => exact .conv (.ann (ihT pT) (.conv (ihx px) (.conv (old_step_join pT)))) (.conv (join_symm (old_step_join pT)))
    | unann px => exact ihx px
  case lett _ hq _ ihv _ ihf => cases hp with
    | lett pv pf => exact .lett (ihv pv) hq (ihf (par_inst pf pv))
    | unlet pv pf => exact ihf (par_inst pf pv)
  case rwt he _ hF _ ihe ihP ihf => cases hp with
    | rwt pe pP pf =>
      exact .rwt (ihe pe) (ihP pP) (.trans (.conv (join_symm (old_step_join (par_inst (par_inst pP (par_ren pe)) par_refl)))) hF)
        (.conv (ihf pf) (.conv (old_step_join (par_inst (par_inst pP .rfl) par_refl))))
    | cast pf =>
      obtain ⟨_, ⟨a, b, _, rfl, hc⟩, hU, _⟩ := gen he
      have ⟨hA, hB, _⟩ := join_eql (new_fits_conv hU join_refl (by simp [former]))
      have hab := join_trans (join_symm hA) (join_trans hc hB)
      exact .conv (ihf pf) (.trans (.conv (join_inst_right hab)) hF)
  case conv _ hf ih => exact .conv (ih hp) hf
  case min _ _ iha ihb =>
    cases hp with
    | min pa pb => exact .min (iha pa) (ihb pb)
    | meet pa pb =>
      have ha := iha pa; have hb := ihb pb
      rcases qmin_view _ _ with e | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> first
        | exact .min ha hb | assumption | exact .lab (by decide)
  -- a λ+ stepped to a λ keeps its liveness and needs no Data
  case lam q _ _ _ _ _ hl hq _ _ ihf => cases hp with
    | lam pf e => cases q <;> rcases e with rfl | rfl <;> exact .lam hl (by first | exact hq | nofun) (ihf pf)
  case app _ hx ihf ihx => cases hp with
    | app pf px => exact .conv (.app (ihf pf) (ihx px)) (.conv (pi px))
    | beta pf px =>
      obtain ⟨_, ⟨_, _, _, rfl, _, _, hb⟩, hF, _⟩ := gen (ihf (.lam pf (.inl rfl)))
      have ⟨_, hA, hB⟩ := new_fits_all hF
      exact .conv (typed_inst hb (.conv (ihx px) hA)) (.trans (new_fits_sub hB) (.conv (pi px)))
    | split ph pa pb =>
      obtain ⟨_, ⟨_, _, _, _, _, rfl, _, hh⟩, hU, _⟩ := gen (ihf (.prj ph))
      obtain ⟨rfl, hS, hP⟩ := new_fits_all hU
      obtain ⟨_, ⟨_, _, rfl, ha, hb⟩, hT, _⟩ := gen (ihx (.tup pa pb))
      obtain ⟨rfl, hA, hB⟩ := join_sig (new_fits_conv (.trans hT hS) join_refl (by simp [former]))
      exact .conv (split_inst ▸ Typed.app (Typed.app hh (.conv ha (.conv hA))) (.conv hb (.conv (join_sub hB))) :)
        (.trans (new_fits_sub hP) (.conv (pi (.tup pa pb))))
    | hit ph =>
      obtain ⟨_, ⟨_, _, _, rfl, _, hh, _⟩, hU, _⟩ := gen (ihf (.mat ph par_refl))
      exact .conv hh (new_fits_sub (new_fits_all hU).2.2)
    | miss hjk pm =>
      obtain ⟨_, ⟨_, ks, _, rfl, _, _, hm⟩, hU, _⟩ := gen (ihf (.mat par_refl pm))
      obtain ⟨rfl, hE, hP⟩ := new_fits_all hU
      exact .conv (.app hm (.lab ((List.mem_erase_of_ne hjk).2 (lab_in hx hE)))) (new_fits_sub hP)
  all_goals cases hp; constructor <;> first
    | assumption | (apply_assumption <;> assumption) | exact ctx_par (by apply_assumption <;> assumption) ‹_›
    | exact .conv (by solve_by_elim) (.conv (by first | exact old_step_join ‹_› | exact join_symm (pi ‹_›)))



theorem pars_sr : Revised.WellTyped bk → Typed bk Γ t T → Pars bk t u → Typed bk Γ u T := by
  intro wt h p; induction p with | refl => exact h | step s _ ih => exact ih (sr wt h s)




theorem eval_preservation (wt : Revised.WellTyped bk) (h : Revised.Typed bk Γ t T)
    (he : Eval bk t u) : Revised.Typed bk Γ u T :=
  pars_sr wt h (eval_pars (fun k d hk => (wt k d hk).2.2) he)



theorem value_fits (wt : Revised.WellTyped bk) (v : Value bk t) (h : Typed bk [] t T) :
    ∃ U, NewFits bk U T ∧ U.former = t.tform := by
  cases v
  case call _ _ _ hk _ w =>
    obtain ⟨v, p, h | ⟨-, tk⟩⟩ := walk_pars' w
    cases h
    rw [env_nil, sub_var] at p
    have ⟨U, _, f, e⟩ := gen (pars_sr wt h (.step (par_spine (.delta hk (wt _ _ hk).2.2)) p))
    refine ⟨U, f, .trans ?_ tform_call.symm⟩
    cases v <;> simp [takes] at tk <;> exact e nofun
  all_goals have ⟨U, _, f, e⟩ := gen h; exact ⟨U, f, e nofun⟩



theorem value_form (wt : Revised.WellTyped bk) (v : Value bk t) (h : Typed bk [] t T)
    (c : Join bk T X) (n : Rigid X) : t.tform = X.former := by
  have ⟨_, f, e⟩ := value_fits wt v h
  have ⟨_, c, a⟩ := (new_fits_at f).1 X c n
  rw [← e, ← NewFitsInversion.at_former a]
  apply join_rigid c
  · rw [Rigid, e]
    cases t <;> simp [tform]
  · simpa only [Rigid, NewFitsInversion.at_former a] using n



theorem canon_enu (wt : Revised.WellTyped bk) (v : Value bk t) (h : Typed bk [] t T)
    (c : Join bk T (Enu ks)) : ∃ k, k ∈ ks ∧ t = Lab k := by
  have := value_form wt v h c (by simp [Rigid, former])
  cases v <;> simp [tform, former, ↓tform_call] at this ⊢
  exact lab_in h (.conv c)



end Revised

end

-- Source section: RevisedDataClassification
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion BetaEtaPeak



namespace Revised



-- Data classification needs only closed Data types and these three heads.
def TypedDataExposure (bk : Book) : Prop :=
  ∀ {T X}, Typed bk [] T T2 → Join bk X T → X.former ∈ [1, 2, 3] →
    ∃ Y, Typed bk [] Y T2 ∧ Join bk X Y ∧ Y.former = X.former



-- Data classification follows if this smaller exposure obligation is proved.
theorem canon_data_of_data_exposure (exposure : TypedDataExposure bk) :
    Revised.WellTyped bk → Value bk t → Typed bk [] t T →
    Typed bk [] T T2 → Data t := by
  intro wt v h hT
  have ⟨U, f, e⟩ := value_fits wt v h
  have N (e : U.former = 1 ∨ U.former = 2) : False := by
    have hu : Rigid U := by simp only [Rigid, List.mem_cons]; omega
    have ⟨X, c, a⟩ := (new_fits_at f).2 U join_refl hu
    have ⟨Y, hY, _, eY⟩ := exposure hT (join_symm c)
      (by rw [← NewFitsInversion.at_former a]; simp; omega)
    have ⟨_, g, f', _⟩ := gen hY
    rw [NewFitsInversion.at_former a, ← eY] at e
    cases Y <;> simp [former] at e <;> cases g <;>
      exact absurd (join_lab_inj (join_typ.1 (new_fits2 f'))) (by decide)
  cases v
  case tup _ _ _ ha hb =>
    obtain ⟨_, ⟨A, B, rfl, h1, h2⟩, f', _⟩ := gen h
    have ⟨_, c, a⟩ := (new_fits_at f').2 _ join_refl (by simp [Rigid, former])
    cases a
    have ⟨Y, hY, c, eY⟩ := exposure hT (join_symm c) (by simp [former])
    cases Y <;> cases eY
    obtain ⟨rfl, hA, hB⟩ := join_sig c
    obtain ⟨_, ⟨_, rfl, hA', hB'⟩, f'', _⟩ := gen hY
    have cK := new_fits2 f''
    exact .tup (fun l => canon_data_of_data_exposure exposure wt (ha l)
        (.conv h1 (.conv hA)) (.conv hA' (.conv (by
          revert l; cases ‹Quan› <;> first
            | exact fun _ => cK | exact fun _ => join_refl | nofun))))
      (canon_data_of_data_exposure exposure wt hb (.conv h2 (.conv (join_sub hB)))
        (.conv (inst_succ ▸ typed_inst hB' (.conv h1 (.conv hA)) :) (.conv cK)))
  all_goals first | constructor | refine (N ?_).elim; rw [e]; first
    | exact .inr tform_call | simp [tform]



end Revised

end

-- Source section: DiagnosticExposure
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion



namespace Revised



theorem no_lambda_kind_ctx (h : Typed bk Γ (Lam q f) (Typ g)) : False := by
  obtain ⟨_, ⟨p, A, B, rfl, _⟩, hf, _⟩ := gen h
  have ⟨Y, hj, ha⟩ := (new_fits_at hf).1 _ join_refl (by simp [Rigid, former])
  have hY : Rigid Y := by simpa only [Rigid, NewFitsInversion.at_former ha] using
    (by simp [Rigid, former] : Rigid (Typ g))
  have he := join_rigid hj (by simp [Rigid, former]) hY
  rw [NewFitsInversion.at_former ha] at he
  simp [former] at he



end Revised

end

-- Source section: ExposureResearch
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion



namespace ExposureResearch



inductive EtaOnly : Term → Term → Prop
  | var : EtaOnly (Var i) (Var i)
  | ref : EtaOnly (Ref k) (Ref k)
  | ann : EtaOnly x x' → EtaOnly T T' → EtaOnly (Ann x T) (Ann x' T')
  | lett : EtaOnly v v' → EtaOnly f f' → EtaOnly (Let q v f) (Let q v' f')
  | typ : EtaOnly q q' → EtaOnly (Typ q) (Typ q')
  | min : EtaOnly a a' → EtaOnly b b' → EtaOnly (Min a b) (Min a' b')
  | all : EtaOnly A A' → EtaOnly B B' → EtaOnly (All q A B) (All q A' B')
  | lam : EtaOnly f f' → EtaOnly (Lam Q1 f) (Lam Q1 f')
  | app : EtaOnly f f' → EtaOnly x x' → EtaOnly (App Q1 f x) (App Q1 f' x')
  | sig : EtaOnly A A' → EtaOnly B B' → EtaOnly (Sig q A B) (Sig q A' B')
  | tup : EtaOnly a a' → EtaOnly b b' → EtaOnly (Tup q a b) (Tup q a' b')
  | prj : EtaOnly h h' → EtaOnly (Prj h) (Prj h')
  | enu : EtaOnly (Enu ks) (Enu ks)
  | lab : EtaOnly (Lab k) (Lab k)
  | mat : EtaOnly h h' → EtaOnly m m' → EtaOnly (Mat k h m) (Mat k h' m')
  | efq : EtaOnly Efq Efq
  | eql : EtaOnly a a' → EtaOnly b b' → EtaOnly T T' →
      EtaOnly (Eql a b T) (Eql a' b' T')
  | rfl : EtaOnly Rfl Rfl
  | rwt : EtaOnly e e' → EtaOnly P P' → EtaOnly f f' →
      EtaOnly (Rwt e P f) (Rwt e' P' f')
  | eta : EtaOnly f f' →
      EtaOnly (Lam Q1 (App Q1 (ren Nat.succ f) (Var 0))) f'



inductive EtaSteps : Term → Term → Prop
  | refl : EtaSteps t t
  | step : EtaOnly t u → EtaSteps u v → EtaSteps t v



theorem eta_refl_erase (t : Term) : EtaOnly (erase t) (erase t) := by
  induction t <;> simp only [erase] <;> constructor <;> assumption



theorem eta_refl (h : Canonical t) : EtaOnly t t := by
  rw [← h]
  exact eta_refl_erase _



theorem eta_epar (h : EtaOnly t u) : EPar bk t u := by
  induction h <;> constructor <;> assumption



theorem erase_ren_fix_reflect (t : Term) :
    ren r (erase t) = erase t → ren r t = t := by
  induction t generalizing r <;> simp_all [erase, ren]



def NonLambda (t : Term) : Prop := ∀ q f, t ≠ Lam q f



theorem eta_nonlambda (h : EtaOnly t u) (hn : NonLambda t) :
    NonLambda u ∧ u.former = t.former := by
  cases h <;> first
    | exact (hn _ _ rfl).elim
    | exact ⟨(by intro q f e; cases e), rfl⟩



theorem eta_steps_nonlambda (h : EtaSteps t u) (hn : NonLambda t) :
    NonLambda u ∧ u.former = t.former := by
  induction h with
  | refl => exact ⟨hn, rfl⟩
  | step h _ ih =>
    have ⟨hu, he⟩ := eta_nonlambda h hn
    have ⟨hv, hf⟩ := ih hu
    exact ⟨hv, hf.trans he⟩



theorem erased_nonlambda (hn : NonLambda t) : NonLambda (erase t) := by
  intro q f he
  cases t <;> simp only [erase] at he <;> first
    | exact (hn _ _ rfl).elim
    | cases he



theorem typed_kind_nonlambda (ht : Revised.Typed bk Γ t (Typ g)) : NonLambda t := by
  intro q f he
  subst t
  exact Revised.no_lambda_kind_ctx ht



theorem typed_rigid_nonlambda (ht : Revised.Typed bk Γ t K)
    (hK : K.former ∈ [1, 3, 4, 5]) : NonLambda t := by
  intro q f he
  subst t
  obtain ⟨_, ⟨p, A, B, rfl, _⟩, hf, _⟩ := Revised.gen ht
  have hr : Rigid K := by simp_all [Rigid]; omega
  have ⟨Y, hj, ha⟩ := (new_fits_at hf).1 K join_refl hr
  have hY : Rigid Y := by simpa only [Rigid, NewFitsInversion.at_former ha] using hr
  have he := join_rigid hj (by simp [Rigid, former]) hY
  rw [NewFitsInversion.at_former ha] at he
  change 2 = K.former at he
  have h2 : (2 : Nat) ∈ [1, 3, 4, 5] := by simpa only [← he] using hK
  simp at h2



theorem nonlambda_sub_reflect (h : NonLambda (sub σ t)) : NonLambda t := by
  intro q f he
  subst t
  exact h _ _ rfl



theorem typed_known_form (h : Revised.Typed bk Γ t T) (hn : t.former ≠ 0)
    (hc : Join bk T X) (hx : Rigid X) : t.tform = X.former := by
  obtain ⟨U, _, hf, he⟩ := Revised.gen h
  have hu := he hn
  obtain ⟨Y, hj, ha⟩ := (new_fits_at hf).1 X hc hx
  have hur : Rigid U := by rw [Rigid, hu]; cases t <;> simp [tform]
  have hyr : Rigid Y := by simpa only [Rigid, NewFitsInversion.at_former ha] using hx
  have hjf := join_rigid hj hur hyr
  rw [hu, NewFitsInversion.at_former ha] at hjf
  exact hjf



def CallableShape (t : Term) : Prop := t.former ∈ [0, 6, 7, 8, 9]



theorem typed_callable (h : Revised.Typed bk Γ t (All q A B)) : CallableShape t := by
  by_cases hn : t.former = 0
  · simp [CallableShape, hn]
  · have hf := typed_known_form h hn join_refl (by simp [Rigid, former])
    cases t <;> simp_all [CallableShape, former, tform]



theorem former_sub_nonzero (h : t.former ≠ 0) : (sub σ t).former = t.former := by
  cases t <;> simp_all [sub, former]



theorem callable_sub_reflect (h : CallableShape (sub σ t)) : CallableShape t := by
  by_cases hz : t.former = 0
  · simp [CallableShape, hz]
  · simpa only [CallableShape, former_sub_nonzero hz] using h



theorem primitive_argument_nonlambda
    (hf : Revised.Typed bk Γ f (All q A B)) (hx : Revised.Typed bk Γ x A)
    (hh : f.former ∈ [7, 8]) : NonLambda x := by
  cases f <;> simp [former] at hh
  case Prj h =>
    obtain ⟨_, ⟨_, _, _, _, _, rfl, _, hh⟩, hfit, _⟩ := Revised.gen hf
    obtain ⟨_, hA, _⟩ := new_fits_all hfit
    exact typed_rigid_nonlambda (.conv hx hA) (by simp [former])
  case Mat k h m =>
    obtain ⟨_, ⟨_, _, _, rfl, _, hh, hm⟩, hfit, _⟩ := Revised.gen hf
    obtain ⟨_, hA, _⟩ := new_fits_all hfit
    exact typed_rigid_nonlambda (.conv hx hA) (by simp [former])



def HeadSafe : Term → Prop
  | App _ f x => CallableShape f ∧ (f.former ∈ [7, 8] → NonLambda x) ∧ HeadSafe f ∧ HeadSafe x
  | Rwt e P f => NonLambda e ∧ HeadSafe e ∧ HeadSafe P ∧ HeadSafe f
  | Typ q => NonLambda q ∧ HeadSafe q
  | Term.Min a b => NonLambda a ∧ NonLambda b ∧ HeadSafe a ∧ HeadSafe b
  | Ann x T => HeadSafe x ∧ HeadSafe T
  | Let _ v f => HeadSafe v ∧ HeadSafe f
  | All _ A B | Sig _ A B => HeadSafe A ∧ HeadSafe B
  | Lam _ f | Prj f => HeadSafe f
  | Tup _ f x => HeadSafe f ∧ HeadSafe x
  | Mat _ h m => HeadSafe h ∧ HeadSafe m
  | Eql a b T => HeadSafe a ∧ HeadSafe b ∧ HeadSafe T
  | _ => True



theorem head_safe_sub_reflect (t : Term) : HeadSafe (sub σ t) → HeadSafe t := by
  induction t generalizing σ <;> simp only [sub, HeadSafe]
  case Rwt e P f ihe ihP ihf =>
    exact fun h => ⟨nonlambda_sub_reflect h.1, ihe h.2.1, ihP h.2.2.1, ihf h.2.2.2⟩
  case Typ g ih => exact fun h => ⟨nonlambda_sub_reflect h.1, ih h.2⟩
  case Min a b iha ihb =>
    exact fun h => ⟨nonlambda_sub_reflect h.1, nonlambda_sub_reflect h.2.1,
      iha h.2.2.1, ihb h.2.2.2⟩
  case App q f x ihf ihx =>
    intro h
    refine ⟨callable_sub_reflect h.1, fun hf => ?_, ihf h.2.2.1, ihx h.2.2.2⟩
    have hz : f.former ≠ 0 := by intro hz; simp [hz] at hf
    have hs : (sub σ f).former ∈ [7, 8] := by simpa only [former_sub_nonzero hz] using hf
    exact nonlambda_sub_reflect (h.2.1 hs)
  all_goals grind



theorem typed_head_safe (h : Revised.Typed bk Γ t T) : HeadSafe t := by
  induction h <;> (try simp only [HeadSafe])
  case lett hv hq hf ihv ihq ihf =>
    exact ⟨ihv, head_safe_sub_reflect _ ihf⟩
  case rwt he hP hF hf ihe ihP ihf =>
    exact ⟨typed_rigid_nonlambda he (by simp [former]), ihe, ihP, ihf⟩
  case typ h ih => exact ⟨typed_rigid_nonlambda h (by simp [former]), ih⟩
  case min ha hb iha ihb => exact ⟨typed_rigid_nonlambda ha (by simp [former]),
    typed_rigid_nonlambda hb (by simp [former]), iha, ihb⟩
  case app hf hx ihf ihx =>
    exact ⟨typed_callable hf, primitive_argument_nonlambda hf hx, ihf, ihx⟩
  all_goals first
    | exact True.intro
    | assumption
    | exact ⟨by assumption, by assumption⟩
    | exact ⟨by assumption, by assumption, by assumption⟩



-- Eta alone cannot expose a new rigid head in a term typed at a kind.
theorem eta_typed_kind_head (ht : Revised.Typed bk Γ t (Typ g))
    (he : EtaSteps (erase t) u) : u.former = t.former := by
  have h := (eta_steps_nonlambda he (erased_nonlambda (typed_kind_nonlambda ht))).2
  simpa only [erase_keeps_former] using h



end ExposureResearch

end

-- Source section: ContextualEta
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open ExposureResearch



namespace ContextualEta



inductive Step : Term → Term → Prop
  | eta : Step (Lam Q1 (App Q1 (ren Nat.succ f) (Var 0))) f
  | ann_left : Step x x' → Step (Ann x T) (Ann x' T)
  | ann_right : Step T T' → Step (Ann x T) (Ann x T')
  | let_value : Step v v' → Step (Let q v f) (Let q v' f)
  | let_body : Step f f' → Step (Let q v f) (Let q v f')
  | typ : Step q q' → Step (Typ q) (Typ q')
  | min_left : Step a a' → Step (Term.Min a b) (Term.Min a' b)
  | min_right : Step b b' → Step (Term.Min a b) (Term.Min a b')
  | all_domain : Step A A' → Step (All q A B) (All q A' B)
  | all_body : Step B B' → Step (All q A B) (All q A B')
  | lam : Step f f' → Step (Lam q f) (Lam q f')
  | app_function : Step f f' → Step (App q f x) (App q f' x)
  | app_argument : Step x x' → Step (App q f x) (App q f x')
  | sig_domain : Step A A' → Step (Sig q A B) (Sig q A' B)
  | sig_body : Step B B' → Step (Sig q A B) (Sig q A B')
  | tup_first : Step a a' → Step (Tup q a b) (Tup q a' b)
  | tup_second : Step b b' → Step (Tup q a b) (Tup q a b')
  | prj : Step h h' → Step (Prj h) (Prj h')
  | mat_hit : Step h h' → Step (Mat k h m) (Mat k h' m)
  | mat_miss : Step m m' → Step (Mat k h m) (Mat k h m')
  | eql_left : Step a a' → Step (Eql a b T) (Eql a' b T)
  | eql_right : Step b b' → Step (Eql a b T) (Eql a b' T)
  | eql_type : Step T T' → Step (Eql a b T) (Eql a b T')
  | rwt_proof : Step e e' → Step (Rwt e P f) (Rwt e' P f)
  | rwt_motive : Step P P' → Step (Rwt e P f) (Rwt e P' f)
  | rwt_value : Step f f' → Step (Rwt e P f) (Rwt e P f')



inductive Steps : Term → Term → Prop
  | refl : Steps t t
  | step : Step t u → Steps u v → Steps t v



theorem steps_trans (h : Steps t u) (g : Steps u v) : Steps t v := by
  induction h with
  | refl => exact g
  | step h _ ih => exact .step h (ih g)



theorem steps_map (F : Term → Term)
    (hf : ∀ {t u}, Step t u → Step (F t) (F u)) (h : Steps t u) :
    Steps (F t) (F u) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (hf h) ih



theorem steps_map2 (F : Term → Term → Term)
    (hl : ∀ {t u} a, Step t u → Step (F t a) (F u a))
    (hr : ∀ {t u} a, Step t u → Step (F a t) (F a u))
    (ha : Steps a a') (hb : Steps b b') : Steps (F a b) (F a' b') :=
  steps_trans (steps_map (F · b) (hl b) ha) (steps_map (F a') (hr a') hb)



theorem steps_map3 (F : Term → Term → Term → Term)
    (h1 : ∀ {t u} a b, Step t u → Step (F t a b) (F u a b))
    (h2 : ∀ {t u} a b, Step t u → Step (F a t b) (F a u b))
    (h3 : ∀ {t u} a b, Step t u → Step (F a b t) (F a b u))
    (ha : Steps a a') (hb : Steps b b') (hc : Steps c c') :
    Steps (F a b c) (F a' b' c') :=
  steps_trans (steps_map (F · b c) (h1 b c) ha)
    (steps_trans (steps_map (F a' · c) (h2 a' c) hb)
      (steps_map (F a' b') (h3 a' b') hc))



theorem step_eta_only (h : Step t u) (hc : Canonical t) : EtaOnly t u := by
  induction h
  all_goals simp only [Canonical, erase, erase_ren, Term.Ann.injEq, Term.Let.injEq,
    Term.Typ.injEq, Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq,
    Term.Sig.injEq, Term.Tup.injEq, Term.Prj.injEq, Term.Mat.injEq, Term.Eql.injEq,
    Term.Rwt.injEq, true_and, and_true] at hc
  case eta f =>
    apply EtaOnly.eta
    apply eta_refl
    exact CriticalPairs.ren_injective Nat.succ (fun _ _ e => Nat.succ.inj e) hc
  case ann_left _ ih => exact .ann (ih hc.1) (eta_refl hc.2)
  case ann_right _ ih => exact .ann (eta_refl hc.1) (ih hc.2)
  case let_value _ ih => exact .lett (ih hc.1) (eta_refl hc.2)
  case let_body _ ih => exact .lett (eta_refl hc.1) (ih hc.2)
  case typ _ ih => exact .typ (ih hc)
  case min_left _ ih => exact .min (ih hc.1) (eta_refl hc.2)
  case min_right _ ih => exact .min (eta_refl hc.1) (ih hc.2)
  case all_domain _ ih => exact .all (ih hc.1) (eta_refl hc.2)
  case all_body _ ih => exact .all (eta_refl hc.1) (ih hc.2)
  case lam _ ih => rcases hc with ⟨rfl, hc⟩; exact .lam (ih hc)
  case app_function _ ih => rcases hc with ⟨rfl, hc⟩; exact .app (ih hc.1) (eta_refl hc.2)
  case app_argument _ ih => rcases hc with ⟨rfl, hc⟩; exact .app (eta_refl hc.1) (ih hc.2)
  case sig_domain _ ih => exact .sig (ih hc.1) (eta_refl hc.2)
  case sig_body _ ih => exact .sig (eta_refl hc.1) (ih hc.2)
  case tup_first _ ih => exact .tup (ih hc.1) (eta_refl hc.2)
  case tup_second _ ih => exact .tup (eta_refl hc.1) (ih hc.2)
  case prj _ ih => exact .prj (ih hc)
  case mat_hit _ ih => exact .mat (ih hc.1) (eta_refl hc.2)
  case mat_miss _ ih => exact .mat (eta_refl hc.1) (ih hc.2)
  case eql_left _ ih => exact .eql (ih hc.1) (eta_refl hc.2.1) (eta_refl hc.2.2)
  case eql_right _ ih => exact .eql (eta_refl hc.1) (ih hc.2.1) (eta_refl hc.2.2)
  case eql_type _ ih => exact .eql (eta_refl hc.1) (eta_refl hc.2.1) (ih hc.2.2)
  case rwt_proof _ ih => exact .rwt (ih hc.1) (eta_refl hc.2.1) (eta_refl hc.2.2)
  case rwt_motive _ ih => exact .rwt (eta_refl hc.1) (ih hc.2.1) (eta_refl hc.2.2)
  case rwt_value _ ih => exact .rwt (eta_refl hc.1) (eta_refl hc.2.1) (ih hc.2.2)



theorem step_canonical (h : Step t u) (hc : Canonical t) : Canonical u :=
  epar_canonical (bk := fun _ => none) (by intro _ _ h; cases h)
    (eta_epar (step_eta_only h hc)) hc



theorem steps_eta_steps (h : Steps t u) (hc : Canonical t) : EtaSteps t u := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (step_eta_only h hc) (ih (step_canonical h hc))



end ContextualEta

end

-- Source section: EtaPathView
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch



namespace ContextualEta



inductive BigEta : Term → Term → Prop
  | var : BigEta (Var i) (Var i)
  | ref : BigEta (Ref k) (Ref k)
  | ann : BigEta x x' → BigEta T T' → BigEta (Ann x T) (Ann x' T')
  | lett : BigEta v v' → BigEta f f' → BigEta (Let q v f) (Let q v' f')
  | typ : BigEta q q' → BigEta (Typ q) (Typ q')
  | min : BigEta a a' → BigEta b b' → BigEta (Min a b) (Min a' b')
  | all : BigEta A A' → BigEta B B' → BigEta (All q A B) (All q A' B')
  | lam : BigEta f f' → BigEta (Lam q f) (Lam q f')
  | app : BigEta f f' → BigEta x x' → BigEta (App q f x) (App q f' x')
  | sig : BigEta A A' → BigEta B B' → BigEta (Sig q A B) (Sig q A' B')
  | tup : BigEta a a' → BigEta b b' → BigEta (Tup q a b) (Tup q a' b')
  | prj : BigEta h h' → BigEta (Prj h) (Prj h')
  | enu : BigEta (Enu ks) (Enu ks)
  | lab : BigEta (Lab k) (Lab k)
  | mat : BigEta h h' → BigEta m m' → BigEta (Mat k h m) (Mat k h' m')
  | efq : BigEta Efq Efq
  | eql : BigEta a a' → BigEta b b' → BigEta T T' →
      BigEta (Eql a b T) (Eql a' b' T')
  | rfl : BigEta Rfl Rfl
  | rwt : BigEta e e' → BigEta P P' → BigEta f f' →
      BigEta (Rwt e P f) (Rwt e' P' f')
  | eta : BigEta body (App Q1 (ren Nat.succ f) (Var 0)) →
      BigEta (Lam Q1 body) f



theorem big_eta_refl (t : Term) : BigEta t t := by
  induction t <;> constructor <;> assumption



theorem big_eta_ren (h : BigEta t u) : BigEta (ren r t) (ren r u) := by
  induction h generalizing r <;> simp only [ren]
  case eta h ih =>
    apply BigEta.eta
    simpa only [ren, ren_ren, Function.comp_def, Ren.up] using ih (r := Ren.up r)
  all_goals constructor <;> first | assumption | apply_assumption



theorem big_eta_trans (h : BigEta t u) (g : BigEta u v) : BigEta t v := by
  induction h generalizing v
  case eta h ih => exact .eta (ih (.app (big_eta_ren g) .var))
  case lam h ih =>
    cases g with
    | lam g => exact .lam (ih g)
    | eta g => exact .eta (ih g)
  all_goals cases g <;> constructor <;> first | assumption | (apply_assumption; assumption)



theorem step_big_eta (h : Step t u) : BigEta t u := by
  induction h
  case eta => exact .eta (big_eta_refl _)
  all_goals constructor <;> first | assumption | exact big_eta_refl _



theorem big_eta_steps (h : BigEta t u) : Steps t u := by
  induction h
  case eta _ ih => exact steps_trans (steps_map (Lam Q1) Step.lam ih) (.step .eta .refl)
  case typ _ ih => exact steps_map Typ Step.typ ih
  case lam _ ih => exact steps_map (Lam _) Step.lam ih
  case prj _ ih => exact steps_map Prj Step.prj ih
  case ann _ _ ih1 ih2 => exact steps_map2 Ann (fun _ => Step.ann_left) (fun _ => Step.ann_right) ih1 ih2
  case lett _ _ ih1 ih2 => exact steps_map2 (Let _) (fun _ => Step.let_value) (fun _ => Step.let_body) ih1 ih2
  case min _ _ ih1 ih2 => exact steps_map2 Term.Min (fun _ => Step.min_left) (fun _ => Step.min_right) ih1 ih2
  case all _ _ ih1 ih2 => exact steps_map2 (All _) (fun _ => Step.all_domain) (fun _ => Step.all_body) ih1 ih2
  case app _ _ ih1 ih2 => exact steps_map2 (App _) (fun _ => Step.app_function) (fun _ => Step.app_argument) ih1 ih2
  case sig _ _ ih1 ih2 => exact steps_map2 (Sig _) (fun _ => Step.sig_domain) (fun _ => Step.sig_body) ih1 ih2
  case tup _ _ ih1 ih2 => exact steps_map2 (Tup _) (fun _ => Step.tup_first) (fun _ => Step.tup_second) ih1 ih2
  case mat _ _ ih1 ih2 => exact steps_map2 (Mat _) (fun _ => Step.mat_hit) (fun _ => Step.mat_miss) ih1 ih2
  case eql _ _ _ ih1 ih2 ih3 => exact steps_map3 Eql (fun _ _ => Step.eql_left) (fun _ _ => Step.eql_right) (fun _ _ => Step.eql_type) ih1 ih2 ih3
  case rwt _ _ _ ih1 ih2 ih3 => exact steps_map3 Rwt (fun _ _ => Step.rwt_proof) (fun _ _ => Step.rwt_motive) (fun _ _ => Step.rwt_value) ih1 ih2 ih3
  all_goals exact .refl



theorem big_eta_eta_steps (h : BigEta t u) (hc : Canonical t) : EtaSteps t u :=
  steps_eta_steps (big_eta_steps h) hc



theorem big_eta_sub (h : BigEta t u) (hs : ∀ i, BigEta (σ i) (τ i)) :
    BigEta (sub σ t) (sub τ u) := by
  have U {σ τ} (h : ∀ i, BigEta (σ i) (τ i)) :
      ∀ i, BigEta (Subst.up σ i) (Subst.up τ i)
    | 0 => .var
    | _ + 1 => big_eta_ren (h _)
  induction h generalizing σ τ <;> simp only [sub]
  case eta h ih =>
    apply BigEta.eta
    simpa only [sub, sub_succ, Subst.up] using ih (U hs)
  all_goals first | exact hs _ | constructor
  all_goals first | assumption | (apply_assumption; (repeat apply U); exact hs)



theorem big_eta_inst (hf : BigEta f f') (hx : BigEta x x') :
    BigEta (inst f x) (inst f' x') :=
  big_eta_sub hf (σ := Subst.one x) (τ := Subst.one x') (by
    intro i; cases i; exact hx; exact .var)



theorem big_eta_nonlambda (h : BigEta t u) (hn : NonLambda t) :
    NonLambda u ∧ u.former = t.former := by
  cases h <;> first
    | exact (hn _ _ rfl).elim
    | exact ⟨(by intro q f he; cases he), rfl⟩



end ContextualEta

end

-- Source section: HeadSafeSupport
section

open Quan Term ConversionDesign ErasedReduction EquationBridge ExecutableOrder


open ExposureResearch



namespace HeadSafeSupport



theorem nonlambda_erase : NonLambda (erase t) ↔ NonLambda t := by
  constructor
  · intro h q f e
    subst t
    exact h Q1 (erase f) rfl
  · exact erased_nonlambda



theorem callable_erase : CallableShape (erase t) ↔ CallableShape t := by
  simp only [CallableShape, erase_keeps_former]



theorem head_safe_erase : HeadSafe (erase t) ↔ HeadSafe t := by
  induction t <;> simp [erase, HeadSafe, nonlambda_erase, callable_erase,
    erase_keeps_former, *]



theorem former_ren : (ren r t).former = t.former := by cases t <;> rfl



theorem nonlambda_ren : NonLambda (ren r t) ↔ NonLambda t := by
  constructor
  · intro h q f e
    subst t
    exact h q (ren (Ren.up r) f) rfl
  · intro h q f e
    cases t <;> simp only [ren] at e <;> first
      | exact (h _ _ rfl).elim
      | cases e



theorem callable_ren : CallableShape (ren r t) ↔ CallableShape t := by
  simp only [CallableShape, former_ren]



-- These facts hold for every renaming. Injectivity is not needed.
theorem head_safe_ren : HeadSafe (ren r t) ↔ HeadSafe t := by
  induction t generalizing r <;> simp [ren, HeadSafe, nonlambda_ren,
    callable_ren, former_ren, *]



end HeadSafeSupport

end

-- Source section: ErasedOrdinary
section

open Quan Term ConversionDesign ErasedReduction



namespace ErasedOrdinary



-- Original reduction transports across Lam and App quantity erasure.
theorem par_retag (hp : Par bk a b) :
    ∀ {t}, erase t = erase a → ∃ u, Par bk t u ∧ erase u = erase b := by
  induction hp
  all_goals intro t he
  all_goals cases t <;> simp only [erase] at he <;> try cases he
  case var.Var.refl => exact ⟨_, .var, rfl⟩
  case ref.Ref.refl => exact ⟨_, .ref, rfl⟩
  case enu.Enu.refl => exact ⟨_, .enu, rfl⟩
  case lab.Lab.refl => exact ⟨_, .lab, rfl⟩
  case efq.Efq.intro => exact ⟨_, .efq, rfl⟩
  case rfl.Rfl.intro => exact ⟨_, .rfl, rfl⟩
  case delta.Ref.refl hk hc => exact ⟨_, .delta hk hc, rfl⟩
  case ann.Ann ihx ihT x T =>
    have ⟨hx, hT⟩ := Term.Ann.inj he
    obtain ⟨x', px, ex⟩ := ihx hx
    obtain ⟨T', pT, eT⟩ := ihT hT
    exact ⟨_, .ann px pT, by simp only [erase, ex, eT]⟩
  case typ.Typ ih q =>
    obtain ⟨q', pq, eq⟩ := ih (Term.Typ.inj he)
    exact ⟨_, .typ pq, by simp only [erase, eq]⟩
  case min.Min iha ihb a b =>
    have ⟨ha, hb⟩ := Term.Min.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .min pa pb, by simp only [erase, ea, eb]⟩
  case lam.Lam ih q f =>
    obtain ⟨f', pf, ef⟩ := ih (Term.Lam.inj he).2
    exact ⟨_, .lam pf (Or.inl rfl), by simp only [erase, ef]⟩
  case app.App ihf ihx q f x =>
    have ⟨_, hf, hx⟩ := Term.App.inj he
    obtain ⟨f', pf, ef⟩ := ihf hf
    obtain ⟨x', px, ex⟩ := ihx hx
    exact ⟨_, .app pf px, by simp only [erase, ef, ex]⟩
  case prj.Prj ih h =>
    obtain ⟨h', ph, eh⟩ := ih (Term.Prj.inj he)
    exact ⟨_, .prj ph, by simp only [erase, eh]⟩
  case unann.Ann ih x T =>
    obtain ⟨x', px, ex⟩ := ih (Term.Ann.inj he).1
    exact ⟨_, .unann px, ex⟩
  case meet.Min iha ihb a b =>
    have ⟨ha, hb⟩ := Term.Min.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .meet pa pb, by simp only [erase_qmin, ea, eb]⟩
  case lett.Let iha ihb q a b =>
    have ⟨hq, ha, hb⟩ := Term.Let.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .lett pa pb, by simp only [erase, hq, ea, eb]⟩
  case all.All iha ihb q a b =>
    have ⟨hq, ha, hb⟩ := Term.All.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .all pa pb, by simp only [erase, hq, ea, eb]⟩
  case sig.Sig iha ihb q a b =>
    have ⟨hq, ha, hb⟩ := Term.Sig.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .sig pa pb, by simp only [erase, hq, ea, eb]⟩
  case tup.Tup iha ihb q a b =>
    have ⟨hq, ha, hb⟩ := Term.Tup.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .tup pa pb, by simp only [erase, hq, ea, eb]⟩
  case mat.Mat iha ihb q a b =>
    have ⟨hq, ha, hb⟩ := Term.Mat.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    exact ⟨_, .mat pa pb, by simp only [erase, hq, ea, eb]⟩
  case eql.Eql iha ihb ihc a b c =>
    have ⟨ha, hb, hc⟩ := Term.Eql.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    obtain ⟨c', pc, ec⟩ := ihc hc
    exact ⟨_, .eql pa pb pc, by simp only [erase, ea, eb, ec]⟩
  case rwt.Rwt iha ihb ihc a b c =>
    have ⟨ha, hb, hc⟩ := Term.Rwt.inj he
    obtain ⟨a', pa, ea⟩ := iha ha
    obtain ⟨b', pb, eb⟩ := ihb hb
    obtain ⟨c', pc, ec⟩ := ihc hc
    exact ⟨_, .rwt pa pb pc, by simp only [erase, ea, eb, ec]⟩
  case unlet.Let ihv ihf q v f =>
    have ⟨_, hv, hf⟩ := Term.Let.inj he
    obtain ⟨v', pv, ev⟩ := ihv hv
    obtain ⟨f', pf, ef⟩ := ihf hf
    exact ⟨_, .unlet pv pf, by simp only [erase_inst, ev, ef]⟩
  case beta.App ihf ihx q f x =>
    have ⟨_, hf, hx⟩ := Term.App.inj he
    cases f <;> simp only [erase] at hf <;> try cases hf
    case Lam p f =>
      obtain ⟨f', pf, ef⟩ := ihf (Term.Lam.inj hf).2
      obtain ⟨x', px, ex⟩ := ihx hx
      exact ⟨_, .beta pf px, by simp only [erase_inst, ef, ex]⟩
  case split.App ihh iha ihb q f x =>
    have ⟨_, hf, hx⟩ := Term.App.inj he
    cases f <;> simp only [erase] at hf <;> try cases hf
    case Prj h =>
      cases x <;> simp only [erase] at hx <;> try cases hx
      case Tup r a b =>
        obtain ⟨h', ph, eh⟩ := ihh (Term.Prj.inj hf)
        obtain ⟨a', pa, ea⟩ := iha (Term.Tup.inj hx).2.1
        obtain ⟨b', pb, eb⟩ := ihb (Term.Tup.inj hx).2.2
        exact ⟨_, .split ph pa pb, by simp only [erase, eh, ea, eb]⟩
  case hit.App ih q f x =>
    have ⟨_, hf, hx⟩ := Term.App.inj he
    cases f <;> simp only [erase] at hf <;> try cases hf
    case Mat k h m =>
      cases x <;> simp only [erase] at hx <;> try cases hx
      have ⟨hk, hh, _⟩ := Term.Mat.inj hf
      subst k
      obtain ⟨h', ph, eh⟩ := ih hh
      exact ⟨_, .hit ph, eh⟩
  case miss.App hn _ ih q f x =>
    have ⟨_, hf, hx⟩ := Term.App.inj he
    cases f <;> simp only [erase] at hf <;> try cases hf
    case Mat k h m =>
      cases x <;> simp only [erase] at hx <;> try cases hx
      have ⟨hk, _, hm⟩ := Term.Mat.inj hf
      subst k
      obtain ⟨m', pm, em⟩ := ih hm
      exact ⟨_, .miss hn pm, by simp only [erase, em]⟩
  case cast.Rwt ih e P f =>
    have ⟨he, _, hf⟩ := Term.Rwt.inj he
    cases e <;> simp only [erase] at he <;> try cases he
    obtain ⟨f', pf, ef⟩ := ih hf
    exact ⟨_, .cast pf, ef⟩



-- OPar contains original reduction after erasure. It has no eta rule.
inductive OPar (bk : Book) : Term → Term → Prop
  | var : OPar bk (Var i) (Var i)
  | ref : OPar bk (Ref k) (Ref k)
  | ann : OPar bk x x' → OPar bk T T' → OPar bk (Ann x T) (Ann x' T')
  | lett : OPar bk v v' → OPar bk f f' → OPar bk (Let q v f) (Let q v' f')
  | typ : OPar bk q q' → OPar bk (Typ q) (Typ q')
  | min : OPar bk a a' → OPar bk b b' → OPar bk (Min a b) (Min a' b')
  | all : OPar bk A A' → OPar bk B B' → OPar bk (All q A B) (All q A' B')
  | lam : OPar bk f f' → OPar bk (Lam Q1 f) (Lam Q1 f')
  | app : OPar bk f f' → OPar bk x x' → OPar bk (App Q1 f x) (App Q1 f' x')
  | sig : OPar bk A A' → OPar bk B B' → OPar bk (Sig q A B) (Sig q A' B')
  | tup : OPar bk a a' → OPar bk b b' → OPar bk (Tup q a b) (Tup q a' b')
  | prj : OPar bk h h' → OPar bk (Prj h) (Prj h')
  | enu : OPar bk (Enu ks) (Enu ks)
  | lab : OPar bk (Lab k) (Lab k)
  | mat : OPar bk h h' → OPar bk m m' → OPar bk (Mat k h m) (Mat k h' m')
  | efq : OPar bk Efq Efq
  | eql : OPar bk a a' → OPar bk b b' → OPar bk T T' →
      OPar bk (Eql a b T) (Eql a' b' T')
  | rfl : OPar bk Rfl Rfl
  | rwt : OPar bk e e' → OPar bk P P' → OPar bk f f' →
      OPar bk (Rwt e P f) (Rwt e' P' f')
  | delta : Book.get bk k = some d → Closed d.v → OPar bk (Ref k) (erase d.v)
  | unann : OPar bk x x' → OPar bk (Ann x T) x'
  | unlet : OPar bk v v' → OPar bk f f' → OPar bk (Let q v f) (inst f' v')
  | beta : OPar bk f f' → OPar bk x x' →
      OPar bk (App Q1 (Lam Q1 f) x) (inst f' x')
  | split : OPar bk h h' → OPar bk a a' → OPar bk b b' →
      OPar bk (App Q1 (Prj h) (Tup r a b)) (App Q1 (App Q1 h' a') b')
  | hit : OPar bk h h' → OPar bk (App Q1 (Mat k h m) (Lab k)) h'
  | miss : j ≠ k → OPar bk m m' →
      OPar bk (App Q1 (Mat k h m) (Lab j)) (App Q1 m' (Lab j))
  | cast : OPar bk f f' → OPar bk (Rwt Rfl P f) f'
  | meet : OPar bk a a' → OPar bk b b' → OPar bk (Min a b) (qmin a' b')



inductive OPars (bk : Book) : Term → Term → Prop
  | refl : OPars bk t t
  | step : OPar bk t u → OPars bk u v → OPars bk t v



theorem original_representative (h : OPar bk a b) :
    ∃ u, Par bk a u ∧ erase u = b := by
  induction h
  case var => exact ⟨_, .var, rfl⟩
  case ref => exact ⟨_, .ref, rfl⟩
  case enu => exact ⟨_, .enu, rfl⟩
  case lab => exact ⟨_, .lab, rfl⟩
  case efq => exact ⟨_, .efq, rfl⟩
  case rfl => exact ⟨_, .rfl, rfl⟩
  case delta hk hc => exact ⟨_, .delta hk hc, rfl⟩
  case ann ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .ann p0 p1, by simp only [erase, e0, e1]⟩
  case lett ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .lett p0 p1, by simp only [erase, e0, e1]⟩
  case typ ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .typ p0, by simp only [erase, e0]⟩
  case min ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .min p0 p1, by simp only [erase, e0, e1]⟩
  case all ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .all p0 p1, by simp only [erase, e0, e1]⟩
  case lam ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .lam p0 (Or.inl rfl), by simp only [erase, e0]⟩
  case app ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .app p0 p1, by simp only [erase, e0, e1]⟩
  case sig ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .sig p0 p1, by simp only [erase, e0, e1]⟩
  case tup ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .tup p0 p1, by simp only [erase, e0, e1]⟩
  case prj ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .prj p0, by simp only [erase, e0]⟩
  case mat ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .mat p0 p1, by simp only [erase, e0, e1]⟩
  case eql ih0 ih1 ih2 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    obtain ⟨u2, p2, e2⟩ := ih2
    exact ⟨_, .eql p0 p1 p2, by simp only [erase, e0, e1, e2]⟩
  case rwt ih0 ih1 ih2 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    obtain ⟨u2, p2, e2⟩ := ih2
    exact ⟨_, .rwt p0 p1 p2, by simp only [erase, e0, e1, e2]⟩
  case unann ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .unann p0, by simp only [ e0]⟩
  case unlet ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .unlet p0 p1, by simp only [erase_inst, e0, e1]⟩
  case beta ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .beta p0 p1, by simp only [erase_inst, e0, e1]⟩
  case split ih0 ih1 ih2 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    obtain ⟨u2, p2, e2⟩ := ih2
    exact ⟨_, .split p0 p1 p2, by simp only [erase, e0, e1, e2]⟩
  case hit ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .hit p0, by simp only [ e0]⟩
  case miss hn _ ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .miss hn p0, by simp only [erase, e0]⟩
  case cast ih0 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    exact ⟨_, .cast p0, by simp only [ e0]⟩
  case meet ih0 ih1 =>
    obtain ⟨u0, p0, e0⟩ := ih0
    obtain ⟨u1, p1, e1⟩ := ih1
    exact ⟨_, .meet p0 p1, by simp only [erase_qmin, e0, e1]⟩




theorem opar_lift (hp : OPar bk a b) (ht : erase t = a) :
    ∃ u, Par bk t u ∧ erase u = b := by
  obtain ⟨v, hv, he⟩ := original_representative hp
  obtain ⟨u, hu, eu⟩ := par_retag hv (t := t) (by rw [← ht, erase_idem])
  exact ⟨u, hu, eu.trans he⟩



theorem opars_lift (hp : OPars bk a b) :
    ∀ {t}, erase t = a → ∃ u, Pars bk t u ∧ erase u = b := by
  induction hp with
  | refl => intro t ht; exact ⟨t, .refl, ht⟩
  | step hp _ ih =>
    intro t ht
    obtain ⟨u, hu, eu⟩ := opar_lift hp ht
    obtain ⟨v, hv, ev⟩ := ih eu
    exact ⟨v, .step hu hv, ev⟩



theorem erase_opar (hp : Par bk a b) : OPar bk (erase a) (erase b) := by
  induction hp <;> simp only [erase, erase_inst, erase_qmin]
  case delta hk hc => exact .delta hk hc
  all_goals first | apply OPar.split | apply OPar.miss | constructor
  all_goals assumption



theorem opar_refl (h : Canonical t) : OPar bk t t := by
  rw [← h]
  exact erase_opar par_refl



theorem opars_trans (ha : OPars bk a b) (hb : OPars bk b c) : OPars bk a c := by
  induction ha with
  | refl => exact hb
  | step hp _ ih => exact .step hp (ih hb)



theorem opar_canonical (hp : OPar bk a b) : Canonical b := by
  obtain ⟨u, _, rfl⟩ := original_representative hp
  exact erase_idem _



theorem opars_canonical (hp : OPars bk a b) (ha : Canonical a) : Canonical b := by
  induction hp with
  | refl => exact ha
  | step hp _ ih => exact ih (opar_canonical hp)



theorem opars_map (F : Term → Term)
    (hf : ∀ {t u}, OPar bk t u → OPar bk (F t) (F u)) (h : OPars bk t u) :
    OPars bk (F t) (F u) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (hf h) ih



theorem opars_map2 (F : Term → Term → Term)
    (hf : ∀ {a a' b b'}, OPar bk a a' → OPar bk b b' → OPar bk (F a b) (F a' b'))
    (ha : OPars bk a a') (hb : OPars bk b b') (ca : Canonical a) (cb : Canonical b) :
    OPars bk (F a b) (F a' b') :=
  opars_trans (opars_map (F · b) (fun h => hf h (opar_refl cb)) ha)
    (opars_map (F a') (fun h => hf (opar_refl (opars_canonical ha ca)) h) hb)



theorem opars_map3 (F : Term → Term → Term → Term)
    (hf : ∀ {a a' b b' c c'}, OPar bk a a' → OPar bk b b' → OPar bk c c' →
      OPar bk (F a b c) (F a' b' c'))
    (ha : OPars bk a a') (hb : OPars bk b b') (hc : OPars bk c c')
    (ca : Canonical a) (cb : Canonical b) (cc : Canonical c) :
    OPars bk (F a b c) (F a' b' c') :=
  opars_trans (opars_map (F · b c) (fun h => hf h (opar_refl cb) (opar_refl cc)) ha)
    (opars_trans (opars_map (F a' · c)
      (fun h => hf (opar_refl (opars_canonical ha ca)) h (opar_refl cc)) hb)
      (opars_map (F a' b')
        (fun h => hf (opar_refl (opars_canonical ha ca))
          (opar_refl (opars_canonical hb cb)) h) hc))



theorem opar_ren (h : OPar bk t u) : OPar bk (ren r t) (ren r u) := by
  induction h generalizing r <;> simp only [ren, ren_inst]
  case delta hk hc =>
    rw [ren_as_sub, erase_closed hc]
    exact .delta hk hc
  case meet =>
    rcases qmin_map (ren r) (fun _ => rfl) with e | e <;> rw [e] <;>
      constructor <;> apply_assumption
  all_goals first | apply OPar.split | apply OPar.miss | constructor
  all_goals first | assumption | apply_assumption



theorem opar_sub (h : OPar bk t u) (hs : ∀ i, OPar bk (σ i) (τ i)) :
    OPar bk (sub σ t) (sub τ u) := by
  have U {σ τ} (h : ∀ i, OPar bk (σ i) (τ i)) :
      ∀ i, OPar bk (Subst.up σ i) (Subst.up τ i)
    | 0 => .var
    | _ + 1 => opar_ren (h _)
  induction h generalizing σ τ <;> simp only [sub, inst_sub]
  case delta hk hc => rw [erase_closed hc]; exact .delta hk hc
  case meet =>
    rcases qmin_map (sub τ) (fun _ => rfl) with e | e <;> rw [e] <;>
      constructor <;> apply_assumption <;> exact hs
  all_goals first | exact hs _ | apply OPar.split | apply OPar.miss | constructor
  all_goals first | assumption | (apply_assumption; (repeat apply U); exact hs)



end ErasedOrdinary

end

-- Source section: TypedHereditarySafety
section

open Quan Term ConversionDesign ErasedReduction EquationBridge ExecutableOrder


open ExposureResearch HeadSafeSupport ErasedOrdinary



namespace TypedHereditarySafety



def HereditaryHeadSafe (bk : Book) (a : Term) : Prop :=
  ∀ b, OPars bk a b → HeadSafe b



theorem hereditary_current (h : HereditaryHeadSafe bk a) : HeadSafe a := h a .refl



theorem hereditary_reduct (h : HereditaryHeadSafe bk a) (hp : OPars bk a b) :
    HereditaryHeadSafe bk b :=
  fun c hq => h c (opars_trans hp hq)



theorem typed_erased_reduct_safe (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ t T) (hp : OPars bk (erase t) u) : HeadSafe u := by
  obtain ⟨v, hv, he⟩ := opars_lift hp rfl
  rw [← he]
  exact head_safe_erase.2 (typed_head_safe (Revised.pars_sr wt ht hv))



theorem typed_erased_hereditary (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ t T) : HereditaryHeadSafe bk (erase t) :=
  fun _ hp => typed_erased_reduct_safe wt ht hp



end TypedHereditarySafety

end

-- Source section: OrdinarySupport
section

open Quan Term ConversionDesign ErasedReduction EquationBridge ExecutableOrder


open ExposureResearch HeadSafeSupport ErasedOrdinary TypedHereditarySafety



namespace OrdinarySupport



theorem hereditary_context_reflect (F : Term → Term)
    (lift : ∀ {a b}, OPar bk a b → OPar bk (F a) (F b))
    (project : ∀ a, HeadSafe (F a) → HeadSafe a)
    (h : HereditaryHeadSafe bk (F t)) : HereditaryHeadSafe bk t := by
  intro u hp
  exact project u (h _ (opars_map F lift hp))



theorem hereditary_parts2 (F : Term → Term → Term)
    (lift : ∀ {a a' b b'}, OPar bk a a' → OPar bk b b' →
      OPar bk (F a b) (F a' b'))
    (project : ∀ a b, HeadSafe (F a b) → HeadSafe a ∧ HeadSafe b)
    (h : HereditaryHeadSafe bk (F a b)) (ca : Canonical a) (cb : Canonical b) :
    HereditaryHeadSafe bk a ∧ HereditaryHeadSafe bk b := by
  constructor
  · exact hereditary_context_reflect (F · b) (fun hp => lift hp (opar_refl cb))
      (fun a hp => (project a b hp).1) h
  · exact hereditary_context_reflect (F a) (fun hp => lift (opar_refl ca) hp)
      (fun b hp => (project a b hp).2) h



theorem hereditary_parts3 (F : Term → Term → Term → Term)
    (lift : ∀ {a a' b b' c c'}, OPar bk a a' → OPar bk b b' → OPar bk c c' →
      OPar bk (F a b c) (F a' b' c'))
    (project : ∀ a b c, HeadSafe (F a b c) → HeadSafe a ∧ HeadSafe b ∧ HeadSafe c)
    (h : HereditaryHeadSafe bk (F a b c))
    (ca : Canonical a) (cb : Canonical b) (cc : Canonical c) :
    HereditaryHeadSafe bk a ∧ HereditaryHeadSafe bk b ∧ HereditaryHeadSafe bk c := by
  refine ⟨?_, ?_, ?_⟩
  · exact hereditary_context_reflect (F · b c)
      (fun hp => lift hp (opar_refl cb) (opar_refl cc))
      (fun a hp => (project a b c hp).1) h
  · exact hereditary_context_reflect (F a · c)
      (fun hp => lift (opar_refl ca) hp (opar_refl cc))
      (fun b hp => (project a b c hp).2.1) h
  · exact hereditary_context_reflect (F a b)
      (fun hp => lift (opar_refl ca) (opar_refl cb) hp)
      (fun c hp => (project a b c hp).2.2) h



theorem hereditary_lam (h : HereditaryHeadSafe bk (Lam Q1 f)) :
    HereditaryHeadSafe bk f :=
  hereditary_context_reflect (Lam Q1) OPar.lam (fun _ hp => hp) h



theorem hereditary_app (h : HereditaryHeadSafe bk (App Q1 f x))
    (cf : Canonical f) (cx : Canonical x) :
    HereditaryHeadSafe bk f ∧ HereditaryHeadSafe bk x :=
  hereditary_parts2 (App Q1) OPar.app (fun _ _ hp => hp.2.2) h cf cx



end OrdinarySupport

end

-- Source section: EtaCommutation
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta



open GlobalDiamond



namespace EtaCommutation



def Extend (x : Term) (σ : Subst) : Subst
  | 0 => x
  | i + 1 => σ i



theorem inst_sub_up : inst (sub (Subst.up σ) f) x = sub (Extend x σ) f := by
  simp only [inst, sub_sub]
  congr 1
  funext i
  cases i
  · rfl
  · simp only [Function.comp_apply, Subst.up, sub_ren]
    exact sub_var _



theorem extend_expansion :
    sub (Extend x σ) (App Q1 (ren Nat.succ f) (Var 0)) = App Q1 (sub σ f) x := by
  simp only [sub, sub_ren]
  rfl



theorem extend_canonical (cx : Canonical x) (cs : ∀ i, Canonical (σ i)) :
    ∀ i, Canonical (Extend x σ i)
  | 0 => cx
  | i + 1 => cs i



-- This is the induction claim for one fixed retained source term.
def Simulates (bk : Book) (a : Term) : Prop :=
  ∀ {b σ c}, BigEta a b → Canonical a → (∀ i, Canonical (σ i)) →
    HereditaryHeadSafe bk (sub σ a) → OPar bk (sub σ b) c →
    ∃ d, OPars bk (sub σ a) d ∧ BigEta d c



-- A retained function wrapper can be removed before any eliminator step.
-- The induction claim is used only for the strict subterm body.
theorem application_wrapper
    (ih : Simulates bk body)
    (he : BigEta body (App Q1 (ren Nat.succ f) (Var 0)))
    (cb : Canonical body) (cs : ∀ i, Canonical (σ i)) (cx : Canonical x)
    (hs : HereditaryHeadSafe bk (App Q1 (Lam Q1 (sub (Subst.up σ) body)) x))
    (hp : OPar bk (App Q1 (sub σ f) x) c) :
    ∃ d, OPars bk (App Q1 (Lam Q1 (sub (Subst.up σ) body)) x) d ∧ BigEta d c := by
  have cup : ∀ i, Canonical (Subst.up σ i) := by
    intro i
    cases i
    · rfl
    · simpa only [Canonical, Subst.up, erase_ren] using congrArg (ren Nat.succ) (cs _)
  have first : OPar bk (App Q1 (Lam Q1 (sub (Subst.up σ) body)) x)
      (sub (Extend x σ) body) := by
    simpa only [inst_sub_up] using OPar.beta (opar_refl (canonical_sub cb cup)) (opar_refl cx)
  have hs' := hereditary_reduct hs (OPars.step first .refl)
  have hp' : OPar bk (sub (Extend x σ) (App Q1 (ren Nat.succ f) (Var 0))) c := by
    simpa only [extend_expansion] using hp
  obtain ⟨d, hd, he'⟩ := ih he cb (extend_canonical cx cs) hs' hp'
  exact ⟨d, .step first hd, he'⟩



theorem application_congruence
    (ih : Simulates bk a) (he : BigEta a b)
    (ca : Canonical a) (cs : ∀ i, Canonical (σ i)) (cx : Canonical x)
    (hs : HereditaryHeadSafe bk (App Q1 (sub σ a) x))
    (pf : OPar bk (sub σ b) f') (px : OPar bk x x') :
    ∃ d, OPars bk (App Q1 (sub σ a) x) d ∧ BigEta d (App Q1 f' x') := by
  have cf := canonical_sub ca cs
  obtain ⟨d, hd, he'⟩ := ih he ca cs (hereditary_app hs cf cx).1 pf
  exact ⟨App Q1 d x', opars_map2 (App Q1) OPar.app hd (.step px .refl) cf cx,
    .app he' (big_eta_refl _)⟩



theorem application_function
    (ih : ∀ t, nodes t ≤ nodes a → Simulates bk t)
    (he : BigEta a b) (ca : Canonical a)
    (cs : ∀ i, Canonical (σ i)) (cx : Canonical x)
    (hs : HereditaryHeadSafe bk (App Q1 (sub σ a) x))
    (hp : OPar bk (App Q1 (sub σ b) x) c) :
    ∃ d, OPars bk (App Q1 (sub σ a) x) d ∧ BigEta d c := by
  have sim : Simulates bk a := ih a (Nat.le_refl _)
  have congr {f' x'} (pf : OPar bk (sub σ b) f') (px : OPar bk x x') :
      ∃ d, OPars bk (App Q1 (sub σ a) x) d ∧ BigEta d (App Q1 f' x') :=
    application_congruence sim he ca cs cx hs pf px
  have he0 := he
  cases he
  case var => exact ⟨_, .step hp .refl, big_eta_refl _⟩
  case eta body hb =>
    have cb : Canonical body := (Term.Lam.inj ca).2
    exact application_wrapper (ih body (by simp [nodes])) hb cb cs cx hs hp
  all_goals simp only [sub] at hp
  all_goals cases hp
  all_goals try { exact congr ‹_› ‹_› }
  case lam.beta =>
    rename_i f g he f' x' pf px
    have cf : Canonical f := (Term.Lam.inj ca).2
    have cup : ∀ i, Canonical (Subst.up σ i) := by
      intro i; cases i
      · rfl
      · simpa only [Canonical, Subst.up, erase_ren] using congrArg (ren Nat.succ) (cs _)
    have first : OPar bk (App Q1 (sub σ (Lam Q1 f)) x) (sub (Extend x σ) f) := by
      simpa only [sub, inst_sub_up] using OPar.beta (opar_refl (canonical_sub cf cup)) (opar_refl cx)
    have target : OPar bk (sub (Extend x σ) g) (inst f' x') := by
      rw [← inst_sub_up]
      exact opar_sub pf (σ := Subst.one x) (τ := Subst.one x') (by
        intro i; cases i; exact px; exact .var)
    obtain ⟨d, hd, he'⟩ := ih f (by simp [nodes]) he cf (extend_canonical cx cs)
      (hereditary_reduct hs (.step first .refl)) target
    exact ⟨d, .step first hd, he'⟩
  case prj.split =>
    rename_i h g he h' a a' b b' r pa pb ph
    have ch : Canonical h := Term.Prj.inj ca
    have csh : Canonical (sub σ h) := canonical_sub ch cs
    have hh : HereditaryHeadSafe bk (sub σ h) :=
      hereditary_context_reflect Prj OPar.prj (fun _ hp => hp)
        (hereditary_app hs (by simpa only [Canonical, sub, erase, Term.Prj.injEq] using csh) cx).1
    obtain ⟨d, hd, he'⟩ := ih h (by simp [nodes]) he ch cs hh ph
    have lift : OPars bk (App Q1 (sub σ (Prj h)) (Tup r a b))
        (App Q1 (Prj d) (Tup r a b)) :=
      opars_map (fun z => App Q1 (Prj z) (Tup r a b))
        (fun hp => OPar.app (.prj hp) (opar_refl cx)) hd
    exact ⟨_, opars_trans lift (.step (.split (opar_refl (opars_canonical hd csh)) pa pb) .refl),
      .app (.app he' (big_eta_refl _)) (big_eta_refl _)⟩
  case mat.hit =>
    rename_i h g m n k he hm ph
    have ⟨_, ch, cm⟩ := Term.Mat.inj ca
    have csh := canonical_sub ch cs
    have csm := canonical_sub cm cs
    have hf := (hereditary_app hs
      (by simp only [Canonical, sub, erase, Term.Mat.injEq]; exact ⟨True.intro,csh,csm⟩) cx).1
    have hh := (hereditary_parts2 (Mat k) OPar.mat (fun _ _ hp => hp) hf csh csm).1
    obtain ⟨d, hd, he'⟩ := ih h (by simp only [nodes]; omega) he ch cs hh ph
    have lift : OPars bk (App Q1 (sub σ (Mat k h m)) (Lab k))
        (App Q1 (Mat k d (sub σ m)) (Lab k)) :=
      opars_map (fun z => App Q1 (Mat k z (sub σ m)) (Lab k))
        (fun hp => .app (.mat hp (opar_refl csm)) .lab) hd
    exact ⟨d, opars_trans lift (.step (.hit (opar_refl (opars_canonical hd csh))) .refl), he'⟩
  case mat.miss =>
    rename_i h g m n k he hm j m' hn pm
    have ⟨_, ch, cm⟩ := Term.Mat.inj ca
    have csh := canonical_sub ch cs
    have csm := canonical_sub cm cs
    have hf := (hereditary_app hs
      (by simp only [Canonical, sub, erase, Term.Mat.injEq]; exact ⟨True.intro,csh,csm⟩) cx).1
    have hh := (hereditary_parts2 (Mat k) OPar.mat (fun _ _ hp => hp) hf csh csm).2
    obtain ⟨d, hd, he'⟩ := ih m (by simp only [nodes]; omega) hm cm cs hh pm
    have lift : OPars bk (App Q1 (sub σ (Mat k h m)) (Lab j))
        (App Q1 (Mat k (sub σ h) d) (Lab j)) :=
      opars_map (fun z => App Q1 (Mat k (sub σ h) z) (Lab j))
        (fun hp => .app (.mat (opar_refl csh) hp) .lab) hd
    exact ⟨_, opars_trans lift (.step (.miss hn (opar_refl (opars_canonical hd csm))) .refl),
      .app he' .lab⟩



end EtaCommutation

end

-- Source section: BigEtaInversion
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch ContextualEta



namespace BigEtaInversion



theorem tuple_source (h : BigEta a (Tup q b c)) (hn : NonLambda a) :
    ∃ x y, a = Tup q x y ∧ BigEta x b ∧ BigEta y c := by
  cases h with
  | tup hb hc => exact ⟨_, _, rfl, hb, hc⟩
  | eta h => exact (hn _ _ rfl).elim



theorem label_source (h : BigEta a (Lab k)) (hn : NonLambda a) :
    a = Lab k := by
  cases h with
  | lab => rfl
  | eta h => exact (hn _ _ rfl).elim



theorem proof_source (h : BigEta a Rfl) (hn : NonLambda a) :
    a = Rfl := by
  cases h with
  | rfl => rfl
  | eta h => exact (hn _ _ rfl).elim



end BigEtaInversion

end

-- Source section: SimulationArgument
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta BigEtaInversion



namespace EtaCommutation



theorem argument_reduction
    (ih : Simulates bk x) (he : BigEta x y)
    (cx : Canonical x) (cs : ∀ i, Canonical (σ i)) (cf : Canonical F)
    (hs : HereditaryHeadSafe bk (App Q1 F (sub σ x)))
    (hp : OPar bk (sub σ y) z) :
    ∃ d, OPars bk (App Q1 F (sub σ x)) (App Q1 F d) ∧
      Canonical d ∧ BigEta d z ∧ HereditaryHeadSafe bk (App Q1 F d) := by
  have hx := (hereditary_app hs cf (canonical_sub cx cs)).2
  obtain ⟨d, hd, he'⟩ := ih he cx cs hx hp
  have hd' := opars_map (App Q1 F) (fun h => OPar.app (opar_refl cf) h) hd
  exact ⟨d, hd', opars_canonical hd (canonical_sub cx cs), he', hereditary_reduct hs hd'⟩



end EtaCommutation

end

-- Source section: SimulationConstructors
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta



namespace EtaCommutation



theorem canonical_up (cs : ∀ i, Canonical (σ i)) :
    ∀ i, Canonical (Subst.up σ i)
  | 0 => rfl
  | i + 1 => by simpa only [Canonical, Subst.up, erase_ren] using congrArg (ren Nat.succ) (cs i)



theorem simulates_typ (ih : Simulates bk q) : Simulates bk (Typ q) := by
  intro b σ c he ca cs hs hp
  cases he with
  | typ he =>
    simp only [sub] at hs hp ⊢
    have cq : Canonical q := by simpa only [Canonical, erase, Typ.injEq] using ca
    have hq := hereditary_context_reflect Typ OPar.typ (fun _ h => h.2) hs
    cases hp with
    | typ hp =>
      obtain ⟨d, hd, he⟩ := ih he cq cs hq hp
      exact ⟨Typ d, opars_map Typ OPar.typ hd, .typ he⟩



theorem simulates_prj (ih : Simulates bk h) : Simulates bk (Prj h) := by
  intro b σ c he ca cs hs hp
  cases he with
  | prj he =>
    simp only [sub] at hs hp ⊢
    have ch : Canonical h := by simpa only [Canonical, erase, Prj.injEq] using ca
    have hh := hereditary_context_reflect Prj OPar.prj (fun _ h => h) hs
    cases hp with
    | prj hp =>
      obtain ⟨d, hd, he⟩ := ih he ch cs hh hp
      exact ⟨Prj d, opars_map Prj OPar.prj hd, .prj he⟩



theorem simulates_all (ihA : Simulates bk A) (ihB : Simulates bk B) : Simulates bk (All q A B) := by
  intro b σ c he ca cs hs hp
  cases he with
  | all heA heB =>
    simp only [sub] at hs hp ⊢
    have cAB : Canonical A ∧ Canonical B := by
      simpa only [Canonical, erase, All.injEq, true_and] using ca
    have cA := canonical_sub cAB.1 cs
    have cB := canonical_sub cAB.2 (canonical_up cs)
    have ⟨hA, hB⟩ := hereditary_parts2 (All q) OPar.all (fun _ _ h => h) hs cA cB
    cases hp with
    | all hpA hpB =>
      obtain ⟨dA, hdA, heA⟩ := ihA heA cAB.1 cs hA hpA
      obtain ⟨dB, hdB, heB⟩ := ihB heB cAB.2 (canonical_up cs) hB hpB
      exact ⟨All q dA dB, opars_map2 (All q) OPar.all hdA hdB cA cB, .all heA heB⟩



theorem simulates_sig (ihA : Simulates bk A) (ihB : Simulates bk B) : Simulates bk (Sig q A B) := by
  intro b σ c he ca cs hs hp
  cases he with
  | sig heA heB =>
    simp only [sub] at hs hp ⊢
    have cAB : Canonical A ∧ Canonical B := by
      simpa only [Canonical, erase, Sig.injEq, true_and] using ca
    have cA := canonical_sub cAB.1 cs
    have cB := canonical_sub cAB.2 (canonical_up cs)
    have ⟨hA, hB⟩ := hereditary_parts2 (Sig q) OPar.sig (fun _ _ h => h) hs cA cB
    cases hp with
    | sig hpA hpB =>
      obtain ⟨dA, hdA, heA⟩ := ihA heA cAB.1 cs hA hpA
      obtain ⟨dB, hdB, heB⟩ := ihB heB cAB.2 (canonical_up cs) hB hpB
      exact ⟨Sig q dA dB, opars_map2 (Sig q) OPar.sig hdA hdB cA cB, .sig heA heB⟩



theorem simulates_tup (ihA : Simulates bk A) (ihB : Simulates bk B) : Simulates bk (Tup q A B) := by
  intro b σ c he ca cs hs hp
  cases he with
  | tup heA heB =>
    simp only [sub] at hs hp ⊢
    have cAB : Canonical A ∧ Canonical B := by
      simpa only [Canonical, erase, Tup.injEq, true_and] using ca
    have cA := canonical_sub cAB.1 cs
    have cB := canonical_sub cAB.2 (cs)
    have ⟨hA, hB⟩ := hereditary_parts2 (Tup q) OPar.tup (fun _ _ h => h) hs cA cB
    cases hp with
    | tup hpA hpB =>
      obtain ⟨dA, hdA, heA⟩ := ihA heA cAB.1 cs hA hpA
      obtain ⟨dB, hdB, heB⟩ := ihB heB cAB.2 (cs) hB hpB
      exact ⟨Tup q dA dB, opars_map2 (Tup q) OPar.tup hdA hdB cA cB, .tup heA heB⟩



theorem simulates_mat (ihA : Simulates bk A) (ihB : Simulates bk B) : Simulates bk (Mat q A B) := by
  intro b σ c he ca cs hs hp
  cases he with
  | mat heA heB =>
    simp only [sub] at hs hp ⊢
    have cAB : Canonical A ∧ Canonical B := by
      simpa only [Canonical, erase, Mat.injEq, true_and] using ca
    have cA := canonical_sub cAB.1 cs
    have cB := canonical_sub cAB.2 (cs)
    have ⟨hA, hB⟩ := hereditary_parts2 (Mat q) OPar.mat (fun _ _ h => h) hs cA cB
    cases hp with
    | mat hpA hpB =>
      obtain ⟨dA, hdA, heA⟩ := ihA heA cAB.1 cs hA hpA
      obtain ⟨dB, hdB, heB⟩ := ihB heB cAB.2 (cs) hB hpB
      exact ⟨Mat q dA dB, opars_map2 (Mat q) OPar.mat hdA hdB cA cB, .mat heA heB⟩



theorem simulates_eql (iha : Simulates bk a) (ihb : Simulates bk b) (ihT : Simulates bk T) :
    Simulates bk (Eql a b T) := by
  intro u σ c he ca cs hs hp
  cases he with
  | eql hea heb heT =>
    simp only [sub] at hs hp ⊢
    have cabT : Canonical a ∧ Canonical b ∧ Canonical T := by
      simpa only [Canonical, erase, Eql.injEq] using ca
    have ca := canonical_sub cabT.1 cs
    have cb := canonical_sub cabT.2.1 cs
    have cT := canonical_sub cabT.2.2 cs
    have ⟨ha, hb, hT⟩ := hereditary_parts3 Eql OPar.eql (fun _ _ _ h => h) hs ca cb cT
    cases hp with
    | eql hpa hpb hpT =>
      obtain ⟨da, hda, hea⟩ := iha hea cabT.1 cs ha hpa
      obtain ⟨db, hdb, heb⟩ := ihb heb cabT.2.1 cs hb hpb
      obtain ⟨dT, hdT, heT⟩ := ihT heT cabT.2.2 cs hT hpT
      exact ⟨Eql da db dT, opars_map3 Eql OPar.eql hda hdb hdT ca cb cT, .eql hea heb heT⟩



theorem simulates_ann (ihx : Simulates bk x) (ihT : Simulates bk T) :
    Simulates bk (Ann x T) := by
  intro b σ c he ca cs hs hp
  cases he with
  | ann hex heT =>
    simp only [sub] at hs hp ⊢
    have cxT : Canonical x ∧ Canonical T := by
      simpa only [Canonical, erase, Ann.injEq] using ca
    have cx := canonical_sub cxT.1 cs
    have cT := canonical_sub cxT.2 cs
    have ⟨hx, hT⟩ := hereditary_parts2 Ann OPar.ann (fun _ _ h => h) hs cx cT
    cases hp with
    | ann hpx hpT =>
      obtain ⟨dx, hdx, hex⟩ := ihx hex cxT.1 cs hx hpx
      obtain ⟨dT, hdT, heT⟩ := ihT heT cxT.2 cs hT hpT
      exact ⟨Ann dx dT, opars_map2 Ann OPar.ann hdx hdT cx cT, .ann hex heT⟩
    | unann hpx =>
      obtain ⟨dx, hdx, hex⟩ := ihx hex cxT.1 cs hx hpx
      exact ⟨dx, .step (.unann (opar_refl cx)) hdx, hex⟩



theorem simulates_let (ihv : Simulates bk v) (ihf : Simulates bk f) :
    Simulates bk (Let q v f) := by
  intro b σ c he ca cs hs hp
  cases he with
  | lett hev hef =>
    simp only [sub] at hs hp ⊢
    have cvf : Canonical v ∧ Canonical f := by
      simpa only [Canonical, erase, Let.injEq, true_and] using ca
    have cv := canonical_sub cvf.1 cs
    have cf := canonical_sub cvf.2 (canonical_up cs)
    have ⟨hv, hf⟩ := hereditary_parts2 (Let q) OPar.lett (fun _ _ h => h) hs cv cf
    cases hp with
    | lett hpv hpf =>
      obtain ⟨dv, hdv, hev⟩ := ihv hev cvf.1 cs hv hpv
      obtain ⟨df, hdf, hef⟩ := ihf hef cvf.2 (canonical_up cs) hf hpf
      exact ⟨Let q dv df, opars_map2 (Let q) OPar.lett hdv hdf cv cf, .lett hev hef⟩
    | unlet hpv hpf =>
      obtain ⟨dv, hdv, hev⟩ := ihv hev cvf.1 cs hv hpv
      obtain ⟨df, hdf, hef⟩ := ihf hef cvf.2 (canonical_up cs) hf hpf
      exact ⟨inst df dv, opars_trans (opars_map2 (Let q) OPar.lett hdv hdf cv cf)
        (.step (.unlet (opar_refl (opars_canonical hdv cv))
          (opar_refl (opars_canonical hdf cf))) .refl), big_eta_inst hef hev⟩



theorem simulates_lam (ih : Simulates bk f) : Simulates bk (Lam q f) := by
  intro b σ c he ca cs hs hp
  have cq : Q1 = q ∧ Canonical f := by
    simpa only [Canonical, erase, Lam.injEq] using ca
  obtain ⟨rfl, cf⟩ := cq
  simp only [sub] at hs ⊢
  have hf := hereditary_lam hs
  cases he with
  | lam he =>
    simp only [sub] at hp
    cases hp with
    | lam hp =>
      obtain ⟨d, hd, he⟩ := ih he cf (canonical_up cs) hf hp
      exact ⟨Lam Q1 d, opars_map (Lam Q1) OPar.lam hd, .lam he⟩
  | eta he =>
    have body_step : OPar bk (sub (Subst.up σ) (App Q1 (ren Nat.succ b) (Var 0)))
        (App Q1 (ren Nat.succ c) (Var 0)) := by
      simpa only [sub, sub_succ, Subst.up] using OPar.app (opar_ren (r := Nat.succ) hp) OPar.var
    obtain ⟨d, hd, he⟩ := ih he cf (canonical_up cs) hf body_step
    exact ⟨Lam Q1 d, opars_map (Lam Q1) OPar.lam hd, .eta he⟩



theorem simulates_fixed (h : ∀ {b}, BigEta a b → a = b) : Simulates bk a := by
  intro b σ c he _ _ _ hp
  cases h he
  exact ⟨c, .step hp .refl, big_eta_refl _⟩



theorem simulates_var : Simulates bk (Var i) := simulates_fixed (by intro _ h; cases h; rfl)


theorem simulates_ref : Simulates bk (Ref k) := simulates_fixed (by intro _ h; cases h; rfl)


theorem simulates_enu : Simulates bk (Enu ks) := simulates_fixed (by intro _ h; cases h; rfl)


theorem simulates_lab : Simulates bk (Lab k) := simulates_fixed (by intro _ h; cases h; rfl)


theorem simulates_efq : Simulates bk Efq := simulates_fixed (by intro _ h; cases h; rfl)


theorem simulates_rfl : Simulates bk Rfl := simulates_fixed (by intro _ h; cases h; rfl)



end EtaCommutation

end

-- Source section: BigEtaSafety
section

open Quan Term ConversionDesign ErasedReduction EquationBridge ExecutableOrder


open ExposureResearch HeadSafeSupport ErasedOrdinary TypedHereditarySafety


open OrdinarySupport ContextualEta



namespace BigEtaSafety



def Extend (x : Term) (σ : Subst) : Subst
  | 0 => x
  | i + 1 => σ i



theorem inst_sub_up : inst (sub (Subst.up σ) f) x = sub (Extend x σ) f := by
  simp only [inst, sub_sub]
  congr 1
  funext i
  cases i
  · rfl
  · simp only [Function.comp_apply, Subst.up, sub_ren]
    exact sub_var _



theorem extend_expansion :
    sub (Extend x σ) (App Q1 (ren Nat.succ f) (Var 0)) = App Q1 (sub σ f) x := by
  simp only [sub, sub_ren]
  rfl



theorem extend_canonical (cx : Canonical x) (cs : ∀ i, Canonical (σ i)) :
    ∀ i, Canonical (Extend x σ i)
  | 0 => cx
  | i + 1 => cs i



theorem up_canonical (cs : ∀ i, Canonical (σ i)) :
    ∀ i, Canonical (Subst.up σ i) := by
  intro i
  cases i
  · rfl
  · simpa only [Canonical, Subst.up, erase_ren] using congrArg (ren Nat.succ) (cs _)



theorem sub_nonlambda (h : BigEta a b) (hn : NonLambda (sub σ a)) :
    NonLambda (sub σ b) :=
  (big_eta_nonlambda (big_eta_sub h (fun _ => big_eta_refl _)) hn).1



-- The second and third claims support the application case of the first claim.
theorem sub_safety (he : BigEta a b) :
    ∀ σ, Canonical a → (∀ i, Canonical (σ i)) →
    (HereditaryHeadSafe bk (sub σ a) → HeadSafe (sub σ b)) ∧
    (HereditaryHeadSafe bk (sub σ a) → CallableShape (sub σ a) → CallableShape (sub σ b)) ∧
    (∀ x, Canonical x → HereditaryHeadSafe bk (App Q1 (sub σ a) x) →
      (sub σ b).former ∈ [7, 8] → NonLambda x) := by
  induction he
  all_goals intro σ ca cs
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | exact fun hh => hereditary_current hh
    | exact fun _ h => h
    | exact fun _ _ hh h => (hereditary_current hh).2.1 h
    | solve | intro x _ _ h; simp [former] at h
    | skip
  all_goals simp only [Canonical, erase, Term.Ann.injEq, Term.Let.injEq,
    Term.Typ.injEq, Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq,
    Term.Sig.injEq, Term.Tup.injEq, Term.Prj.injEq, Term.Mat.injEq, Term.Eql.injEq,
    Term.Rwt.injEq, true_and] at ca
  all_goals simp only [sub] at *
  case ann.refine_1 h g ihx ihT =>
    intro hh
    have hp := hereditary_parts2 Ann OPar.ann (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 cs)
    exact ⟨(ihx σ ca.1 cs).1 hp.1, (ihT σ ca.2 cs).1 hp.2⟩
  case lett.refine_1 h g ihv ihf =>
    intro hh
    have hp := hereditary_parts2 (Let _) OPar.lett (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 (up_canonical cs))
    exact ⟨(ihv σ ca.1 cs).1 hp.1, (ihf (Subst.up σ) ca.2 (up_canonical cs)).1 hp.2⟩
  case typ.refine_1 h ih =>
    intro hh
    have hp := hereditary_context_reflect Typ OPar.typ (fun _ h => h.2) hh
    exact ⟨sub_nonlambda h (hereditary_current hh).1, (ih σ ca cs).1 hp⟩
  case min.refine_1 h g iha ihb =>
    intro hh
    have hp := hereditary_parts2 Term.Min OPar.min (fun _ _ h => h.2.2) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 cs)
    exact ⟨sub_nonlambda h (hereditary_current hh).1,
      sub_nonlambda g (hereditary_current hh).2.1,
      (iha σ ca.1 cs).1 hp.1, (ihb σ ca.2 cs).1 hp.2⟩
  case all.refine_1 h g ihA ihB =>
    intro hh
    have hp := hereditary_parts2 (All _) OPar.all (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 (up_canonical cs))
    exact ⟨(ihA σ ca.1 cs).1 hp.1, (ihB (Subst.up σ) ca.2 (up_canonical cs)).1 hp.2⟩
  case sig.refine_1 h g ihA ihB =>
    intro hh
    have hp := hereditary_parts2 (Sig _) OPar.sig (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 (up_canonical cs))
    exact ⟨(ihA σ ca.1 cs).1 hp.1, (ihB (Subst.up σ) ca.2 (up_canonical cs)).1 hp.2⟩
  case lam.refine_1 h ih =>
    rcases ca with ⟨rfl, ca⟩
    intro hh
    exact (ih (Subst.up σ) ca (up_canonical cs)).1 (hereditary_lam hh)
  case tup.refine_1 h g iha ihb =>
    intro hh
    have hp := hereditary_parts2 (Tup _) OPar.tup (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 cs)
    exact ⟨(iha σ ca.1 cs).1 hp.1, (ihb σ ca.2 cs).1 hp.2⟩
  case mat.refine_1 h g iha ihb =>
    intro hh
    have hp := hereditary_parts2 (Mat _) OPar.mat (fun _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2 cs)
    exact ⟨(iha σ ca.1 cs).1 hp.1, (ihb σ ca.2 cs).1 hp.2⟩
  case prj.refine_1 h ih =>
    intro hh
    exact (ih σ ca cs).1 (hereditary_context_reflect Prj OPar.prj (fun _ h => h) hh)
  case eql.refine_1 h g j iha ihb ihT =>
    intro hh
    have hp := hereditary_parts3 Eql OPar.eql (fun _ _ _ h => h) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2.1 cs) (canonical_sub ca.2.2 cs)
    exact ⟨(iha σ ca.1 cs).1 hp.1, (ihb σ ca.2.1 cs).1 hp.2.1,
      (ihT σ ca.2.2 cs).1 hp.2.2⟩
  case rwt.refine_1 h g j ihe ihP ihf =>
    intro hh
    have hp := hereditary_parts3 Rwt OPar.rwt (fun _ _ _ h => h.2) hh
      (canonical_sub ca.1 cs) (canonical_sub ca.2.1 (up_canonical (up_canonical cs))) (canonical_sub ca.2.2 cs)
    exact ⟨sub_nonlambda h (hereditary_current hh).1, (ihe σ ca.1 cs).1 hp.1,
      (ihP (Subst.up (Subst.up σ)) ca.2.1 (up_canonical (up_canonical cs))).1 hp.2.1, (ihf σ ca.2.2 cs).1 hp.2.2⟩
  case app.refine_1 h g ihf ihx =>
    rcases ca with ⟨rfl, cf, cx⟩
    intro hh
    have hp := hereditary_app hh (canonical_sub cf cs) (canonical_sub cx cs)
    exact ⟨(ihf σ cf cs).2.1 hp.1 (hereditary_current hh).1,
      fun hprim => sub_nonlambda g ((ihf σ cf cs).2.2 _ (canonical_sub cx cs) hh hprim),
      (ihf σ cf cs).1 hp.1, (ihx σ cx cs).1 hp.2⟩
  case eta.refine_1 body f h ih =>
    intro hh
    have hp := (ih (Subst.up σ) ca (up_canonical cs)).1 (hereditary_lam hh)
    simp only [sub_succ, Subst.up] at hp
    exact head_safe_ren.1 hp.2.2.1
  case eta.refine_2 body f h ih =>
    intro hh _
    have hp := (ih (Subst.up σ) ca (up_canonical cs)).1 (hereditary_lam hh)
    simp only [sub_succ, Subst.up] at hp
    exact callable_ren.1 hp.1
  case eta.refine_3 body f h ih =>
    intro x cx hh hprim
    have first : OPar bk (App Q1 (Lam Q1 (sub (Subst.up σ) body)) x)
        (sub (Extend x σ) body) := by
      simpa only [inst_sub_up] using
        OPar.beta (opar_refl (canonical_sub ca (up_canonical cs))) (opar_refl cx)
    have hp := (ih (Extend x σ) ca (extend_canonical cx cs)).1
      (hereditary_reduct hh (.step first .refl))
    change HeadSafe (sub (Extend x σ) (App Q1 (ren Nat.succ f) (Var 0))) at hp
    rw [extend_expansion] at hp
    exact hp.2.1 hprim



end BigEtaSafety

end

-- Source section: SimulationEliminators
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta BigEtaInversion



namespace EtaCommutation



theorem qmin_formula (a b : Term) : qmin a b =
    if a = Lab "Q2" then b else if b = Lab "Q2" then a else
    if a = Lab "Q0" then Lab "Q0" else if b = Lab "Q0" then Lab "Q0" else
    if a = Lab "Q1" ∧ b = Lab "Q1" then Lab "Q1" else Term.Min a b := by
  unfold qmin
  split <;> simp_all



theorem big_eta_label_iff (h : BigEta a b) (hn : NonLambda a) :
    a = Lab k ↔ b = Lab k := by
  constructor
  · rintro rfl
    cases h
    rfl
  · rintro rfl
    exact label_source h hn



theorem big_eta_qmin (ha : BigEta a a') (hb : BigEta b b')
    (na : NonLambda a) (nb : NonLambda b) :
    BigEta (qmin a b) (qmin a' b') := by
  rw [qmin_formula, qmin_formula]
  simp only [big_eta_label_iff ha na, big_eta_label_iff hb nb]
  repeat' first | exact ha | exact hb | exact .lab | exact .min ha hb | split




theorem simulates_min (iha : Simulates bk a) (ihb : Simulates bk b) :
    Simulates bk (Term.Min a b) := by
  intro u σ c he ca cs hs hp
  cases he with
  | min hea heb =>
    simp only [sub] at hs hp ⊢
    have cab : Canonical a ∧ Canonical b := by
      simpa only [Canonical, erase, Term.Min.injEq] using ca
    have ca := canonical_sub cab.1 cs
    have cb := canonical_sub cab.2 cs
    have ⟨ha, hb⟩ := hereditary_parts2 Term.Min OPar.min (fun _ _ h => h.2.2) hs ca cb
    cases hp with
    | min hpa hpb =>
      obtain ⟨da, hda, hea⟩ := iha hea cab.1 cs ha hpa
      obtain ⟨db, hdb, heb⟩ := ihb heb cab.2 cs hb hpb
      exact ⟨Term.Min da db, opars_map2 Term.Min OPar.min hda hdb ca cb, .min hea heb⟩
    | meet hpa hpb =>
      obtain ⟨da, hda, hea⟩ := iha hea cab.1 cs ha hpa
      obtain ⟨db, hdb, heb⟩ := ihb heb cab.2 cs hb hpb
      have hd := opars_map2 Term.Min OPar.min hda hdb ca cb
      have hsd := hereditary_current (hereditary_reduct hs hd)
      exact ⟨qmin da db, opars_trans hd
        (.step (.meet (opar_refl (opars_canonical hda ca))
          (opar_refl (opars_canonical hdb cb))) .refl),
        big_eta_qmin hea heb hsd.1 hsd.2.1⟩



theorem simulates_rwt (ihe : Simulates bk e) (ihP : Simulates bk P) (ihf : Simulates bk f) :
    Simulates bk (Rwt e P f) := by
  intro u σ c he ca cs hs hp
  cases he with
  | rwt hee heP hef =>
    simp only [sub] at hs hp ⊢
    have cePf : Canonical e ∧ Canonical P ∧ Canonical f := by
      simpa only [Canonical, erase, Rwt.injEq] using ca
    have ce := canonical_sub cePf.1 cs
    have cP := canonical_sub cePf.2.1 (canonical_up (canonical_up cs))
    have cf := canonical_sub cePf.2.2 cs
    have ⟨hse, hsP, hsf⟩ := hereditary_parts3 Rwt OPar.rwt (fun _ _ _ h => h.2) hs ce cP cf
    generalize hey : sub σ _ = Y at hp
    cases hp with
    | rwt hpe hpP hpf =>
      obtain ⟨de, hde, hee⟩ := ihe hee cePf.1 cs hse (hey ▸ hpe)
      obtain ⟨dP, hdP, heP⟩ := ihP heP cePf.2.1 (canonical_up (canonical_up cs)) hsP hpP
      obtain ⟨df, hdf, hef⟩ := ihf hef cePf.2.2 cs hsf hpf
      exact ⟨Rwt de dP df, opars_map3 Rwt OPar.rwt hde hdP hdf ce cP cf, .rwt hee heP hef⟩
    | cast hpf =>
      have hep := big_eta_sub hee (fun i => big_eta_refl (σ i))
      rw [hey] at hep
      have ep := proof_source hep (hereditary_current hs).1
      rw [ep]
      obtain ⟨df, hdf, hef⟩ := ihf hef cePf.2.2 cs hsf hpf
      exact ⟨df, .step (.cast (opar_refl cf)) hdf, hef⟩



end EtaCommutation

end

-- Source section: FullEtaSimulation
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch GlobalDiamond


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta BigEtaInversion



namespace EtaCommutation



theorem simulates_app
    (ihf : ∀ t, nodes t ≤ nodes f → Simulates bk t)
    (ihx : Simulates bk x) : Simulates bk (App q f x) := by
  intro b σ c he ca cs hs hp
  have ⟨hq, cf, cx⟩ := Term.App.inj ca
  subst q
  cases he with
  | app hf hx =>
    rename_i g y
    simp only [sub] at hp hs ⊢
    generalize hy : sub σ y = Y at hp
    have move {z} (hp : OPar bk Y z) :=
      argument_reduction ihx hx cx cs (canonical_sub cf cs) hs (hy ▸ hp)
    have consume {z c} (cz : Canonical z)
        (hz : HereditaryHeadSafe bk (App Q1 (sub σ f) z))
        (hp : OPar bk (App Q1 (sub σ g) z) c) :=
      application_function ihf hf cf cs cz hz hp
    have guard {z} (cz : Canonical z)
        (hz : HereditaryHeadSafe bk (App Q1 (sub σ f) z))
        (hg : (sub σ g).former ∈ [7,8]) : NonLambda z :=
      (BigEtaSafety.sub_safety hf σ cf cs).2.2 z cz hz hg
    generalize hg : sub σ g = G at hp
    cases hp with
    | app pf px =>
      obtain ⟨d, hd, cd, he, hsd⟩ := move px
      obtain ⟨e, pe, ee⟩ := consume cd hsd (hg ▸ OPar.app pf (opar_refl cd))
      exact ⟨e, opars_trans hd pe, big_eta_trans ee (.app (big_eta_refl _) he)⟩
    | beta pf px =>
      obtain ⟨d, hd, cd, he, hsd⟩ := move px
      obtain ⟨e, pe, ee⟩ := consume cd hsd (hg ▸ OPar.beta pf (opar_refl cd))
      exact ⟨e, opars_trans hd pe, big_eta_trans ee (big_eta_inst (big_eta_refl _) he)⟩
    | split ph pa pb =>
      obtain ⟨d, hd, cd, he, hsd⟩ := move (.tup pa pb)
      have hn := guard cd hsd (by rw [hg]; simp [former])
      obtain ⟨a, b, rfl, hea, heb⟩ := tuple_source he hn
      have cc : Canonical a ∧ Canonical b := by
        simpa only [Canonical, erase, Term.Tup.injEq, true_and] using cd
      obtain ⟨e, pe, ee⟩ := consume cd hsd
        (hg ▸ OPar.split ph (opar_refl cc.1) (opar_refl cc.2))
      exact ⟨e, opars_trans hd pe,
        big_eta_trans ee (.app (.app (big_eta_refl _) hea) heb)⟩
    | hit ph =>
      obtain ⟨d, hd, cd, he, hsd⟩ := move .lab
      have hn := guard cd hsd (by rw [hg]; simp [former])
      cases label_source he hn
      obtain ⟨e, pe, ee⟩ := consume cd hsd (hg ▸ OPar.hit ph)
      exact ⟨e, opars_trans hd pe, ee⟩
    | miss hn pm =>
      obtain ⟨d, hd, cd, he, hsd⟩ := move .lab
      have hnl := guard cd hsd (by rw [hg]; simp [former])
      cases label_source he hnl
      obtain ⟨e, pe, ee⟩ := consume cd hsd (hg ▸ OPar.miss hn pm)
      exact ⟨e, opars_trans hd pe, ee⟩



theorem simulates    (a : Term) : Simulates bk a := by
  induction a using (measure nodes).wf.induction with
  | h a ih =>
    cases a with
    | Var _ => exact simulates_var
    | Ref _ => exact simulates_ref
    | Enu _ => exact simulates_enu
    | Lab _ => exact simulates_lab
    | Efq => exact simulates_efq
    | Rfl => exact simulates_rfl
    | Ann x T => exact simulates_ann (ih x (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih T (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Let q v f => exact simulates_let (ih v (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih f (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Typ q => exact simulates_typ (ih q (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Min a b => exact simulates_min (ih a (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih b (by change nodes _ < nodes _; simp only [nodes]; omega))
    | All q A B => exact simulates_all (ih A (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih B (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Lam q f => exact simulates_lam (ih f (by change nodes _ < nodes _; simp only [nodes]; omega))
    | App q f x =>
      apply simulates_app
      · intro t ht
        exact ih t (by change nodes _ < nodes _; simp only [nodes]; omega)
      · exact ih x (by change nodes _ < nodes _; simp only [nodes]; omega)
    | Sig q A B => exact simulates_sig (ih A (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih B (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Tup q a b => exact simulates_tup (ih a (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih b (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Prj h => exact simulates_prj (ih h (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Mat k h m => exact simulates_mat (ih h (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih m (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Eql a b T => exact simulates_eql (ih a (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih b (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih T (by change nodes _ < nodes _; simp only [nodes]; omega))
    | Rwt e P f => exact simulates_rwt (ih e (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih P (by change nodes _ < nodes _; simp only [nodes]; omega)) (ih f (by change nodes _ < nodes _; simp only [nodes]; omega))



theorem full_eta_ordinary (he : BigEta a b) (ca : Canonical a)
    (hs : HereditaryHeadSafe bk a) (hp : OPar bk b c) :
    ∃ d, OPars bk a d ∧ BigEta d c := by
  simpa only [sub_var] using simulates a he ca (σ := Var) (fun _ => rfl)
    (by simpa only [sub_var] using hs) (by simpa only [sub_var] using hp)



end EtaCommutation

end

-- Source section: MixedReduction
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch ErasedOrdinary



namespace MixedReduction



inductive Step (bk : Book) : Term → Term → Prop
  | ordinary : OPar bk t u → Step bk t u
  | eta : ContextualEta.Step t u → Step bk t u



inductive Steps (bk : Book) : Term → Term → Prop
  | refl : Steps bk t t
  | step : Step bk t u → Steps bk u v → Steps bk t v



theorem single (h : Step bk t u) : Steps bk t u := .step h .refl



theorem steps_trans (h : Steps bk t u) (g : Steps bk u v) : Steps bk t v := by
  induction h with
  | refl => exact g
  | step h _ ih => exact .step h (ih g)



theorem step_canonical (h : Step bk t u) (hc : Canonical t) : Canonical u := by
  cases h with
  | ordinary h => exact opar_canonical h
  | eta h => exact ContextualEta.step_canonical h hc



theorem steps_canonical (h : Steps bk t u) (hc : Canonical t) : Canonical u := by
  induction h with
  | refl => exact hc
  | step h _ ih => exact ih (step_canonical h hc)



theorem steps_map (F : Term → Term)
    (ho : ∀ {t u}, OPar bk t u → OPar bk (F t) (F u))
    (he : ∀ {t u}, ContextualEta.Step t u → ContextualEta.Step (F t) (F u))
    (h : Steps bk t u) : Steps bk (F t) (F u) := by
  induction h with
  | refl => exact .refl
  | step h _ ih =>
    apply Steps.step (u := F _)
    · cases h with
      | ordinary h => exact .ordinary (ho h)
      | eta h => exact .eta (he h)
    · exact ih



theorem steps_map2 (F : Term → Term → Term)
    (ho : ∀ {a a' b b'}, OPar bk a a' → OPar bk b b' → OPar bk (F a b) (F a' b'))
    (hl : ∀ {t u} a, ContextualEta.Step t u → ContextualEta.Step (F t a) (F u a))
    (hr : ∀ {t u} a, ContextualEta.Step t u → ContextualEta.Step (F a t) (F a u))
    (ha : Steps bk a a') (hb : Steps bk b b')
    (ca : Canonical a) (cb : Canonical b) : Steps bk (F a b) (F a' b') :=
  steps_trans (steps_map (F · b) (fun h => ho h (opar_refl cb)) (hl b) ha)
    (steps_map (F a') (fun h => ho (opar_refl (steps_canonical ha ca)) h) (hr a') hb)



theorem steps_map3 (F : Term → Term → Term → Term)
    (ho : ∀ {a a' b b' c c'}, OPar bk a a' → OPar bk b b' → OPar bk c c' →
      OPar bk (F a b c) (F a' b' c'))
    (h1 : ∀ {t u} a b, ContextualEta.Step t u → ContextualEta.Step (F t a b) (F u a b))
    (h2 : ∀ {t u} a b, ContextualEta.Step t u → ContextualEta.Step (F a t b) (F a u b))
    (h3 : ∀ {t u} a b, ContextualEta.Step t u → ContextualEta.Step (F a b t) (F a b u))
    (ha : Steps bk a a') (hb : Steps bk b b') (hc : Steps bk c c')
    (ca : Canonical a) (cb : Canonical b) (cc : Canonical c) :
    Steps bk (F a b c) (F a' b' c') :=
  steps_trans (steps_map (F · b c) (fun h => ho h (opar_refl cb) (opar_refl cc)) (h1 b c) ha)
    (steps_trans (steps_map (F a' · c)
      (fun h => ho (opar_refl (steps_canonical ha ca)) h (opar_refl cc)) (h2 a' c) hb)
      (steps_map (F a' b')
        (fun h => ho (opar_refl (steps_canonical ha ca)) (opar_refl (steps_canonical hb cb)) h)
        (h3 a' b') hc))



theorem erase_closed_reflect (h : Closed (erase t)) : Closed t := by
  apply ren_closed
  apply erase_ren_fix_reflect
  rw [ren_as_sub]
  exact h _



theorem epar_steps (h : EPar (eraseBook bk) t u) (hc : Canonical t) : Steps bk t u := by
  induction h
  all_goals simp only [Canonical, erase, erase_ren, Term.Ann.injEq, Term.Let.injEq,
    Term.Typ.injEq, Term.Min.injEq, Term.All.injEq, Term.Lam.injEq, Term.App.injEq,
    Term.Sig.injEq, Term.Tup.injEq, Term.Prj.injEq, Term.Mat.injEq, Term.Eql.injEq,
    Term.Rwt.injEq, true_and, and_true] at hc
  case var | ref | enu | lab | efq | rfl => exact .refl
  case ann _ _ iha ihb => exact steps_map2 Ann OPar.ann (fun _ => .ann_left) (fun _ => .ann_right) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case lett _ _ iha ihb => exact steps_map2 (Let _) OPar.lett (fun _ => .let_value) (fun _ => .let_body) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case typ _ ih => exact steps_map Typ OPar.typ ContextualEta.Step.typ (ih hc)
  case min _ _ iha ihb => exact steps_map2 Term.Min OPar.min (fun _ => .min_left) (fun _ => .min_right) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case all _ _ iha ihb => exact steps_map2 (All _) OPar.all (fun _ => .all_domain) (fun _ => .all_body) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case lam _ ih => exact steps_map (Lam Q1) OPar.lam ContextualEta.Step.lam (ih hc)
  case app _ _ iha ihb => exact steps_map2 (App Q1) OPar.app (fun _ => .app_function) (fun _ => .app_argument) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case sig _ _ iha ihb => exact steps_map2 (Sig _) OPar.sig (fun _ => .sig_domain) (fun _ => .sig_body) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case tup _ _ iha ihb => exact steps_map2 (Tup _) OPar.tup (fun _ => .tup_first) (fun _ => .tup_second) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case prj _ ih => exact steps_map Prj OPar.prj ContextualEta.Step.prj (ih hc)
  case mat _ _ iha ihb => exact steps_map2 (Mat _) OPar.mat (fun _ => .mat_hit) (fun _ => .mat_miss) (iha hc.1) (ihb hc.2) hc.1 hc.2
  case eql _ _ _ iha ihb ihc => exact steps_map3 Eql OPar.eql (fun _ _ => .eql_left) (fun _ _ => .eql_right) (fun _ _ => .eql_type) (iha hc.1) (ihb hc.2.1) (ihc hc.2.2) hc.1 hc.2.1 hc.2.2
  case rwt _ _ _ iha ihb ihc => exact steps_map3 Rwt OPar.rwt (fun _ _ => .rwt_proof) (fun _ _ => .rwt_motive) (fun _ _ => .rwt_value) (iha hc.1) (ihb hc.2.1) (ihc hc.2.2) hc.1 hc.2.1 hc.2.2
  case delta k v hk hv =>
    unfold eraseBook at hk
    cases hd : Book.get bk k with
    | none => simp [hd] at hk
    | some d =>
      have he : erase d.v = v := by simpa [hd] using hk
      subst v
      exact single (.ordinary (.delta hd (erase_closed_reflect hv)))
  case unann _ ih => exact .step (.ordinary (.unann (opar_refl hc.1))) (ih hc.1)
  case unlet hv hf ihv ihf =>
    rename_i q
    have hs := steps_map2 (Let q) OPar.lett (fun _ => .let_value) (fun _ => .let_body) (ihv hc.1) (ihf hc.2) hc.1 hc.2
    exact steps_trans hs (single (.ordinary (.unlet (opar_refl (epar_canonical eraseBook_canonical hv hc.1)) (opar_refl (epar_canonical eraseBook_canonical hf hc.2)))))
  case beta hf hx ihf ihx =>
    have hs := steps_map2 (fun f x => App Q1 (Lam Q1 f) x)
      (fun hf hx => .app (.lam hf) hx)
      (fun _ h => .app_function (.lam h)) (fun _ h => .app_argument h)
      (ihf hc.1) (ihx hc.2) hc.1 hc.2
    exact steps_trans hs (single (.ordinary (.beta (opar_refl (epar_canonical eraseBook_canonical hf hc.1)) (opar_refl (epar_canonical eraseBook_canonical hx hc.2)))))
  case split hh ha hb ihh iha ihb =>
    rename_i r
    have hs := steps_map3 (fun h a b => App Q1 (Prj h) (Tup r a b))
      (fun hh ha hb => .app (.prj hh) (.tup ha hb))
      (fun _ _ h => .app_function (.prj h))
      (fun _ _ h => .app_argument (.tup_first h))
      (fun _ _ h => .app_argument (.tup_second h))
      (ihh hc.1) (iha hc.2.1) (ihb hc.2.2) hc.1 hc.2.1 hc.2.2
    exact steps_trans hs (single (.ordinary (.split (opar_refl (epar_canonical eraseBook_canonical hh hc.1)) (opar_refl (epar_canonical eraseBook_canonical ha hc.2.1)) (opar_refl (epar_canonical eraseBook_canonical hb hc.2.2)))))
  case hit hh ih => exact .step (.ordinary (.hit (opar_refl hc.1))) (ih hc.1)
  case miss hn hm ih =>
    refine .step (.ordinary (.miss hn (opar_refl hc.2))) ?_
    exact steps_map (App Q1 · (Lab _)) (fun h => .app h .lab) (fun h => .app_function h) (ih hc.2)
  case cast hf ih => exact .step (.ordinary (.cast (opar_refl hc.2))) (ih hc.2)
  case meet ha hb iha ihb =>
    have hs := steps_map2 Term.Min OPar.min (fun _ => .min_left) (fun _ => .min_right) (iha hc.1) (ihb hc.2) hc.1 hc.2
    exact steps_trans hs (single (.ordinary (.meet (opar_refl (epar_canonical eraseBook_canonical ha hc.1)) (opar_refl (epar_canonical eraseBook_canonical hb hc.2)))))
  case eta hf ih =>
    have cf : Canonical _ := CriticalPairs.ren_injective Nat.succ (fun _ _ e => Nat.succ.inj e) hc
    exact .step (.eta .eta) (ih cf)



theorem epars_steps (h : EPars (eraseBook bk) t u) (hc : Canonical t) : Steps bk t u := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact steps_trans (epar_steps h hc) (ih (epar_canonical eraseBook_canonical h hc))



end MixedReduction

end

-- Source section: RevisedValueForms
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion BetaEtaPeak



namespace Revised



theorem empty_value (wt : Revised.WellTyped bk) (v : Value bk t)
    (h : Typed bk [] t (Enu [])) : False :=
  (canon_enu wt v h join_refl).elim nofun



end Revised

end

-- Source section: OperationalBridge
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge



namespace OperationalBridge



inductive Trace (bk : Book) : Term → Term → Prop
  | refl : Trace bk t t
  | step : Eval bk t u → Trace bk u v → Trace bk t v



end OperationalBridge

end

-- Source section: RevisedProgress
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion BetaEtaPeak



namespace Revised



theorem spine_arg (h : Typed bk [] (spine (App q f x) xs) T) :
    ∃ A B, Typed bk [] f (All q A B) ∧ Typed bk [] x A := by
  induction xs generalizing q f x T
  rotate_left; rename_i ih; have ⟨_, _, h, _⟩ := ih h
  all_goals have ⟨_, ⟨A, B, _, h⟩, _⟩ := gen h; exact ⟨A, B, h⟩



theorem no_var (h : Typed bk Γ t A) : Γ = [] → t = Var w → False := by
  induction h
  case var => rintro rfl _; simp_all
  case conv => assumption
  all_goals intro _ e; cases e




theorem fire_ok (exposure : TypedDataExposure bk) (wt : Revised.WellTyped bk) (hf : Typed bk [] f (All q A B)) (hx : Typed bk [] x A)
    (vx : q.live = true → Value bk x) : Fire q x f := by
  have ⟨_, g, F, _⟩ := gen hf
  cases f <;> simp only [Fire, Gen] at g ⊢ <;> (repeat obtain ⟨_, g⟩ : ∃ _, _ := g) <;> obtain ⟨rfl, g⟩ := g <;>
    obtain ⟨rfl, hA, -⟩ := new_fits_all F
  case Lam => exact ⟨g.1.symm, fun e => canon_data_of_data_exposure exposure wt (vx (by subst e; exact g.1)) (.conv hx hA) (g.2.1 e)⟩
  case Prj =>
    have v := vx g.1; have := value_form wt v (.conv hx hA) join_refl (by simp [Rigid, former])
    cases v <;> simp_all [tform, former, ↓tform_call]
  case Mat => exact ⟨g.1, (canon_enu wt (vx g.1) (.conv hx hA) join_refl).imp fun _ => And.right⟩
  case Efq => exact (canon_enu wt (vx g) (.conv hx hA) join_refl).elim nofun



theorem arg_fire (exposure : TypedDataExposure bk) (wt : Revised.WellTyped bk) (h : Typed bk [] (spine t ((q, x) :: xs)) T)
    (vx : q.live = true → Value bk x) : Fire q x t :=
  let ⟨_, _, hf, hx⟩ := spine_arg h; fire_ok exposure wt hf hx vx




theorem walk_go (exposure : TypedDataExposure bk) (wt : Revised.WellTyped bk) (t : Term) : ∀ e xs {T g ps}, tree g ps t = true →
    EnvOk bk e t → Values bk xs → Typed bk [] (spine (sub (Env.sub e) t) xs) T →
    ∃ o, Walk bk t e xs o := by
  have S := fun {t u T} => sr (Γ := []) (t := t) (u := u) (T := T) wt
  have M : ∀ {e s t}, EnvOk bk e t →
      ∀ (_ : ∀ i, uses s i ≤ uses t i := by simp [uses]), EnvOk bk e s :=
    fun hu le i => (hu i).imp_right (Or.imp_left fun h => by have := le i; omega)
  induction t <;> intro e xs T g ps ht hu vs hty
  case App q f y ihf ihy =>
    cases y
    case Var v =>
      cases hn : takes (unspine f []).1; exact ⟨_, .done hn⟩
      simp only [tree, hn] at ht
      refine (ihf _ _ ht (M hu) (.cons (fun l => ?_) vs) hty).imp fun _ => .app hn
      rcases hu v with h | h | ⟨_, h⟩; exact h; simp [uses, l] at h
      have ⟨_, _, _, hx⟩ := spine_arg hty; exact (no_var hx rfl h).elim
    all_goals exact ⟨_, .done rfl⟩
  all_goals first | exact ⟨_, .done rfl⟩ | (cases vs; exact ⟨_, .need rfl⟩)
  case Lam.cons p f ih x xs q vx vs =>
    have ⟨pl, dx⟩ : Fire q x (Lam p _) := arg_fire exposure wt hty vx
    simp only [tree, Bool.and_eq_true] at ht
    refine (ih (x :: e) xs ht.2 (fun | 0 => ?_ | i + 1 => hu i) vs
      (env_inst ▸ S hty (par_spine (a := App ..) (.beta par_refl par_refl)))).imp
      fun _ => .lam pl dx
    cases p <;> first | exact .inl (vx (pl ▸ rfl)) | exact .inr (.inl (beq_iff_eq.1 ht.1))
  case Prj.cons h ih x xs q vx vs =>
    obtain ⟨l, r, _, _, rfl⟩ : Fire q x (Prj _) := arg_fire exposure wt hty vx
    have ⟨va, vb⟩ := value_tup (vx l)
    exact (ih _ _ ht hu
      (.cons (fun l' => va (by cases r <;> trivial)) (.cons (fun _ => vb) vs))
      (S hty (par_spine (a := App ..) (.split par_refl par_refl par_refl)))).imp fun _ => .prj l
  case Mat.cons k h m ihh ihm x xs q vx vs =>
    obtain ⟨l, j, rfl⟩ : Fire q x (Mat _ _ _) := arg_fire exposure wt hty vx
    simp only [tree, Bool.and_eq_true] at ht
    by_cases ej : j = k; subst ej
    exact (ihh _ _ ht.1 (M hu) vs (S hty (par_spine (a := App ..) (.hit par_refl)))).imp fun _ => .hit l
    exact (ihm _ _ ht.2 (M hu)
      (.cons (fun _ => .lab) vs) (S hty (par_spine (a := App ..) (.miss ej par_refl)))).imp fun _ => .miss l ej
  case Efq.cons => exact (arg_fire (t := Efq) exposure wt hty ‹_›).elim



theorem call_ok (exposure : TypedDataExposure bk) (wt : Revised.WellTyped bk) (lv : Book.Live bk) (hk : Book.get bk k = some d)
    (vs : Values bk xs) (h : Typed bk [] (spine (Ref k) xs) T) :
    Value bk (spine (Ref k) xs) ∨ ∃ u, Eval bk (spine (Ref k) xs) u := by
  have ⟨i, hi⟩ := index_of_get hk
  obtain ⟨_ | _, w⟩ := walk_go exposure wt _ _ _ (lv.2 k i d hi hk) (fun i => .inr (.inr ⟨i, rfl⟩)) vs
    (by rw [env_nil, sub_var]; exact sr wt h (par_spine (.delta hk (wt _ _ hk).2.2)))
  exact .inl (.call hk vs w); exact .inr ⟨_, .call hk vs w⟩




theorem progress_of_data_exposure (exposure : TypedDataExposure bk)
    (wt : Revised.WellTyped bk) (lv : Book.Live bk) (h : Typed bk [] t T) :
    Value bk t ∨ ∃ u, Eval bk t u := by
  generalize eΓ : ([] : List Term) = Γ at h
  induction h <;> subst eΓ
  case var e => simp at e
  case ref hk => exact call_ok (xs := []) exposure wt lv hk .nil (.ref (σ := Var) hk)
  case ann => exact .inr ⟨_, .ann⟩
  case lett hv hq _ ihv _ _ =>
    exact .inr <| (live_or fun _ => ihv rfl).elim
      (fun v => ⟨_, .unlet v fun e => canon_data_of_data_exposure exposure wt (v (e ▸ rfl)) hv (hq e)⟩) fun ⟨_, l, s⟩ => ⟨_, .lett l s⟩
  case app hf hx ihf ihx =>
    refine (ihf rfl).elim (fun vf => ?_) fun ⟨_, s⟩ => .inr ⟨_, .app_f s⟩
    refine (live_or fun _ => ihx rfl).elim (fun vx => ?_) fun ⟨_, l, s⟩ => .inr ⟨_, .app_x vf l s⟩
    have F := fire_ok exposure wt hf hx vx
    have C := value_form wt vf hf join_refl (by simp [Rigid, former])
    cases vf
    case lam => exact .inr ⟨_, .beta F.1 vx F.2⟩
    case prj => obtain ⟨l, _, _, _, rfl⟩ := F; exact .inr ⟨_, .split l (vx l)⟩
    case mat k _ _ => obtain ⟨l, j, rfl⟩ := F; exact .inr (if e : j = k then e ▸ ⟨_, .hit l⟩ else ⟨_, .miss l e⟩)
    case efq => exact F.elim
    case call hk vs _ =>
      rw [← spine_snoc]; exact call_ok exposure wt lv hk (values_snoc.2 ⟨vs, vx⟩) (spine_snoc ▸ Typed.app hf hx)
    all_goals simp [tform, former] at C
  case tup _ _ iha ihb =>
    exact (live_or fun _ => iha rfl).elim (fun va => (ihb rfl).imp (.tup va) fun ⟨_, s⟩ => ⟨_, .tup_b va s⟩)
      fun ⟨_, l, s⟩ => .inr ⟨_, .tup_a l s⟩
  case rwt _ he _ _ ihe _ _ =>
    exact .inr <| (ihe rfl).elim
      (fun ve => by
        have := value_form wt ve he join_refl (by simp [Rigid, former])
        cases ve <;> simp [tform, former, ↓tform_call] at this; exact ⟨_, .cast⟩)
      fun ⟨_, s⟩ => ⟨_, .rwt s⟩
  case conv _ _ ih => exact ih rfl
  case min ha hb iha ihb =>
    refine .inr <| (iha rfl).elim (fun va => (ihb rfl).elim (fun vb => ?_) fun ⟨_, s⟩ => ⟨_, .min_b va s⟩)
      fun ⟨_, s⟩ => ⟨_, .min_a s⟩
    obtain ⟨_, mi, rfl⟩ := canon_enu wt va ha join_refl
    obtain ⟨_, mj, rfl⟩ := canon_enu wt vb hb join_refl
    exact ⟨_, .meet mi mj⟩
  all_goals exact .inl (by constructor)




theorem value_reached_of_data_exposure (exposure : TypedDataExposure bk)
    (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (ht : Acc (fun u t => Eval bk t u) t) (h : Typed bk [] t T) :
    ∃ v, OperationalBridge.Trace bk t v ∧ Value bk v ∧ Typed bk [] v T := by
  induction ht with
  | intro t _ ih =>
    rcases progress_of_data_exposure exposure wt lv h with hv | ⟨u, hu⟩
    · exact ⟨t, .refl, hv, h⟩
    · obtain ⟨v, hv, vv, ht⟩ := ih u hu (eval_preservation wt h hu)
      exact ⟨v, .step hu hv, vv, ht⟩



theorem data_results_of_data_exposure (exposure : TypedDataExposure bk)
    (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (hc : Closed t) (hl : Term.Live bk t)
    (h : Typed bk [] t T) (hT : Typed bk [] T T2) :
    ∃ v, OperationalBridge.Trace bk t v ∧ Data v ∧ Typed bk [] v T := by
  obtain ⟨v, hv, vv, ht⟩ := value_reached_of_data_exposure exposure wt lv
    (halts bk t lv hc hl) h
  exact ⟨v, hv, canon_data_of_data_exposure exposure wt vv ht hT, ht⟩



theorem no_closed_empty_of_data_exposure (exposure : TypedDataExposure bk)
    (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (hc : Closed t) (hl : Term.Live bk t) : ¬ Typed bk [] t (Enu []) := by
  intro h
  obtain ⟨v, _, vv, ht⟩ := value_reached_of_data_exposure exposure wt lv
    (halts bk t lv hc hl) h
  exact empty_value wt vv ht



end Revised

end

-- Source section: RevisedChecker
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open ExecutableOrder



namespace Revised



def fit (ck : Book) (c : Ctx) (U T : Term) : Res Unit :=
  let U := Ctx.zeta c U
  let T := Ctx.zeta c T
  Ctx.need c (diagnosticFits ck c.isEmpty FUEL U T) (Term.show T c.length) U




mutual

def infer (ck : Book) : Nat → Ctx → Term → Res Term
  | 0, _, _ => throw "out of fuel"
  | _ + 1, c, Var i =>
    match c[i]? with
    | some (A, _) => pure (Term.ren (· + (i + 1)) A)
    | none        => throw "unbound variable"
  | _ + 1, _, Ref k =>
    match ck.get k with
    | some d => pure d.T
    | none   => throw ("unknown def: " ++ k)
  | n + 1, c, Ann x T => do
    check ck n c T T1
    check ck n c x T
    pure T
  | n + 1, c, Typ q => do
    check ck n c q (Enu QS)
    pure T1
  | n + 1, c, Term.Min a b => do
    check ck n c a (Enu QS)
    check ck n c b (Enu QS)
    pure (Enu QS)
  | n + 1, c, All q A B => do
    check ck n c A (Term.kindof q T1)
    check ck n ((A, none) :: c) B T1
    pure T1
  | n + 1, c, App q f x => do
    let F ← infer ck n c f
    match Ctx.wnf ck c F with
    | All p A B => do
      Res.need (p == q) "an argument of its binder's quantity"
      check ck n c x A
      pure (Term.inst B (Term.arg x A))
    | F => Ctx.fail c "a function" F
  | _ + 1, _, Enu _ => pure T2
  | n + 1, c, Eql a b T => do
    check ck n c T T1
    check ck n c a T
    check ck n c b T
    pure T2
  | _ + 1, c, t => Ctx.fail c "an annotated term" t

-- Γ ⊢ v : V   V : *2 if q=2   Γ, V := v ⊢ f : T
-- -------------------------------------------- let
-- Γ ⊢ !q x = v; f : T
--
-- T = ∀p x:A -> B   live p = live q   A : *2 if q=2   Γ, A ⊢ f : B
-- ---------------------------------------------------------- lam
-- Γ ⊢ λq x => f : T
--
-- T = *(g)   Γ ⊢ A : kindof(q, *(g))   Γ, A ⊢ B : *(g)
-- ------------------------------------------------- sig
-- Γ ⊢ Σq x:A -> B : T
--
-- T = Σq x:A -> B   Γ ⊢ a : A   Γ ⊢ b : B[a]      T = <ks>   k ∈ ks
-- ------------------------------------ tup     ---------------- lab
-- Γ ⊢ (q a, b) : T                              Γ ⊢ .k : T
--
-- T = ∀q s:(Σr x:A -> B) -> P   live q
-- Γ ⊢ h : ∀fld(r, q) x:A -> ∀q y:B -> P[(r x, y)]
-- ---------------------------------------------- prj
-- Γ ⊢ λ{(,): h} : T
--
-- T = ∀q s:<ks> -> P   live q   k ∈ ks
-- Γ ⊢ h : P[.k]   Γ ⊢ m : ∀q s:<ks - k> -> P
-- ----------------------------------------- mat
-- Γ ⊢ λ{.k: h; m} : T
--
-- T = ∀q s:<> -> P   live q       T = {a == b : A}   a ≡ b
-- ------------------------ efq    ----------------------- rfl
-- Γ ⊢ λ{} : T                     Γ ⊢ {==} : T
--
-- Γ ⊢ e : {a == b : A}   Γ, x : A, h : {a == x : A} ⊢ P : *1
-- P[b, e] ≤ T   Γ ⊢ f : P[a, {==}]
-- ------------------------------------------------------- rwt
-- Γ ⊢ %e : x, h => P; f : T
--
-- Γ ⊢ x : A   Γ ⊢ f : ∀q s:A -> T[x := s]    f's head is a λ or a λ-match
-- -------------------------------------------------------------- elim
-- Γ ⊢ (f q x) : T
--
-- Γ ⊢ x : U   U ≤ T
-- ----------------- any
-- Γ ⊢ x : T
def check (ck : Book) : Nat → Ctx → Term → Term → Res Unit
  | 0, _, _, _ => throw "out of fuel"
  | n + 1, c, Let q v f, T => do
    let V := Ctx.wnf ck c (← infer ck n c v)
    if q == Q2 then
      check ck n c V T2
    check ck n ((V, some v) :: c) f (Term.ren Nat.succ T)
  | n + 1, c, Lam q f, T =>
    match Ctx.wnf ck c T with
    | All p A B => do
      let A := Ctx.wnf ck c A
      Res.need (Quan.live p == Quan.live q) "a λ of its binder's liveness"
      if q == Q2 then
        check ck n c A T2
      check ck n ((A, none) :: c) f B
    | T => Ctx.fail c "a function type" T
  | n + 1, c, Sig q A B, T =>
    match Ctx.wnf ck c T with
    | Typ g => do
      check ck n c A (Term.kindof q (Typ g))
      check ck n ((A, none) :: c) B (Typ (Term.ren Nat.succ g))
    | T => Ctx.fail c "a kind" T
  | n + 1, c, Tup q a b, T =>
    match Ctx.wnf ck c T with
    | Sig p A B => do
      Res.need (p == q) "a field of its Σ's quantity"
      check ck n c a A
      check ck n c b (Term.inst B a)
    | T => Ctx.fail c "a Σ type" T
  | _ + 1, c, Lab k, T =>
    match Ctx.wnf ck c T with
    | Enu ks => Res.need (ks.contains k) ("a label of " ++ Term.show (Enu ks) 0)
    | T      => Ctx.fail c "an enum" T
  | n + 1, c, Prj h, T =>
    match Ctx.wnf ck c T with
    | All q D P =>
      match Ctx.wnf ck c D with
      | Sig r A B => do
        Res.need (Quan.live q) "a live scrutinee"
        let P := Term.sub (Subst.tup r) P
        check ck n c h (All (Quan.fld r q) A (All q B P))
      | D => Ctx.fail c "a Σ type" D
    | T => Ctx.fail c "a function type" T
  | n + 1, c, Mat k h m, T =>
    match Ctx.wnf ck c T with
    | All q D P =>
      match Ctx.wnf ck c D with
      | Enu ks => do
        Res.need (Quan.live q) "a live scrutinee"
        Res.need (ks.contains k) ("a label of " ++ Term.show (Enu ks) 0)
        check ck n c h (Term.inst P (Lab k))
        check ck n c m (All q (Enu (ks.erase k)) P)
      | D => Ctx.fail c "an enum" D
    | T => Ctx.fail c "a function type" T
  | _ + 1, c, Efq, T =>
    match Ctx.wnf ck c T with
    | All q D _ =>
      match Ctx.wnf ck c D with
      | Enu [] => Res.need (Quan.live q) "a live scrutinee"
      | D      => Ctx.fail c "an empty enum" D
    | T => Ctx.fail c "a function type" T
  | _ + 1, c, Rfl, T =>
    match Ctx.wnf ck c T with
    | Eql a b _ => Ctx.need c (diagnosticCompare ck c.isEmpty FUEL a b) (Term.show a c.length) b
    | T => Ctx.fail c "an equation" T
  | n + 1, c, Rwt e P f, T => do
    let E ← infer ck n c e
    match Ctx.wnf ck c E with
    | Eql a b A => do
      let E := Eql (Term.ren Nat.succ a) (Var 0) (Term.ren Nat.succ A)
      check ck n ((E, none) :: (A, none) :: c) P T1
      fit ck c (Term.inst (Term.inst P (Term.ren Nat.succ e)) b) T
      check ck n c f (Term.inst (Term.inst P Rfl) a)
    | E => Ctx.fail c "an equation" E
  | n + 1, c, App q f (Var i), T =>
    if Term.takes (Term.unspine f []).1 then do
      let A ← infer ck n c (Var i)
      let P := Term.ren (Ren.pick i) T
      check ck n c f (All q A P)
    else do
      let U ← infer ck n c (App q f (Var i))
      fit ck c U T
  | n + 1, c, t, T => do
    let U ← infer ck n c t
    fit ck c U T


end



section



-- every variable has its type, through Ctx.drop
def CtxOk (bk : Book) (c : Ctx) : Prop :=
  SubstOk bk (Ctx.decl c) (Ctx.drop c) (c.map (·.1))



-- a checker judgment, read through Ctx.drop
def Chk (bk : Book) (c : Ctx) (t T : Term) : Prop :=
  Typed bk (Ctx.decl c) (sub (Ctx.drop c) t) (sub (Ctx.drop c) T)



attribute [local simp] ok_bind ok_map ok_pure ok_unit ok_need ok_cneed ok_fail ok_if



theorem fit_sound (hb : Sees ck bk) (h : fit ck c U T = .ok a) :
    NewFits bk (sub (Ctx.drop c) U) (sub (Ctx.drop c) T) :=
  (zeta_drop ▸ zeta_drop ▸ new_fits_sub (σ := Ctx.drop c) (diagnostic_fits_sound hb (ok_cneed.1 h)) :)



-- a checker type converts with its Ctx.wnf
theorem wnf_conv (hcl : Sees ck bk) (e : Ctx.wnf ck c T = W) : Join bk (sub (Ctx.drop c) T) (sub (Ctx.drop c) W) :=
  e ▸ zeta_drop ▸ join_sub (join_old ⟨_, (wnf_pars (xs := []) hcl).1, .refl⟩)



-- each checker rule lands on its Typed rule, through Ctx.drop
theorem chk (hcl : Sees ck bk) (n : Nat) : ∀ c t T, CtxOk bk c →
    (infer ck n c t = .ok T → Chk bk c t T) ∧
    (check ck n c t T = .ok () → Chk bk c t T) := by
  induction n with
  | zero => intros; constructor <;> nofun
  | succ n ih =>
  intro c t T hc
  have I t T := (ih c t T hc).1
  have C t T := (ih c t T hc).2
  have B {A t T} := (ih ((A, none) :: c) t T (substok_up hc)).2
  have A {t T} (h : (infer ck n c t >>= (fit ck c · T)) = .ok ()) :=
    have ⟨_, h1, h⟩ := ok_bind.1 h
    Typed.conv (I _ _ h1) (fit_sound hcl h)
  unfold Chk at *
  refine ⟨fun h => ?_, fun h => ?_⟩
  · revert T; cases t <;> simp only [infer] <;> (try split) <;> simp
    · rename_i e; exact hc _ _ (by simp [e])
    · rename_i e; have ⟨_, e, _⟩ := hcl _ _ e; exact (Typed.ref e :)
    · exact fun h1 h2 => .ann (C _ _ h1) (C _ _ h2)
    · exact fun h1 => .typ (C _ _ h1)
    · exact fun h1 h2 => .min (C _ _ h1) (C _ _ h2)
    · exact fun h1 h2 => .all (by simpa only [kindof_sub, sub] using C _ _ h1) (B h2)
    · intro _ F h1 h; split at h <;> simp at h; rename_i e; obtain ⟨rfl, h2, rfl⟩ := h
      rw [inst_sub]
      refine .conv (.app (.conv (I _ _ h1) (.conv (wnf_conv hcl e))) (C _ _ h2))
        (.conv (join_old ⟨_, .refl, .step (par_inst par_refl ?_) .refl⟩))
      unfold arg; split; exact .unann par_refl; exact par_refl
    · exact .enu
    · rintro _ h1 h2 h3 rfl; exact .eql (C _ _ h1) (C _ _ h2) (C _ _ h3)
  · cases t <;> (try simp [check] at h) <;> (try split at h) <;>
      (try simp at h) <;> (try split at h) <;> (try simp at h)
    all_goals try first | exact A h | exact A (ok_bind.2 h)
    all_goals try refine .conv ?_ (.conv (join_symm (wnf_conv hcl ‹Ctx.wnf ck c T = _›)))
    all_goals try refine .conv ?_ (.all (.conv (wnf_conv hcl (by first | assumption | rfl))) (.conv join_refl))
    · obtain ⟨V, h1, h3, h2⟩ := h
      have h1 := Typed.conv (I _ _ h1) (.conv (wnf_conv hcl rfl))
      have := (ih _ _ _ fun i A e => by rw [sub_ren]; cases i; (cases e; exact h1); exact (sub_ren _ ▸ hc _ _ e :)).2 h2
      rw [Ctx.drop, sub_ren, ← sub_sub] at this
      exact .lett h1 (fun e => C _ _ (h3 e)) (inst_sub ▸ this)
    · exact .lam h.1 (fun e => C _ _ (h.2.1 e)) (B h.2.2)
    · cases ‹Term› <;> simp only [check] at h <;> (try split at h) <;> try exact A h
      rename_i i _; obtain ⟨A, h1, h2⟩ := ok_bind.1 h
      rw [← pick_inst (T := T) (i := i), inst_sub]; exact .app (C _ _ h2) (I _ _ h1)
    · exact .sig (by simpa only [kindof_sub, sub] using C _ _ h.1)
        (by simpa only [sub_succ, Ctx.decl, Ctx.drop, sub] using B h.2)
    · obtain ⟨rfl, h1, h2⟩ := h; exact .tup (C _ _ h1) (inst_sub ▸ C _ _ h2)
    · exact .prj h.1 (by simpa only [sub, tup_sub] using C _ _ h.2)
    · exact .lab h
    · exact .mat h.1 h.2.1 (inst_sub ▸ C _ _ h.2.2.1 :) (C _ _ h.2.2.2)
    · exact .efq h
    · exact .rfl (join_sub (diagnostic_join hcl h))
    · obtain ⟨E, h1, h⟩ := h; split at h <;> simp at h; rename_i e
      refine .rwt (.conv (I _ _ h1) (.conv (wnf_conv hcl e))) ?_ ?_ ?_
      · simpa only [Ctx.decl, Ctx.drop, sub, Subst.up, sub_succ] using
          (ih ((_, none) :: (_, none) :: c) _ _ (substok_up (substok_up hc))).2 h.1
      · simpa only [inst_sub, sub_succ] using fit_sound hcl h.2.1
      · simpa only [inst_sub, sub] using C _ _ h.2.2




end



end Revised

end

-- Source section: RevisedBook
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open ExecutableOrder



namespace Revised



def checkDef (bk : Book) (ls : Book × Book) (i : Nat) (d : Def) : Res Unit := do
  let ck := if d.o then ls.2 else ls.1
  Res.need (Book.index bk d.k == some i) "a fresh name"
  check ck FUEL [] d.T T1
  check ck FUEL [] d.v d.T
  Res.need (Term.ren Nat.succ d.v == d.v) "a closed def"
  let g : Guard := ⟨bk, i, [], [], []⟩
  Res.need (Term.tree g [] d.v) "affine live code, calls that descend"



-- ls holds bk, and bk with every def transparent
def checkFrom (bk : Book) (ls : Book × Book) : Nat → List Def → Res Unit
  | _, [] => pure ()
  | i, d :: ds => do
    (checkDef bk ls i d).mapError (fun e => "In " ++ d.k ++ ":\n" ++ e)
    checkFrom bk ls (i + 1) ds



def checkBook (bk : Book) : Res Unit :=
  checkFrom bk (bk, Book.of (bk.defs.map ({ · with o := false }))) 0 bk.defs




attribute [local simp] ok_bind ok_map ok_pure ok_unit ok_need ok_cneed ok_fail ok_if



theorem check_from_ok : ∀ ds i, checkFrom bk ls i ds = .ok () →
    ∀ d ∈ ds, ∃ i, checkDef bk ls i d = .ok ()
  | [], _, _, _, h => nomatch h
  | d :: ds, i, h, e, he => by
    cases h2 : checkDef bk ls i d <;> simp_all [checkFrom, Except.mapError]
    exact he.elim (· ▸ ⟨i, h2⟩) (check_from_ok ds _ h e)



theorem book_check (h : checkBook bk = .ok ()) : WellTyped bk ∧ Book.Live bk := by
  have K ck t T (s : Sees ck bk) := (chk s FUEL [] t T nofun).2
  simp only [Chk, Ctx.decl, Ctx.drop, sub_var] at K
  -- a def checks against bk, or bk with no opaque flag
  have get k d (e : Book.get bk k = some d) : ∃ i, Book.index bk k = some i ∧ Closed d.v ∧
      (Book.Closed bk → Typed bk [] d.T T1 ∧ Typed bk [] d.v d.T) ∧ tree ⟨bk, i, [], [], []⟩ [] d.v = true := by
    rw [get_find] at e
    obtain ⟨i, h⟩ := check_from_ok _ 0 h d (List.mem_of_find?_eq_some e)
    obtain rfl : d.k = k := by simpa using List.find?_some e
    simp [checkDef] at h
    refine ⟨i, h.1, ren_closed h.2.2.2.1, fun hcl => ⟨K _ _ _ ?_ h.2.1, K _ _ _ ?_ h.2.2.1⟩, h.2.2.2.2⟩ <;> intro k d e <;>
      split at e <;> (try (rw [get_find] at e; simp [Book.of, List.find?_map, Function.comp_def] at e; obtain ⟨d, e, rfl⟩ := e; rw [← get_find] at e)) <;>
      exact ⟨d.o, e, hcl k d e⟩
  have hcl : Book.Closed bk := fun k d e => have ⟨_, _, c, _⟩ := get k d e; c
  refine ⟨fun k d e => ?_, hcl, fun k i d ei e => ?_⟩ <;> obtain ⟨j, ej, c, w, t⟩ := get k d e
  · exact ⟨(w hcl).1, (w hcl).2, c⟩
  · cases ei.symm.trans ej; exact t



end Revised

end

-- Source section: CheckedEvaluation
section

open Quan Term OperationalBridge



namespace Revised



theorem trace_preservation (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ t T) (hs : Trace bk t u) : Revised.Typed bk Γ u T := by
  induction hs with
  | refl => exact ht
  | step hs _ ih => exact ih (eval_preservation wt ht hs)



-- Every evaluated checked definition keeps its declared type.
theorem checked_definition_trace_preservation
    (hb : checkBook bk = .ok ()) (hd : Book.get bk k = some d)
    (hs : Trace bk d.v u) : Revised.Typed bk [] u d.T := by
  have wt := (book_check hb).1
  exact trace_preservation wt (wt k d hd).2.1 hs



-- A Data-kind judgment stays valid during original runtime evaluation.
theorem data_kind_trace_preservation (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ T T2) (hs : Trace bk T U) :
    Revised.Typed bk Γ U T2 := trace_preservation wt ht hs



end Revised

end

-- Source section: FullDataSafety
section

open Quan Term ConversionDesign ErasedReduction ExposureResearch


open ErasedOrdinary TypedHereditarySafety OrdinarySupport ContextualEta


open ExecutableOrder NewFitsInversion



namespace FullDataSafety



-- Each ordinary step can move before the remaining eta steps.
theorem mixed_factor_from (sim : ∀ a, EtaCommutation.Simulates bk a)
    (hm : MixedReduction.Steps bk b c) :
    ∀ {a}, Canonical a → HereditaryHeadSafe bk a → BigEta a b →
      ∃ d, OPars bk a d ∧ BigEta d c := by
  induction hm with
  | refl => intro a _ _ he; exact ⟨a, .refl, he⟩
  | step hs hm ih =>
    intro a ca hh he
    cases hs with
    | eta hs => exact ih ca hh (big_eta_trans he (step_big_eta hs))
    | ordinary hs =>
      obtain ⟨d, hd, he'⟩ := sim a he ca (σ := Var) (fun _ => rfl)
        (by simpa only [sub_var] using hh) (by simpa only [sub_var] using hs)
      simp only [sub_var] at hd
      obtain ⟨e, hd', he''⟩ := ih (opars_canonical hd ca) (hereditary_reduct hh hd) he'
      exact ⟨e, opars_trans hd hd', he''⟩



theorem mixed_factor_of_simulation (sim : ∀ a, EtaCommutation.Simulates bk a)
    (ca : Canonical a) (hh : HereditaryHeadSafe bk a)
    (hm : MixedReduction.Steps bk a c) : ∃ d, OPars bk a d ∧ BigEta d c :=
  mixed_factor_from sim hm ca hh (big_eta_refl a)



-- The factorization applies to every typed term, including terms in open contexts.
theorem typed_eta_factorization_of_simulation
    (sim : ∀ a, EtaCommutation.Simulates bk a)
    (wt : Revised.WellTyped bk) (ht : Revised.Typed bk Γ t T)
    (he : EPars (eraseBook bk) (erase t) C) :
    ∃ Y, Pars bk t Y ∧ EtaSteps (erase Y) C := by
  have hh := typed_erased_hereditary wt ht
  obtain ⟨d, hd, he'⟩ := mixed_factor_of_simulation sim (erase_idem t) hh
    (MixedReduction.epars_steps he (erase_idem t))
  obtain ⟨Y, hp, hY⟩ := opars_lift hd rfl
  refine ⟨Y, hp, ?_⟩
  rw [← hY] at he'
  exact big_eta_eta_steps he' (erase_idem Y)



-- A type at a kind can expose its rigid head through the original reduction rules.
theorem typed_kind_exposure_of_simulation
    (sim : ∀ a, EtaCommutation.Simulates bk a)
    (wt : Revised.WellTyped bk) (ht : Revised.Typed bk Γ T (Typ g))
    (hj : Join bk X T) (hr : Rigid X) :
    ∃ Y, Pars bk T Y ∧ Revised.Typed bk Γ Y (Typ g) ∧ Join bk X Y ∧
      Y.former = X.former := by
  obtain ⟨C, hX, hT⟩ := hj
  obtain ⟨Y, hp, he⟩ := typed_eta_factorization_of_simulation sim wt ht hT
  have hY := Revised.pars_sr wt ht hp
  have hf := eta_typed_kind_head hY he
  have hXf := epars_rigid hX (by simpa only [Rigid, erase_keeps_former] using hr)
  have hXY : Join bk X Y :=
    join_trans ⟨C, hX, hT⟩ (join_old ⟨_, hp, .refl⟩)
  refine ⟨Y, hp, hY, hXY, ?_⟩
  simpa only [erase_keeps_former] using hf.symm.trans hXf



theorem typed_data_exposure_of_simulation
    (sim : ∀ a, EtaCommutation.Simulates bk a)
    (wt : Revised.WellTyped bk) : Revised.TypedDataExposure bk := by
  intro T X ht hj hx
  obtain ⟨Y, _, hY, hXY, hhead⟩ := typed_kind_exposure_of_simulation sim wt ht hj
    (by simp_all [Rigid]; omega)
  exact ⟨Y, hY, hXY, hhead⟩



theorem typed_eta_factorization (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ t T) (he : EPars (eraseBook bk) (erase t) C) :
    ∃ Y, Pars bk t Y ∧ EtaSteps (erase Y) C :=
  typed_eta_factorization_of_simulation EtaCommutation.simulates wt ht he



theorem typed_kind_exposure (wt : Revised.WellTyped bk)
    (ht : Revised.Typed bk Γ T (Typ g)) (hj : Join bk X T) (hr : Rigid X) :
    ∃ Y, Pars bk T Y ∧ Revised.Typed bk Γ Y (Typ g) ∧ Join bk X Y ∧
      Y.former = X.former :=
  typed_kind_exposure_of_simulation EtaCommutation.simulates wt ht hj hr



theorem typed_data_exposure (wt : Revised.WellTyped bk) : Revised.TypedDataExposure bk :=
  typed_data_exposure_of_simulation EtaCommutation.simulates wt



end FullDataSafety



namespace Revised



-- A value at a formed Data type has only Data in its live fields.
theorem canon_data (wt : Revised.WellTyped bk) (hv : Value bk t)
    (ht : Revised.Typed bk [] t T) (hT : Revised.Typed bk [] T T2) : Data t :=
  canon_data_of_data_exposure (FullDataSafety.typed_data_exposure wt) wt hv ht hT



theorem progress (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (ht : Revised.Typed bk [] t T) : Value bk t ∨ ∃ u, Eval bk t u :=
  progress_of_data_exposure (FullDataSafety.typed_data_exposure wt) wt lv ht



theorem data_results (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (hc : Closed t) (hl : Term.Live bk t)
    (ht : Revised.Typed bk [] t T) (hT : Revised.Typed bk [] T T2) :
    ∃ v, OperationalBridge.Trace bk t v ∧ Data v ∧ Revised.Typed bk [] v T :=
  data_results_of_data_exposure (FullDataSafety.typed_data_exposure wt) wt lv hc hl ht hT



theorem no_closed_empty (wt : Revised.WellTyped bk) (lv : Book.Live bk)
    (hc : Closed t) (hl : Term.Live bk t) : ¬ Revised.Typed bk [] t (Enu []) :=
  no_closed_empty_of_data_exposure (FullDataSafety.typed_data_exposure wt) wt lv hc hl



-- A checked definition keeps both its declared type and its Data classification.
theorem checked_definition_data (hb : checkBook bk = .ok ())
    (hd : Book.get bk k = some d) (hT : Revised.Typed bk [] d.T T2)
    (hs : OperationalBridge.Trace bk d.v v) (hv : Value bk v) :
    Data v ∧ Revised.Typed bk [] v d.T := by
  have ht := checked_definition_trace_preservation hb hd hs
  exact ⟨canon_data (book_check hb).1 hv ht hT, ht⟩



theorem checked_data_results (hb : checkBook bk = .ok ())
    (hc : Closed t) (hl : Term.Live bk t)
    (ht : Revised.Typed bk [] t T) (hT : Revised.Typed bk [] T T2) :
    ∃ v, OperationalBridge.Trace bk t v ∧ Data v ∧ Revised.Typed bk [] v T :=
  data_results (book_check hb).1 (book_check hb).2 hc hl ht hT



end Revised

end

-- Source section: CheckedConsistency
section

open Quan Term ExecutableOrder



namespace Revised



-- A checked definition's declared type cannot equal Empty under revised conversion.
theorem checked_no_empty (ok : checkBook bk = .ok ())
    (get : Book.get bk k = some d) : ¬ Join bk d.T (Enu []) := by
  intro hc
  have ⟨wt, lv⟩ := book_check ok
  have ⟨i, hi⟩ := index_of_get get
  have ht : Revised.Typed bk [] (Ref k) d.T := by
    simpa only [sub_var] using (Revised.Typed.ref (σ := Var) get)
  have hclosed : Closed (Ref k) := fun _ => rfl
  have hlive : Term.Live bk (Ref k) := by
    simp [Live, Term.live, called, unspine, hi, index_lt hi]
  exact no_closed_empty wt lv hclosed hlive (.conv ht (.conv hc))



end Revised

end

-- Source section: TypedValueDataEquality
section

open Quan Term ConversionDesign ErasedReduction ConversionSpec EquationBridge


open QuantityBoundary GlobalDiamond ExecutableOrder NewFitsInversion BetaEtaPeak



namespace TypedValueDataEquality



theorem epars_tuple_parts (h : EPars bk s t) : s = Tup q a b →
    ∃ c d, t = Tup q c d ∧ EPars bk a c ∧ EPars bk b d := by
  induction h generalizing q a b with
  | refl => intro e; subst e; exact ⟨_, _, rfl, .refl, .refl⟩
  | step h _ ih =>
    intro e; subst e
    cases h with | tup ha hb =>
      obtain ⟨c, d, rfl, hc, hd⟩ := ih rfl
      exact ⟨_, _, rfl, .step ha hc, .step hb hd⟩



theorem join_tuple (h : Join bk (Tup p a b) (Tup q c d)) :
    p = q ∧ Join bk a c ∧ Join bk b d := by
  obtain ⟨t, h₁, h₂⟩ := h
  obtain ⟨a', b', rfl, ha, hb⟩ := epars_tuple_parts h₁ rfl
  obtain ⟨c', d', e, hc, hd⟩ := epars_tuple_parts h₂ rfl
  cases e
  exact ⟨rfl, ⟨_, ha, hc⟩, ⟨_, hb, hd⟩⟩



theorem same_value_type_form (wt : Revised.WellTyped bk)
    (va : Value bk a) (vb : Value bk b)
    (ha : Revised.Typed bk [] a T) (hb : Revised.Typed bk [] b T) :
    a.tform = b.tform := by
  obtain ⟨U, hU, eU⟩ := Revised.value_fits wt va ha
  obtain ⟨V, hV, eV⟩ := Revised.value_fits wt vb hb
  have ru : Rigid U := by rw [Rigid, eU]; cases a <;> simp [tform]
  have rv : Rigid V := by rw [Rigid, eV]; cases b <;> simp [tform]
  obtain ⟨X, cX, aX⟩ := (new_fits_at hU).2 U join_refl ru
  have rx : Rigid X := by simpa only [Rigid, ← NewFitsInversion.at_former aX] using ru
  obtain ⟨Y, cY, aY⟩ := (new_fits_at hV).1 X cX rx
  have ry : Rigid Y := by simpa only [Rigid, NewFitsInversion.at_former aY] using rx
  calc
    a.tform = U.former := eU.symm
    _ = X.former := NewFitsInversion.at_former aX
    _ = Y.former := (NewFitsInversion.at_former aY).symm
    _ = V.former := (join_rigid cY rv ry).symm
    _ = b.tform := eV



-- Both endpoints are values with the same type. No type-formation premise is needed.
theorem data_of_same_type_join (wt : Revised.WellTyped bk)
    (da : Data a) (va : Value bk a) (vb : Value bk b)
    (ha : Revised.Typed bk [] a T) (hb : Revised.Typed bk [] b T)
    (he : Join bk a b) : Data b := by
  induction da generalizing b T with
  | lab =>
    have hf := same_value_type_form wt va vb ha hb
    cases vb <;> simp [tform, ↓tform_call] at hf
    exact .lab
  | rfl =>
    have hf := same_value_type_form wt va vb ha hb
    cases vb <;> simp [tform, ↓tform_call] at hf
    exact .rfl
  | @tup a₁ a₂ q da₁ da₂ iha₁ iha₂ =>
    have hf := same_value_type_form wt va vb ha hb
    cases vb <;> simp [tform, ↓tform_call] at hf
    rename_i b₁ b₂ p vb₁ vb₂
    obtain ⟨rfl, he₁, he₂⟩ := join_tuple he
    obtain ⟨va₁, va₂⟩ := value_tup va
    obtain ⟨_, ⟨A, B, rfl, ha₁, ha₂⟩, hfitA, _⟩ := Revised.gen ha
    obtain ⟨_, ⟨C, D, rfl, hb₁, hb₂⟩, hfitB, _⟩ := Revised.gen hb
    obtain ⟨X, cX, aX⟩ := (new_fits_at hfitA).2 _ join_refl (by simp [Rigid, former])
    cases aX
    have hsig := new_fits_conv hfitB cX (by simp [former])
    obtain ⟨_, hCA, hDB⟩ := join_sig hsig
    have hb₁' : Revised.Typed bk [] b₁ A := .conv hb₁ (.conv hCA)
    have hb₂' : Revised.Typed bk [] b₂ (inst B a₁) := .conv hb₂ (.conv
      (join_trans (join_sub hDB) (Revised.join_inst_right (join_symm he₁))))
    exact .tup (fun l => iha₁ l (va₁ l) (vb₁ l) ha₁ hb₁' he₁)
      (iha₂ va₂ vb₂ ha₂ hb₂' he₂)



theorem data_iff_same_type_join (wt : Revised.WellTyped bk)
    (va : Value bk a) (vb : Value bk b)
    (ha : Revised.Typed bk [] a T) (hb : Revised.Typed bk [] b T)
    (he : Join bk a b) : Data a ↔ Data b :=
  ⟨fun h => data_of_same_type_join wt h va vb ha hb he,
    fun h => data_of_same_type_join wt h vb va hb ha (join_symm he)⟩



end TypedValueDataEquality

end

-- Source section: Candidate
section

open Quan Term ExecutableOrder



namespace Candidate



-- The CLI uses the parser and the checker in the formal development.
def checkText (source : String) : Res Unit :=
  Book.parse source >>= Revised.checkBook



-- Acceptance of text gives the checked book and its consistency result.
theorem accepted_text_no_empty (ok : checkText source = .ok ()) :
    ∃ bk, Book.parse source = .ok bk ∧ Revised.checkBook bk = .ok () ∧
      ∀ k d, Book.get bk k = some d → ¬ Join bk d.T (Enu []) := by
  unfold checkText at ok
  cases hp : Book.parse source with
  | error e => simp [hp, bind, Except.bind] at ok
  | ok bk =>
    have hc : Revised.checkBook bk = .ok () := by
      simpa [hp, bind, Except.bind] using ok
    exact ⟨bk, rfl, hc, fun k d hd => Revised.checked_no_empty hc hd⟩



-- This function keeps the original CLI input and output contract.
@[export bendtt_candidate_main]
def run (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let source ← IO.FS.readFile path
    match checkText source with
    | .ok _ =>
      IO.println "ALL PROOFS CHECK"
      pure 0
    | .error e =>
      IO.println ("SOME PROOFS FAIL\n" ++ e)
      pure 1
  | _ =>
    IO.println "usage: bendtt <file.bendtt>"
    pure 2



end Candidate

end

def main := Candidate.run

example := @Candidate.accepted_text_no_empty
#print axioms Candidate.accepted_text_no_empty

example := @Revised.chk
#print axioms Revised.chk

example := @Revised.book_check
#print axioms Revised.book_check

example := @Revised.typed_sub
#print axioms Revised.typed_sub

example := @Revised.typed_inst
#print axioms Revised.typed_inst

example := @Revised.sr
#print axioms Revised.sr

example := @Revised.pars_sr
#print axioms Revised.pars_sr

example := @Revised.eval_preservation
#print axioms Revised.eval_preservation

example := @Revised.trace_preservation
#print axioms Revised.trace_preservation

example := @Revised.data_kind_trace_preservation
#print axioms Revised.data_kind_trace_preservation

example := @Revised.checked_definition_trace_preservation
#print axioms Revised.checked_definition_trace_preservation

example := @Revised.progress
#print axioms Revised.progress

example := @Revised.empty_value
#print axioms Revised.empty_value

example := @Revised.canon_data
#print axioms Revised.canon_data

example := @Revised.data_results
#print axioms Revised.data_results

example := @Revised.no_closed_empty
#print axioms Revised.no_closed_empty

example := @Revised.checked_definition_data
#print axioms Revised.checked_definition_data

example := @Revised.checked_data_results
#print axioms Revised.checked_data_results

example := @Revised.checked_no_empty
#print axioms Revised.checked_no_empty

example := @FullDataSafety.typed_eta_factorization
#print axioms FullDataSafety.typed_eta_factorization

example := @FullDataSafety.typed_kind_exposure
#print axioms FullDataSafety.typed_kind_exposure

example := @FullDataSafety.typed_data_exposure
#print axioms FullDataSafety.typed_data_exposure

example := @TypedValueDataEquality.data_iff_same_type_join
#print axioms TypedValueDataEquality.data_iff_same_type_join

example := @halts
#print axioms halts

example := @confluent
#print axioms confluent

example := @sub_subz
#print axioms sub_subz

example := @EquationBridge.diagnostic_substitution_join
#print axioms EquationBridge.diagnostic_substitution_join

example := @EtaCommutation.full_eta_ordinary
#print axioms EtaCommutation.full_eta_ordinary

example := @GlobalDiamond.confluent
#print axioms GlobalDiamond.confluent

example := @EquationBridge.diagnostic_join
#print axioms EquationBridge.diagnostic_join

example := @ExecutableOrder.diagnostic_qge_sound
#print axioms ExecutableOrder.diagnostic_qge_sound

example := @ExecutableOrder.diagnostic_fits_sound
#print axioms ExecutableOrder.diagnostic_fits_sound

example := @ExecutableOrder.join_old
#print axioms ExecutableOrder.join_old

example := @ExecutableOrder.join_sub
#print axioms ExecutableOrder.join_sub

example := @ExecutableOrder.join_refl
#print axioms ExecutableOrder.join_refl

example := @ExecutableOrder.join_symm
#print axioms ExecutableOrder.join_symm

example := @ExecutableOrder.join_trans
#print axioms ExecutableOrder.join_trans
