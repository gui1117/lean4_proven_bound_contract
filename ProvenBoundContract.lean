-- DeBruijn indexing
namespace DBI

-- TODO: enforce expression are correctly built: every variable points to a correct lambda
-- TODO: every variable before and after a reduction points to the same lambda, except the removed lambda

-- DeBruijn indexing
inductive Expr
| app: Expr -> Expr -> Expr
| abst: Expr -> Expr
| var: Nat -> Expr
deriving Repr, BEq, Inhabited
open Expr

-- Helper function to avoid instance loop
def dbiToString : Expr → String
| app e1 e2  => "(" ++ dbiToString e1 ++ ") (" ++ dbiToString e2 ++ ")"
| abst e     => "λ. " ++ dbiToString e
| var x      => "#" ++ toString x

instance : ToString Expr where
  toString := dbiToString

-- Shift all the free vars in the expression by `shift`. `traversed` is used to follow through the
-- abstractions
def shiftFreeVars (shift : Nat) (traversed : Nat) : Expr -> Expr
  | app e1 e2 => app
    (shiftFreeVars shift traversed e1)
    (shiftFreeVars shift traversed e2)
  | abst e1 => abst (shiftFreeVars shift (traversed + 1) e1)
  | var x => if x >= traversed then var (x + shift) else var x

-- A shift of 0 is identity
theorem tZeroShiftFreeVars (traversed : Nat) : ∀ e : Expr, shiftFreeVars 0 traversed e = e
| app e₁ e₂ => by simp [shiftFreeVars, tZeroShiftFreeVars]
| abst e => by simp [shiftFreeVars, tZeroShiftFreeVars]
| var x => by
  by_cases h : x ≥ traversed
  <;> simp [shiftFreeVars, h, Nat.add_zero]

-- Replace the pos with `replaceWith` in `replaceIn`, pos is incremented for each abst
def replaceVars (pos : Nat) (replaceWith : Expr) (replaceIn : Expr) : Expr :=
  match replaceIn with
  | app e1 e2 => app (replaceVars pos replaceWith e1) (replaceVars pos replaceWith e2)
  | abst e1 => abst (replaceVars (pos + 1) replaceWith e1)
  | var x => if x = pos then
      shiftFreeVars pos 0 replaceWith
    else
      match x with
      | x' + 1 => if x' >= pos then var x' else var x
      | 0 => var x

-- Single β reduction
def betaRed : Expr -> Option Expr
| app e1 e2 =>
  (app · e2) <$> betaRed e1
  <|>
  (app e1 ·) <$> betaRed e2
  <|>
  match e1 with
    | abst e1_inner => some (replaceVars 0 e2 e1_inner)
    | _ => none
| abst e1 => (abst ·) <$> betaRed e1
| var _ => none

-- Reduce Expr n times
def reduceN (e : Expr) (n : Nat): Expr :=
  match n with
  | 0 => e
  | x + 1 =>
    match betaRed e with
    | some e' => reduceN e' x
    | none => e

-- Reduce Expr as much as possible, maybe forever
partial def reduceMax (e : Expr) : Expr :=
  match betaRed e with
  | some e' => reduceMax e'
  | none => e

-- Reduce both operand 10000 times and then compare them
def reduceEq10000 (a : Expr) (b : Expr) : Bool :=
  let ra := reduceN a 10000
  let rb := reduceN b 10000
  ra == rb

-- Reduce the expression and convert it to a string representation
def eval10000 (e : Expr) : String :=
  dbiToString (reduceN e 10000)

def idDBI : Expr := abst (var 0)

-- Id is identity for reduced operand
-- NOTE: all those theorem should be expanded for when the argument can be reduced in a number of
-- steps, something like: ∃ n : Nat, betaRed (reduceN x n) = none -> ...
-- Maybe we can create a concept of ReducedExpr
theorem tIdIsIdForReduced : ∀ x : Expr, betaRed x = none -> betaRed (app idDBI x) = x := by
  intro x _
  have : shiftFreeVars 0 0 x = x := by simp [tZeroShiftFreeVars]
  simp [betaRed, replaceVars, shiftFreeVars, *, idDBI]

def constantDBI : Expr := abst (abst (var 1))
def compDBI: Expr := abst (abst (abst (app (var 2) (app (var 1) (var 0)))))
def trueDBI : Expr := abst (abst (var 1))
def falseDBI : Expr := abst (abst (var 0))
def ifThenElseDBI : Expr := abst (abst (abst (app (app (var 2) (var 1)) (var 0))))
-- theorem if cond is true then reduce to then if cond is false then reduce to else, in K steps

def num0DBI : Expr := abst (abst (var 0))
def num1DBI : Expr := abst (abst (app (var 1) (var 0)))
def succDBI : Expr :=
  abst
    (abst
      (abst
        (app
          (var 1)
          (app
            (app
              (var 2)
              (var 1))
            (var 0)))))

def divergeDBI : Expr :=
  app
    (abst (app (var 0) (var 0)))
    (abst (app (var 0) (var 0)))
def DBINegate : Expr :=
  abst
    (app
      (app
        (app
          ifThenElseDBI
          (var 0))
        falseDBI)
      trueDBI)

def fromNatAux : Nat -> Expr
| 0 => var 0
| x + 1 => app (var 1) (fromNatAux x)

-- Convert Nat to Expr
def fromNat (n : Nat) : Expr :=
  abst (abst (fromNatAux n))

-- fromNatAux result is in formal form
theorem tFromNatAuxNf (n : Nat) : betaRed (fromNatAux n) = none := by
  induction n <;> simp [fromNatAux, *, betaRed]

theorem tFromNatIsReduced (n : Nat) : betaRed (fromNat n) = none := by
  simp [fromNat, fromNatAux, betaRed, tFromNatAuxNf]

def intoNatAux : Expr -> Option Nat
| var 0 => some 0
| app (var 1) e => Nat.succ <$> intoNatAux e
| _ => none

def intoNat : Expr -> Option Nat
| abst (abst e) => intoNatAux e
| _ => none

theorem tIntoNatAuxFromNatAuxIsId : ∀ n : Nat, intoNatAux (fromNatAux n) = some n := by
  intro n
  induction n <;> simp [fromNatAux, intoNatAux, *]

theorem tIntoNatfromNatIsId : ∀ n : Nat, intoNat (fromNat n) = some n := by
  intro n
  induction n <;> simp [fromNat, intoNat, tIntoNatAuxFromNatAuxIsId, *]

theorem tSuccWorks: ∀ n : Nat, reduceN (app succDBI (fromNat n)) 3 = fromNat (n + 1) := by
  intro n
  simp [reduceN]

  have step1Helper: ∀ n : Nat, shiftFreeVars 2 2 (fromNatAux n) = fromNatAux n := by
    intro n
    induction n <;> simp [fromNatAux, shiftFreeVars, *]

  have step1Helper2 : ∀ n : Nat, betaRed (fromNatAux n) = none := by simp [tFromNatAuxNf]

  have step3Helper : ∀ n : Nat, betaRed (replaceVars 1 (var 1) (fromNatAux n)) = none := by
    intro n
    induction n <;> simp [fromNatAux, betaRed, replaceVars, shiftFreeVars, *]

  have step3Helper2 : ∀ n : Nat, replaceVars 0 (var 0) (replaceVars 1 (var 1) (fromNatAux n)) = fromNatAux n := by
    intro n
    induction n <;> simp [fromNatAux, betaRed, replaceVars, shiftFreeVars, *]

  have h₁ :
    betaRed (app succDBI (fromNat n))
    = some (abst (abst (app (var 1) (app (app (fromNat n) (var 1)) (var 0)))))
    := by simp [succDBI, fromNat, betaRed, shiftFreeVars, replaceVars, step1Helper, step1Helper2]

  have h₂ :
    betaRed (abst (abst (app (var 1) (app (app (fromNat n) (var 1)) (var 0)))))
    = some
      (abst
        (abst
          (app
            (var 1)
            (app
              (abst (replaceVars 1 (var 1) (fromNatAux n)))
              (var 0)))))
    := by simp [succDBI, fromNat, betaRed, shiftFreeVars, replaceVars, tFromNatAuxNf]

  have h₃ :
    betaRed
      (abst
        (abst
          (app
            (var 1)
            (app
              (abst (replaceVars 1 (var 1) (fromNatAux n)))
              (var 0)))))
    = some (abst (abst (app (var 1) (fromNatAux n))))
    := by simp [succDBI, fromNat, betaRed, shiftFreeVars, step3Helper, step3Helper2]

  have h₄ :
    (betaRed (app succDBI (fromNat n)) >>= betaRed >>= betaRed)
    = some (abst (abst (app (var 1) (fromNatAux n))))
    := by simp [h₁, h₂, h₃]

  have h₅ :
    abst (abst (app (var 1) (fromNatAux n)))
    = fromNat (n + 1)
    := by simp [fromNatAux, fromNat]

  simp [h₁, h₂, h₃, h₄, h₅]

example : reduceEq10000 (fromNat 0) num0DBI := by rfl
example : reduceEq10000 (fromNat 1) num1DBI := by rfl
example : reduceEq10000 (fromNat 2) (app succDBI num1DBI) := by rfl
example : reduceEq10000 (fromNat 3) (app succDBI (app succDBI num1DBI)) := by rfl

example :
    reduceEq10000
      (app DBINegate falseDBI)
      trueDBI
    = true := by rfl

example :
    reduceEq10000
      (app DBINegate trueDBI)
      falseDBI
    = true := by rfl

example :
    reduceEq10000
      (app (app (app ifThenElseDBI trueDBI) falseDBI) trueDBI)
      falseDBI
    = true := by
    rfl

example : eval10000 trueDBI = "λ. λ. #1" := by rfl
example : eval10000 falseDBI= "λ. λ. #0" := by rfl
example : eval10000 ifThenElseDBI = "λ. λ. λ. ((#2) (#1)) (#0)" := by rfl
example : eval10000 compDBI = "λ. λ. λ. (#2) ((#1) (#0))" := by rfl

-- Contract input is a Nat
structure Contract where
  code : Expr
  bound : Nat
  prop : ∀ x : Nat, betaRed (reduceN (Expr.app code (fromNat x)) bound) = none

-- Execute a contract
def exec (c : Contract) (n : Nat) : Expr :=
  reduceN (Expr.app c.code (fromNat n)) c.bound

def idContract: Contract :=
  {
    code := idDBI,
    bound := 1,
    prop := by
      intro x
      have h1 : betaRed (fromNat x) = none := by
        simp [tFromNatIsReduced]
      have h3 : betaRed (Expr.app idDBI (fromNat x)) = fromNat x := by
        simp [h1, tIdIsIdForReduced]
      have h4 : reduceN (Expr.app idDBI (fromNat x)) 1 = fromNat x := by
        simp [reduceN, *]
      simp [*]
  }

def add1Contract: Contract :=
  {
    code := succDBI,
    bound := 3,
    prop := by simp [tSuccWorks, tFromNatIsReduced]
  }

end DBI
