module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# The four literal exterior marks and their path heights

These definitions are extracted unchanged from the endpoint and path modules.
The extraction separates finite enumeration from the polynomial-ideal proofs;
all original declaration names and definitions are preserved.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.Endpoint

/-- The four literal exterior occupation patterns. -/
inductive Mark
  | unmarked | theta | xi | double
  deriving DecidableEq

end PaperVerification.Fermion.Endpoint

namespace PaperVerification.Fermion.Paths

open Endpoint
open scoped BigOperators

instance mark_fintype : Fintype Mark where
  elems := {.unmarked,.theta,.xi,.double}
  complete m := by cases m <;> simp

theorem sum_mark {A : Type*} [AddCommMonoid A] (f : Mark → A) :
    ∑ m, f m = f .unmarked+f .theta+f .xi+f .double := by
  change (∑ m ∈ ({.unmarked,.theta,.xi,.double} : Finset Mark), f m)=_
  simp [add_assoc]

def markDegree : Mark → ℕ
  | .unmarked => 0
  | .theta => 1
  | .xi => 1
  | .double => 2

def advance (h : ℕ) : Mark → ℕ
  | .unmarked => h+1
  | .theta => h
  | .xi => h
  | .double => h-1

def pathHeight : {n : ℕ} → (Fin n → Mark) → ℕ
  | 0,_ => 0
  | n+1,m => advance (pathHeight (Fin.init m)) (m (Fin.last n))

end PaperVerification.Fermion.Paths
