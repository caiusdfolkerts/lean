module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Basic
public import Lean.Elab.Tactic.Omega

/-!
# A genuine all-degree shift of a graded vector space

Removing an initial segment of zero groups preserves the actual direct sum.
The map is restriction of finitely supported functions, and its inverse is
extension by zero. This is the all-degree form of the Thom degree shift.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DirectSumShift

open scoped DirectSum

variable {K : Type*} [Field K] (V : ℕ → Type*)
  [∀ n, AddCommGroup (V n)] [∀ n, Module K (V n)]

/-- Restrict the actual finitely supported family to degrees at least `d`. -/
def restriction (d : ℕ) : (⨁ n : ℕ, V n) →ₗ[K] ⨁ n : ℕ, V (d+n) where
  toFun := DFinsupp.comapDomain (fun n => d+n) (fun _ _ h => Nat.add_left_cancel h)
  map_add' := DFinsupp.comapDomain_add _ _
  map_smul' := DFinsupp.comapDomain_smul _ _

@[simp] theorem restriction_apply (d : ℕ) (x : ⨁ n : ℕ, V n) (n : ℕ) :
    restriction (K := K) V d x n = x (d+n) := rfl

/-- Every shifted finitely supported family extends by zero. -/
theorem restriction_surjective (d : ℕ) : Function.Surjective (restriction (K := K) V d) := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0,map_zero _⟩
  | add x y hx hy =>
      obtain ⟨a,rfl⟩ := hx
      obtain ⟨b,rfl⟩ := hy
      exact ⟨a+b,map_add _ _ _⟩
  | of n x =>
      refine ⟨DirectSum.of V (d+n) x,?_⟩
      exact DFinsupp.comapDomain_single (fun n => d+n) (fun _ _ h => Nat.add_left_cancel h) n x

/-- Restriction loses nothing when precisely the discarded groups vanish. -/
theorem restriction_injective (d : ℕ)
    (hz : ∀ n < d, Subsingleton (V n)) :
    Function.Injective (restriction (K := K) V d) := by
  intro x y h
  ext n
  by_cases hn : n < d
  · letI := hz n hn
    exact Subsingleton.elim _ _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show d ≤ n from by omega)
    exact congrArg (fun z => z m) h

/-- The full direct sum is isomorphic to its genuine degree shift. -/
def equivalence (d : ℕ) (hz : ∀ n < d, Subsingleton (V n)) :
    (⨁ n : ℕ, V n) ≃ₗ[K] ⨁ n : ℕ, V (d+n) :=
  LinearEquiv.ofBijective (restriction V d)
    ⟨restriction_injective V d hz, restriction_surjective V d⟩

/-- Degreewise isomorphisms after a shift give an all-degree isomorphism. -/
def ofDegreewiseEquivalences (d : ℕ) (hz : ∀ n < d, Subsingleton (V n))
    (W : ℕ → Type*) [∀ n, AddCommGroup (W n)] [∀ n, Module K (W n)]
    (e : ∀ n, W n ≃ₗ[K] V (d+n)) :
    (⨁ n : ℕ, W n) ≃ₗ[K] ⨁ n : ℕ, V n :=
  (DirectSum.congrLinearEquiv e).trans (equivalence V d hz).symm

end PaperVerification.DirectSumShift
