module

public import PaperVerification.HomogeneousRegularSequence
public import Mathlib.RingTheory.Nullstellensatz

/-!
# From the actual common zero set to regularity

This file closes the algebraic-geometry step over an algebraically closed field:
if a full-length homogeneous sequence vanishes at the origin and has no other
common zero, it is regular. The zero-set hypothesis is about evaluation of the
actual defining polynomials, not a substitute definition of regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence

namespace PaperVerification.HomogeneousLocalization

variable {K ι : Type*} [Field K] [IsAlgClosed K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem origin_le_radical_of_zeroLocus
    (I : Ideal P) (hzero : ∀ x ∈ zeroLocus K I, x = 0) :
    originIdeal (K := K) (ι := ι) ≤ I.radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro f hf x hx
  rw [hzero x hx, aeval_zero, Algebra.algebraMap_self]
  exact hf

/-- A full sequence with the origin as its entire common zero set is regular. -/
theorem homogeneous_parameters_regular_of_common_zero
    (w : ι → ℕ) (hw : ∀ i, w i ≠ 0)
    (rs : List P) (hhom : ∀ f ∈ rs, ∃ d, f.IsWeightedHomogeneous w d)
    (horigin : ∀ f ∈ rs, constantCoeff f = 0)
    (hzero : ∀ x : ι → K, (∀ f ∈ rs, aeval x f = 0) → x = 0)
    (hlen : rs.length = Fintype.card ι) : IsWeaklyRegular P rs := by
  apply homogeneous_parameters_regular w hw rs hhom horigin _ hlen
  apply origin_le_radical_of_zeroLocus
  intro x hx
  apply hzero x
  intro f hf
  exact hx f (Ideal.subset_span hf)

/-- Function-indexed version for actual polynomial families. -/
theorem homogeneous_family_regular_of_common_zero {n : ℕ}
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0)
    (f : Fin n → MvPolynomial (Fin n) K)
    (hhom : ∀ i, ∃ d, (f i).IsWeightedHomogeneous w d)
    (horigin : ∀ i, constantCoeff (f i) = 0)
    (hzero : ∀ x : Fin n → K, (∀ i, aeval x (f i) = 0) → x = 0) :
    IsWeaklyRegular (MvPolynomial (Fin n) K) (List.ofFn f) := by
  apply homogeneous_parameters_regular_of_common_zero w hw (List.ofFn f)
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hhom i
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact horigin i
  · intro x hx
    exact hzero x (fun i => hx (f i) (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · simp

end PaperVerification.HomogeneousLocalization
