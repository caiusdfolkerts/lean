import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Genuine direct sums concentrated in one degree

The inclusion from the only possible nonzero summand is a surjective linear
map. Consequently a finite relative group in that degree gives a finite
total direct sum, with the same rank bound. This uses the ordinary algebraic
direct sum over every degree, without a truncation or a degree bound.
-/

namespace PaperVerification.DirectSumConcentration

noncomputable section

open scoped DirectSum

variable {K ι : Type*} [Field K] [DecidableEq ι]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

theorem inclusion_surjective (d : ι)
    (hzero : ∀ i, i ≠ d → Subsingleton (V i)) :
    Function.Surjective (DirectSum.lof K ι V d) := by
  classical
  intro x
  refine ⟨x d, ?_⟩
  ext i
  by_cases hi : i = d
  · subst i
    change (DFinsupp.single d (x d)) d = x d
    exact DFinsupp.single_eq_same
  · letI := hzero i hi
    exact Subsingleton.elim _ _

/-- This equivalence is induced by the actual inclusion of the single
nonzero summand. -/
def equivalence (d : ι) (hzero : ∀ i, i ≠ d → Subsingleton (V i)) :
    V d ≃ₗ[K] ⨁ i, V i := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.lof K ι V d)
    ⟨DirectSum.of_injective (β := V) d, inclusion_surjective (K := K) V d hzero⟩

theorem finite_and_finrank_le (d : ι)
    (hzero : ∀ i, i ≠ d → Subsingleton (V i))
    [Module.Finite K (V d)] (b : ℕ) (hbound : Module.finrank K (V d) ≤ b) :
    Module.Finite K (⨁ i, V i) ∧ Module.finrank K (⨁ i, V i) ≤ b := by
  let e := equivalence (K := K) V d hzero
  exact ⟨Module.Finite.equiv e, by simpa only [← e.finrank_eq] using hbound⟩

/-- Degreewise exact maps remain exact on the genuine direct sums over
all degrees. -/
theorem range_eq_ker {A B C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (f : ∀ i, A i →ₗ[K] B i) (g : ∀ i, B i →ₗ[K] C i)
    (hexact : ∀ i, LinearMap.range (f i) = LinearMap.ker (g i)) :
    LinearMap.range (DirectSum.lmap f) = LinearMap.ker (DirectSum.lmap g) := by
  simp only [DirectSum.range_lmap, DirectSum.ker_lmap, hexact]

end
end PaperVerification.DirectSumConcentration
