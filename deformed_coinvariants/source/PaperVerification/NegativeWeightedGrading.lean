module

public import PaperVerification.JacobianGrading
public import TauCeti.Algebra.Module.GradedModule.Quotient

/-!
# The bounded integer grading on a positive-weight polynomial ring

Negating the usual natural-number weights gives a grading bounded above.
The statements here identify its components with the actual polynomial
components, including all the zero positive-degree pieces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.NegativeWeightedGrading

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def negativeWeights (w : ι → ℕ) : ι → ℤ := fun i => -(w i : ℤ)

theorem weight_negative (w : ι → ℕ) (a : ι →₀ ℕ) :
    Finsupp.weight (negativeWeights w) a = -(Finsupp.weight w a : ℤ) := by
  simp [Finsupp.weight_eq_sum, negativeWeights, nsmul_eq_mul,
    Finset.sum_neg_distrib]

theorem homogeneous_negative_iff (w : ι → ℕ) (f : P) (d : ℕ) :
    f.IsWeightedHomogeneous (negativeWeights w) (-(d : ℤ)) ↔
      f.IsWeightedHomogeneous w d := by
  simp only [IsWeightedHomogeneous, weight_negative, neg_inj, Nat.cast_inj]

theorem component_negative_nat (w : ι → ℕ) (f : P) (d : ℕ) :
    weightedHomogeneousComponent (negativeWeights w) (-(d : ℤ)) f =
      weightedHomogeneousComponent w d f := by
  classical
  ext a
  simp only [coeff_weightedHomogeneousComponent, weight_negative,
    neg_inj, Nat.cast_inj]

theorem component_positive_eq_zero (w : ι → ℕ) (f : P) (p : ℤ) (hp : 0 < p) :
    weightedHomogeneousComponent (negativeWeights w) p f = 0 := by
  classical
  ext a
  have ha : Finsupp.weight (negativeWeights w) a ≠ p := by
    rw [weight_negative]
    have hn : (0 : ℤ) ≤ (Finsupp.weight w a : ℤ) := Nat.cast_nonneg _
    omega
  simp [coeff_weightedHomogeneousComponent, ha]

theorem homogeneous_positive_eq_zero (w : ι → ℕ) (f : P) (p : ℤ)
    (hp : 0 < p) (hf : f.IsWeightedHomogeneous (negativeWeights w) p) : f = 0 := by
  rw [← hf.weightedHomogeneousComponent_same]
  exact component_positive_eq_zero w f p hp

def grading (w : ι → ℕ) : TauCeti.InternalGrading K P :=
  .ofDecomposition (weightedHomogeneousSubmodule K (negativeWeights w))

@[simp] theorem mem_piece (w : ι → ℕ) (p : ℤ) (f : P) :
    f ∈ (grading (K := K) w).piece p ↔
      f.IsWeightedHomogeneous (negativeWeights w) p := by
  rw [grading, TauCeti.InternalGrading.ofDecomposition_piece]
  rfl

theorem piece_positive_eq_bot (w : ι → ℕ) (p : ℤ) (hp : 0 < p) :
    (grading (K := K) w).piece p = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  exact homogeneous_positive_eq_zero w f p hp ((mem_piece w p f).mp hf)

theorem grading_boundedAbove (w : ι → ℕ) :
    BddAbove {p | (grading (K := K) w).piece p ≠ ⊥} := by
  refine ⟨0, ?_⟩
  intro p hp
  by_contra h
  exact hp (piece_positive_eq_bot w p (lt_of_not_ge h))

/-- Homogeneity of the actual divergence subspace, with no ideal assumption. -/
theorem divergenceSpace_homogeneous [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h) :
    DirectSum.SetLike.IsHomogeneous (grading (K := K) w).piece
      (JacobianDivergence.divergenceSpace F) := by
  rw [grading, TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
  intro p f hf
  have he :
      (DirectSum.decompose (weightedHomogeneousSubmodule K (negativeWeights w)) f p : P) =
      weightedHomogeneousComponent (negativeWeights w) p f :=
    weightedDecomposition.decompose'_apply K (negativeWeights w) f p
  rw [he]
  by_cases hp : 0 < p
  · rw [component_positive_eq_zero w f p hp]
    exact Submodule.zero_mem _
  · have hp' : p = -(((-p).toNat : ℕ) : ℤ) := by omega
    rw [hp', component_negative_nat]
    exact JacobianDivergence.homogeneousComponent_mem_divergenceSpace F w h hF f hf _

end PaperVerification.NegativeWeightedGrading
