module

public import PaperVerification.NegativeWeightedGrading
public import PaperVerification.HomogeneousQuotientBasis
public import PaperVerification.JacobianFreeness
import Lean.Elab.Tactic.Omega

/-!
# The exact integer grading of the Milnor quotient

This grading negates polynomial degree. Its piece at `-d` is the actual
degree-`d` quotient component, and all positive pieces are proved zero. Thus
shifted direct sums include all tower exponents while interpreting negative
polynomial degrees as zero, exactly as in the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial

namespace PaperVerification.NegativeWeightedGrading

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem submodule_homogeneous (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) :
    DirectSum.SetLike.IsHomogeneous (grading (K := K) w).piece U := by
  rw [grading, TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
  intro p f hf
  have he :
      (DirectSum.decompose (weightedHomogeneousSubmodule K (negativeWeights w)) f p : P) =
        weightedHomogeneousComponent (negativeWeights w) p f :=
    weightedDecomposition.decompose'_apply K (negativeWeights w) f p
  rw [he]
  by_cases hp : 0 < p
  · rw [component_positive_eq_zero w f p hp]
    exact U.zero_mem
  · have hp' : p = -(((-p).toNat : ℕ) : ℤ) := by omega
    rw [hp', component_negative_nat]
    exact hU _ f hf

def quotientGrading (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) :
    TauCeti.InternalGrading K (P ⧸ U) :=
  (grading w).quotient U (submodule_homogeneous w U hU)

theorem quotientGrading_piece (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) (p : ℤ) :
    (quotientGrading w U hU).piece p =
      (weightedHomogeneousSubmodule K (negativeWeights w) p).map U.mkQ := by
  simp only [quotientGrading, TauCeti.InternalGrading.quotient_piece,
    grading, TauCeti.InternalGrading.ofDecomposition_piece, LinearMap.restrictScalars_self]

theorem quotientGrading_piece_negative_nat (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U) (d : ℕ) :
    (quotientGrading w U hU).piece (-(d : ℤ)) =
      EulerResonance.quotientComponent w d U := by
  rw [quotientGrading_piece, EulerResonance.quotientComponent_eq_map]
  congr 1
  ext f
  exact homogeneous_negative_iff w f d

theorem quotientGrading_piece_positive (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d f, f ∈ U → weightedHomogeneousComponent w d f ∈ U)
    (p : ℤ) (hp : 0 < p) : (quotientGrading w U hU).piece p = ⊥ := by
  rw [quotientGrading_piece]
  have hz := piece_positive_eq_bot (K := K) w p hp
  rw [grading, TauCeti.InternalGrading.ofDecomposition_piece] at hz
  rw [hz, Submodule.map_bot]

end PaperVerification.NegativeWeightedGrading

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]
local notation "P" => MvPolynomial ι K

def milnorNegativeGrading (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) : TauCeti.InternalGrading K (MilnorQuotient F) :=
  NegativeWeightedGrading.quotientGrading w (jacobianSubmodule F)
    (homogeneousComponent_mem_jacobian F w h hF)

theorem milnorNegativeGrading_piece (F : P) (w : ι → ℕ) (h d : ℕ)
    (hF : F.IsWeightedHomogeneous w h) :
    (milnorNegativeGrading F w h hF).piece (-(d : ℤ)) =
      EulerResonance.quotientComponent w d (jacobianSubmodule F) :=
  NegativeWeightedGrading.quotientGrading_piece_negative_nat w _ _ d

theorem milnorNegativeGrading_positive (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (p : ℤ) (hp : 0 < p) :
    (milnorNegativeGrading F w h hF).piece p = ⊥ :=
  NegativeWeightedGrading.quotientGrading_piece_positive w _ _ p hp

/-- A section preserving every ordinary homogeneous degree also preserves
the full integer grading after passage to the actual Brieskorn module. -/
theorem classOf_section_homogeneous (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (s : MilnorQuotient F →ₗ[K] P)
    (hs : ∀ d x, x ∈ EulerResonance.quotientComponent w d (jacobianSubmodule F) →
      (s x).IsWeightedHomogeneous w d)
    (p : ℤ) (x : MilnorQuotient F)
    (hx : x ∈ (milnorNegativeGrading F w h hF).piece p) :
    classOf F (s x) ∈ (brieskornGrading F w h hF).piece p := by
  by_cases hp : 0 < p
  · rw [milnorNegativeGrading_positive F w h hF p hp] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero, map_zero]
    exact Submodule.zero_mem _
  · have hp' : p = -(((-p).toNat : ℕ) : ℤ) := by omega
    rw [hp'] at hx ⊢
    rw [milnorNegativeGrading_piece] at hx
    apply (mem_brieskornGrading_piece F w h hF _ _).mpr
    exact ⟨s x,
      (NegativeWeightedGrading.homogeneous_negative_iff w (s x) (-p).toNat).mpr
        (hs _ x hx), rfl⟩

end PaperVerification.JacobianDivergence
