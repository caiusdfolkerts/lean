module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Tactic.Ring

/-!
# Polynomial divergence and the Lie cocycle identity

Divergence is the coordinate sum of the actual partial derivatives of a
polynomial derivation's coefficients.  Its product and commutator rules
are proved from the polynomial Leibniz rule and equality of mixed partials.
No divergence or Lie-cocycle identity is included as an extra assumption.

This is supporting source for the differential normal-form construction;
it has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.PolynomialDivergence

open MvPolynomial
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

theorem summed_derivation_apply {α : Type*} (s : Finset α) (D : α → Der) (p : P) :
    (∑ i ∈ s, D i) p = ∑ i ∈ s, D i p := by
  have h := congrFun
    ((Derivation.coeFnAddMonoidHom (R := K) (A := P) (M := P)).map_sum D s) p
  simpa only [Derivation.coeFnAddMonoidHom_apply,Finset.sum_apply] using h

/-- Every polynomial derivation is its literal coordinate expansion. -/
theorem coordinate_expansion (D : Der) : D = ∑ i, D (X i) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  simp only [summed_derivation_apply,Derivation.smul_apply,smul_eq_mul,pderiv_X]
  simp [Pi.single_apply]

theorem apply_eq_sum (D : Der) (p : P) : D p = ∑ i, D (X i) * pderiv i p := by
  conv_lhs => rw [coordinate_expansion D]
  simp only [summed_derivation_apply,Derivation.smul_apply,smul_eq_mul]

/-- Divergence relative to the coordinate volume form. -/
def divergence : Der →ₗ[K] P where
  toFun D := ∑ i, pderiv i (D (X i))
  map_add' D E := by
    simp only [Derivation.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' a D := by
    simp only [Derivation.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

@[simp] theorem divergence_apply (D : Der) :
    divergence D = ∑ i, pderiv i (D (X i)) := rfl

/-- The coefficient-ring linearity fails by exactly the anchor term. -/
theorem divergence_polynomial_smul (a : P) (D : Der) :
    divergence (a • D) = a * divergence D + D a := by
  simp only [divergence_apply,Derivation.smul_apply,smul_eq_mul,pderiv_mul,
    Finset.sum_add_distrib,Finset.mul_sum]
  rw [apply_eq_sum D a]
  have h : (∑ i, pderiv i a * D (X i)) = ∑ i, D (X i) * pderiv i a := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [h,add_comm]

/-- The commutator of a coordinate partial and a polynomial derivation. -/
theorem pderiv_apply (D : Der) (p : P) (i : ι) :
    pderiv i (D p) =
      D (pderiv i p) + ∑ j, pderiv i (D (X j)) * pderiv j p := by
  rw [apply_eq_sum D p,map_sum]
  simp only [pderiv_mul,Finset.sum_add_distrib]
  rw [apply_eq_sum D (pderiv i p)]
  have h : (∑ j, D (X j) * pderiv i (pderiv j p)) =
      ∑ j, D (X j) * pderiv j (pderiv i p) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [pderiv_comm i j p]
  rw [h,add_comm]

theorem cross_terms_swap (D E : Der) :
    (∑ i, ∑ j, pderiv i (D (X j)) * pderiv j (E (X i))) =
      ∑ i, ∑ j, pderiv i (E (X j)) * pderiv j (D (X i)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem sum_pderiv_derivation_coefficients (D E : Der) :
    (∑ i, pderiv i (D (E (X i)))) = D (divergence E) +
      ∑ i, ∑ j, pderiv i (D (X j)) * pderiv j (E (X i)) := by
  calc
    (∑ i, pderiv i (D (E (X i)))) =
        ∑ i, (D (pderiv i (E (X i))) +
          ∑ j, pderiv i (D (X j)) * pderiv j (E (X i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pderiv_apply D (E (X i)) i
    _ = _ := by simp only [Finset.sum_add_distrib,divergence_apply,map_sum]

/-- Divergence is an actual Lie cocycle. -/
theorem divergence_commutator (D E : Der) :
    divergence ⁅D,E⁆ = D (divergence E) - E (divergence D) := by
  change (∑ i, pderiv i (⁅D,E⁆ (X i))) = _
  simp only [Derivation.commutator_apply,map_sub,Finset.sum_sub_distrib]
  rw [sum_pderiv_derivation_coefficients,sum_pderiv_derivation_coefficients]
  rw [cross_terms_swap D E]
  ring

/-- The divergence operator on a polynomial multiple of a fixed field. -/
def divergenceOperator (D : Der) : P →ₗ[K] P :=
  D.toLinearMap + LinearMap.mulLeft K (divergence D)

@[simp] theorem divergenceOperator_apply (D : Der) (p : P) :
    divergenceOperator D p = D p + divergence D * p := rfl

theorem divergenceOperator_eq (D : Der) (p : P) :
    divergenceOperator D p = divergence (p • D) := by
  rw [divergenceOperator_apply,divergence_polynomial_smul]
  ring

/-- The right-coefficient identity that makes the joint image independent
of the chosen polynomial basis of the vector-field module. -/
theorem divergenceOperator_polynomial_smul (a : P) (D : Der) (p : P) :
    divergenceOperator (a • D) p = divergenceOperator D (a*p) := by
  rw [divergenceOperator_eq,divergenceOperator_eq,smul_smul]
  congr 1
  exact mul_comm p a

/-- Divergence-corrected derivations represent the same Lie bracket. -/
theorem divergenceOperator_commutator (D E : Der) (p : P) :
    divergenceOperator D (divergenceOperator E p) -
      divergenceOperator E (divergenceOperator D p) =
        divergenceOperator ⁅D,E⁆ p := by
  simp only [divergenceOperator_apply,map_add,Derivation.leibniz,smul_eq_mul,
    Derivation.commutator_apply,divergence_commutator]
  ring

end PaperVerification.PolynomialDivergence
