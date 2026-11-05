module

public import PaperVerification.FermionNewtonRestrictionMap

/-!
# The exact denominator under coordinate restriction

Removing a coordinate splits the negative-edge product into the smaller
negative-edge product and the actual incident coordinate factors. The only
scalar is an explicit product of minus signs. This also proves the required
edge-count identity by comparing the degrees of nonzero polynomials.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem negativeDenominator_eq_double_product (σ : Fin n → ℤ) :
    negativeDenominator (F := F) σ =
      ∏ i, ∏ j, if i < j ∧ σ i = -1 then (X i - X j : MvPolynomial (Fin n) F) else 1 := by
  classical
  have h := Fintype.prod_of_injective
    (Subtype.val : Edge n → Fin n × Fin n) Subtype.val_injective
    (fun e : Edge n ↦ if σ e.1.1 = -1 then edgeLinear (F := F) e else 1)
    (fun a : Fin n × Fin n ↦ if a.1 < a.2 ∧ σ a.1 = -1 then X a.1 - X a.2 else 1)
    (by
      intro a ha
      have hlt : ¬ a.1 < a.2 := fun hlt ↦ ha ⟨⟨a,hlt⟩,rfl⟩
      simp only [hlt,false_and,ite_false])
    (by
      intro e
      simp only [e.property,true_and,edgeLinear])
  rw [Fintype.prod_prod_type] at h
  simpa only [negativeDenominator, Finset.prod_filter] using h

def restrictionOrientation (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) : F :=
  ∏ i : Fin n, if q < q.succAbove i ∧ σ q = -1 then -1 else 1

theorem restrictionOrientation_isUnit (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) :
    IsUnit (restrictionOrientation (F := F) σ q) := by
  apply IsUnit.prod_iff.mpr
  intro i hi
  split_ifs <;> simp

theorem incident_factor_identity (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) (i : Fin n) :
    (if q < q.succAbove i ∧ σ q = -1 then -(X i : MvPolynomial (Fin n) F) else 1) *
      (if q.succAbove i < q ∧ σ (q.succAbove i) = -1 then X i else 1) =
      C (if q < q.succAbove i ∧ σ q = -1 then (-1 : F) else 1) *
        (if incidentSign σ q i = -1 then X i else 1) := by
  rcases lt_or_gt_of_ne (Fin.succAbove_ne q i) with hi | hi
  · by_cases hσ : σ (q.succAbove i) = -1 <;>
      simp [incidentSign,hi,not_lt_of_gt hi,hσ]
  · by_cases hσ : σ q = -1 <;>
      simp [incidentSign,hi,not_lt_of_gt hi,hσ]

/-- Exact polynomial factorization, including its orientation scalar. -/
theorem removeCoordinate_negativeDenominator (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) :
    removeCoordinate q (negativeDenominator (F := F) σ) =
      C (restrictionOrientation (F := F) σ q) * coordinateProduct (negativeNeighbours σ q) *
        negativeDenominator (σ ∘ q.succAbove) := by
  classical
  rw [negativeDenominator_eq_double_product, map_prod,
    Fin.prod_univ_succAbove _ q]
  have hfirst : removeCoordinate (F := F) q
      (∏ j, if q < j ∧ σ q = -1 then X q - X j else 1) =
      ∏ i : Fin n, if q < q.succAbove i ∧ σ q = -1 then -X i else 1 := by
    rw [map_prod,Fin.prod_univ_succAbove _ q]
    simp only [lt_self_iff_false,false_and,ite_false,map_one,one_mul]
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp only [map_sub,removeCoordinate_X_self,
      removeCoordinate_X_succAbove,zero_sub,map_one]
  have hrow (i : Fin n) : removeCoordinate (F := F) q
      (∏ j, if q.succAbove i < j ∧ σ (q.succAbove i) = -1 then X (q.succAbove i) - X j else 1) =
      (if q.succAbove i < q ∧ σ (q.succAbove i) = -1 then X i else 1) *
        ∏ j : Fin n, if i < j ∧ σ (q.succAbove i) = -1 then X i - X j else 1 := by
    rw [map_prod,Fin.prod_univ_succAbove _ q]
    congr 1
    · split_ifs <;> simp only [map_sub,removeCoordinate_X_self,
        removeCoordinate_X_succAbove,sub_zero,map_one]
    · apply Finset.prod_congr rfl
      intro j hj
      simp only [Fin.succAbove_lt_succAbove_iff]
      split_ifs <;> simp only [map_sub,removeCoordinate_X_succAbove,map_one]
  rw [hfirst]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib,← mul_assoc,← Finset.prod_mul_distrib]
  simp_rw [incident_factor_identity]
  rw [Finset.prod_mul_distrib,← map_prod]
  change C (restrictionOrientation σ q) *
    (∏ i : Fin n, if incidentSign σ q i = -1 then X i else 1) * _ = _
  rw [show (∏ i : Fin n, if incidentSign σ q i = -1 then (X i : MvPolynomial (Fin n) F) else 1) =
    coordinateProduct (negativeNeighbours σ q) by
      simp only [coordinateProduct,negativeNeighbours,Finset.prod_filter]]
  congr 1
  exact (negativeDenominator_eq_double_product (F := F) (σ ∘ q.succAbove)).symm

theorem removeCoordinate_negativeDenominator_ne_zero
    (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) :
    removeCoordinate q (negativeDenominator (F := F) σ) ≠ 0 := by
  rw [removeCoordinate_negativeDenominator]
  exact mul_ne_zero (mul_ne_zero
    ((restrictionOrientation_isUnit (F := F) σ q).map MvPolynomial.C).ne_zero
    (coordinateProduct_ne_zero _)) (negativeDenominator_ne_zero _)

theorem negativeEdgeCount_restriction (σ : Fin (n + 1) → ℤ) (q : Fin (n + 1)) :
    negativeEdgeCount σ = (negativeNeighbours σ q).card + negativeEdgeCount (σ ∘ q.succAbove) := by
  have he := congrArg MvPolynomial.totalDegree
    (removeCoordinate_negativeDenominator (F := ℚ) σ q)
  have hleft := (removeCoordinate_homogeneous q (negativeDenominator_homogeneous (F := ℚ) σ)).totalDegree (removeCoordinate_negativeDenominator_ne_zero (F := ℚ) σ q)
  have hright := ((coordinateProduct_homogeneous (F := ℚ) (negativeNeighbours σ q)).C_mul
    (restrictionOrientation (F := ℚ) σ q)).mul
      (negativeDenominator_homogeneous (F := ℚ) (σ ∘ q.succAbove))
  have hright0 : C (restrictionOrientation (F := ℚ) σ q) *
      coordinateProduct (negativeNeighbours σ q) * negativeDenominator (σ ∘ q.succAbove) ≠ 0 := by
    rw [← removeCoordinate_negativeDenominator]
    exact removeCoordinate_negativeDenominator_ne_zero σ q
  rw [hleft,hright.totalDegree hright0] at he
  exact he

theorem columnNumeratorDegree_restriction
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1) (hc : Compatible δ σ)
    (q : Fin (n + 1)) (hq : DeletionVertex δ σ q) (i : Fin n) :
    columnNumeratorDegree δ σ (q.succAbove i) = (negativeNeighbours σ q).card +
      columnNumeratorDegree (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) i := by
  have hh := profileHeight_restricted δ σ hσ hc q hq i
  rw [profileHeight_eq_card_difference δ σ hσ,
    profileHeight_eq_card_difference (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)
      (fun j ↦ hσ (q.succAbove j))] at hh
  have hn := negativeEdgeCount_restriction σ q
  have hle := earlierNegative_card_le σ (q.succAbove i)
  have hle' := earlierNegative_card_le (σ ∘ q.succAbove) i
  unfold columnNumeratorDegree
  omega

end PaperVerification.Fermion.Newton
