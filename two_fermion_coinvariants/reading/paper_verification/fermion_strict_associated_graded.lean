module

public import PaperVerification.FermionStrictInitial
public import PaperVerification.FermionPairedAssociatedGraded

/-!
# The actual strict associated graded with both odd weights zero

The source filtration is independently defined on the original strict
quotient, using only polynomial weights. Its algebra structure is induced
from actual quotient multiplication. The canonical comparison is graded
and sends each bounded representative to its highest polynomial form.

-/

@[expose] public section
set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped DirectSum

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictAssociatedGraded_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def strictQuotientFiltration (d : StrictData (K := R) (n := n)) :
    FilteredAlgebra.Filtration R (StrictQuotient d.beta d.phi) :=
  BasisFiltered.quotientFiltration (superMonomialBasis (K := R)) (strictSuperWeight d)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))

abbrev StrictAssociatedGraded (d : StrictData (K := R) (n := n)) :=
  FilteredAlgebra.AssociatedGraded (strictQuotientFiltration d)

def strictPowerWeightedPiece (d : StrictData (K := R) (n := n)) (k : ℕ) :
    Submodule R (StrictQuotient d.beta (fun i ↦ X i^d.r i)) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (strictSuperWeight d) k).map
    ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap

theorem strictPower_kernel_component (d : StrictData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n)
    (hx : x ∈ (((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap).ker) :
    BasisFiltered.component (superMonomialBasis (K := R)) (strictSuperWeight d) k x ∈
      (((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap).ker := by
  rw [strictPower_kernel_eq_relationSpan] at hx ⊢
  apply BasisFiltered.component_mem_span (superMonomialBasis (K := R)) (strictSuperWeight d)
    (basisRelationMultiple superMonomialBasis (strictPowerFiniteRelation d))
    (strictRelationMultipleDegree d) _ x hx k
  intro z
  have h := BasisFiltered.homogeneous_component (superMonomialBasis (K := R)) (strictSuperWeight d)
    (strictRelationMultipleDegree d z)
    (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z)
  rwa [(strictRelationMultiple_hasTop d z).2] at h

theorem strictPowerWeighted_isInternal (d : StrictData (K := R) (n := n)) :
    DirectSum.IsInternal (strictPowerWeightedPiece d) := by
  have hclass (z : StrictPowerIndex d.r) :
      ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap
        (superMonomialBasis (z.2.val.val,z.1)) = strictArbitraryRingBasis d.power z := by
    change ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R)
      (superMonomialBasis (z.2.val.val,z.1)) = _
    exact (congrArg ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R)
      (superMonomialBasis_apply (K := R) (z.2.val.val,z.1))).trans
        (strictArbitraryRingBasis_apply d.power
          (show StrictPowerIndex d.power.r from z)).symm
  exact BasisFiltered.homogeneousQuotient_isInternal
    (R := R) (M := SuperRing R n)
    (Q := StrictQuotient d.beta (fun i ↦ X i^d.r i))
    (I := SuperMonomialIndex n) (E := StrictPowerIndex d.r)
    (superMonomialBasis (K := R)) (strictSuperWeight d)
    ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap
    (strictArbitraryRingBasis d.power)
    (fun z : StrictPowerIndex d.r ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ strictSuperWeight d (z.2.val.val,z.1))
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    hclass (strictPower_kernel_component d)

theorem strict_initial_kernel_le_power (d : StrictData (K := R) (n := n)) :
    BasisFiltered.initialSubmodule (superMonomialBasis (K := R)) (strictSuperWeight d)
      (((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap).ker ≤
        (((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap).ker := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule,quotient_kernel_eq_twoSidedIdealSubmodule]
  exact (strict_initialSubmodule_eq_power d).le

set_option maxHeartbeats 100000 in
/-- The actual strict highest-component homomorphism, using the comparison
already proved for symbolic quotient ideals. -/
def strictAssociatedGradedHom (d : StrictData (K := R) (n := n)) :
    StrictAssociatedGraded d →ₐ[R] StrictQuotient d.beta (fun i ↦ X i^d.r i) :=
  pairedSymbolicComparisonHom (R := R) (n := n)
    (strictIdeal d.beta d.phi)
    (strictIdeal d.beta (fun i ↦ X i^d.r i))
    (superMonomialBasis (K := R) (n := n)) (strictSuperWeight d)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (basisRelationMultiple (superMonomialBasis (K := R) (n := n)) (strictFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := R) (n := n)) (strictPowerFiniteRelation d))
    (strictRelationMultipleDegree d) (strictRelationMultiple_hasTop d)
    (strict_quotient_kernel_eq_relationSpan R d)
    (strictPower_kernel_eq_relationSpan d)
    (strict_initial_kernel_le_power d)

set_option maxHeartbeats 100000 in
theorem strictAssociatedGradedHom_bijective (d : StrictData (K := R) (n := n)) :
    Function.Bijective (strictAssociatedGradedHom d) :=
  pairedSymbolicComparisonHom_bijective (R := R) (n := n)
    (strictIdeal d.beta d.phi)
    (strictIdeal d.beta (fun i ↦ X i^d.r i))
    (superMonomialBasis (K := R) (n := n)) (strictSuperWeight d)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (basisRelationMultiple (superMonomialBasis (K := R) (n := n)) (strictFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := R) (n := n)) (strictPowerFiniteRelation d))
    (strictRelationMultipleDegree d) (strictRelationMultiple_hasTop d)
    (strict_quotient_kernel_eq_relationSpan R d)
    (strictPower_kernel_eq_relationSpan d)
    (strict_initial_kernel_le_power d)
    (strictPowerWeighted_isInternal d)

set_option maxHeartbeats 100000 in
def strictAssociatedGradedEquiv (d : StrictData (K := R) (n := n)) :
    StrictAssociatedGraded d ≃ₐ[R] StrictQuotient d.beta (fun i ↦ X i^d.r i) :=
  AlgEquiv.ofBijective (strictAssociatedGradedHom d)
    (strictAssociatedGradedHom_bijective d)

@[simp] theorem strictAssociatedGradedEquiv_of_projection
    (d : StrictData (K := R) (n := n)) (k : ℕ)
    (x : BasisFiltered.boundPiece (superMonomialBasis (K := R)) (strictSuperWeight d) k) :
    strictAssociatedGradedEquiv d
      (DirectSum.of (FilteredAlgebra.GradedPiece (strictQuotientFiltration d)) k
        (BasisFiltered.gradedProjection
          (R := R) (A := SuperRing R n) (Q := StrictQuotient d.beta d.phi)
          (I := SuperMonomialIndex n)
          (superMonomialBasis (K := R)) (strictSuperWeight d)
          ((strictIdeal d.beta d.phi).ringCon.mkₐ R)
          (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0)) (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0)) k x))=
      ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R)
        (BasisFiltered.component (superMonomialBasis (K := R)) (strictSuperWeight d) k x) :=
  BasisFiltered.associatedGradedComparison_of_projection
    _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      constructor
      · intro a b hab
        apply (strictPowerWeighted_isInternal d).1
        exact hab
      · intro y
        obtain ⟨a,ha⟩ := (strictPowerWeighted_isInternal d).2 y
        exact ⟨a,ha⟩) k x

theorem strictAssociatedGradedEquiv_range (d : StrictData (K := R) (n := n)) (k : ℕ) :
    LinearMap.range ((strictAssociatedGradedEquiv d).toLinearMap.comp
      (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (strictQuotientFiltration d)) k))=
        strictPowerWeightedPiece d k :=
  BasisFiltered.associatedGradedComparison_range
    _ _ _ _ _ _ _ _ _ _ _ _ _ (by
      constructor
      · intro a b hab
        apply (strictPowerWeighted_isInternal d).1
        exact hab
      · intro y
        obtain ⟨a,ha⟩ := (strictPowerWeighted_isInternal d).2 y
        exact ⟨a,ha⟩) k

/-- Clearing the positive covering denominator gives exactly the paper's
polynomial weights, and contributes zero for every exterior generator. -/
theorem strictSuperWeight_le_iff (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n) (k : ℕ) :
    strictSuperWeight d z≤k ↔ monomialWeight d.r z.1≤(k : ℚ)/(∏ i,d.r i : ℕ) := by
  have hp : (0 : ℚ)<(∏ i,d.r i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ ↦ d.positive_r i)
  rw [le_div_iff₀ hp,monomialWeight_mul_coveringProduct d.r d.positive_r,strictSuperWeight_apply]
  norm_cast

theorem strictSuperWeight_eq_iff (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n) (k : ℕ) :
    strictSuperWeight d z=k ↔ monomialWeight d.r z.1=(k : ℚ)/(∏ i,d.r i : ℕ) := by
  have hp : (∏ i,d.r i : ℕ)≠(0 : ℚ) := by
    exact_mod_cast (Finset.prod_pos (fun i _ ↦ d.positive_r i)).ne'
  rw [eq_div_iff hp,monomialWeight_mul_coveringProduct d.r d.positive_r,strictSuperWeight_apply]
  norm_cast

theorem strict_bound_iff_rational (d : StrictData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n) :
    BasisFiltered.Bound (superMonomialBasis (K := R)) (strictSuperWeight d) k x ↔
      ∀ z,(superMonomialBasis (K := R)).repr x z≠0 →
        monomialWeight d.r z.1≤(k : ℚ)/(∏ i,d.r i : ℕ) := by
  simp only [BasisFiltered.Bound,strictSuperWeight_le_iff]

theorem strict_homogeneous_iff_rational (d : StrictData (K := R) (n := n))
    (k : ℕ) (x : SuperRing R n) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (strictSuperWeight d) k x ↔
      ∀ z,(superMonomialBasis (K := R)).repr x z≠0 →
        monomialWeight d.r z.1=(k : ℚ)/(∏ i,d.r i : ℕ) := by
  simp only [BasisFiltered.Homogeneous,strictSuperWeight_eq_iff]

end PaperVerification.Fermion
