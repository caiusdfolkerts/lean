module

public import PaperVerification.FermionDescendingBasisComparison
public import PaperVerification.FermionStrictWeightReesFibers

/-!
# The actual associated graded for smallest multiplicity weights

This is the direct sum of F_d/F_(d+1), with the product induced from the
original moment quotient. The filtration is rigorously identified with the
independently defined ambient-image filtration. The comparison with the
smallest-weight initial quotient uses the already proved exact structure
constants and is an algebra equivalence, not a dimension equality.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators DirectSum

namespace PaperVerification.Fermion


open MvPolynomial Exterior

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionMultiplicityAssociatedGraded_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- This multiplicative filtration is constructed from the actual quotient
basis; the next theorem proves it equals the original ambient-image filtration. -/
abbrev strictMultiplicityDescendingFiltration (d : StrictData (K := F) (n := n)) :
    DescendingAlgebra.Filtration F (StrictQuotient d.beta d.phi) :=
  DescendingBasis.filtration (K := F) (A := StrictQuotient d.beta d.phi)
    (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
    (strictBasisMultiplicityWeight_multiplicative d)

theorem strictMultiplicityDescendingFiltration_piece
    (d : StrictData (K := F) (n := n)) (r : ℕ) :
    (strictMultiplicityDescendingFiltration d).piece r=strictMultiplicityFiltration d r :=
  (strictMultiplicityFiltration_eq_basisTail d r).symm

/-- The actual direct sum of successive descending-filtration quotients. -/
abbrev StrictMultiplicityAssociatedGraded (d : StrictData (K := F) (n := n)) :=
  DescendingAlgebra.AssociatedGraded (strictMultiplicityDescendingFiltration d)

set_option maxHeartbeats 1000000 in
/-- All structure constants and the unit are inherited from the actual
initial algebra and were proved independently before this comparison. -/
def strictMultiplicityAssociatedGradedEquiv (d : StrictData (K := F) (n := n)) :
    StrictMultiplicityAssociatedGraded d ≃ₐ[F] StrictMultiplicityInitialQuotient d := by
  let b := strictCoupledBasis d
  let w := strictBasisMultiplicityWeight d
  have hweight := strictBasisMultiplicityWeight_multiplicative d
  let c := strictMultiplicityInitialBasis d
  let makeEquiv := DescendingBasis.comparisonAlgEquiv
    (K := F) (A := StrictQuotient d.beta d.phi) (I := StrictPowerIndex d.r)
    (B := StrictMultiplicityInitialQuotient d)
    (b := b) (w := w) (hmul := hweight) (c := c)
  let e := makeEquiv
    (by
      dsimp only [b,w,c]
      rw [strictInitial_basis_one d]
      apply Finset.sum_congr rfl
      intro i hi
      rw [WeightRees.unitPolynomial_eval_zero (K := F)
        (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
        (strictBasisMultiplicityWeight d) i]
      split_ifs <;> simp only [zero_smul])
    (by
      dsimp only [b,w,c]
      intro i j
      rw [strictInitial_basis_mul d i j]
      apply Finset.sum_congr rfl
      intro k hk
      rw [WeightRees.multiplicationPolynomial_eval_zero (K := F)
        (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
        (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d) i j k]
      split_ifs <;> simp only [zero_smul])
  exact e

/-- The comparison takes the actual graded class of each original basis
representative to its actual initial class, with exactly the same weight. -/
@[simp] theorem strictMultiplicityAssociatedGradedEquiv_basis
    (d : StrictData (K := F) (n := n)) (i : StrictPowerIndex d.r) :
    strictMultiplicityAssociatedGradedEquiv d
      (DescendingBasis.gradedBasis (K := F) (A := StrictQuotient d.beta d.phi)
        (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
        (strictBasisMultiplicityWeight_multiplicative d) i)=
      strictMultiplicityInitialBasis d i :=
  DescendingBasis.comparison_basis _ _ _ _ i

/-- The full quotient representatives determine the comparison in every
degree; larger weights are exactly those killed by the next-step quotient. -/
theorem strictMultiplicityAssociatedGradedEquiv_of_mk
    (d : StrictData (K := F) (n := n)) (r : ℕ)
    (x : (strictMultiplicityDescendingFiltration d).piece r) :
    strictMultiplicityAssociatedGradedEquiv d
      (DirectSum.of (DescendingAlgebra.GradedPiece (strictMultiplicityDescendingFiltration d))
        r (Submodule.Quotient.mk x))=
      ∑ i : StrictPowerIndex d.r,
        if strictBasisMultiplicityWeight d i=r then
          (strictCoupledBasis d).repr x i • strictMultiplicityInitialBasis d i else 0 := by
  change (strictCoupledBasis d).equiv (strictMultiplicityInitialBasis d)
    (Equiv.refl (StrictPowerIndex d.r))
    (DescendingBasis.totalEquiv _ _ _ (DirectSum.of _ r (Submodule.Quotient.mk x)))=_
  rw [DescendingBasis.totalEquiv_of_mk]
  have hx := DescendingBasis.equiv_component (K := F)
    (A := StrictQuotient d.beta d.phi) (I := StrictPowerIndex d.r)
    (B := StrictMultiplicityInitialQuotient d)
    (b := strictCoupledBasis d) (w := strictBasisMultiplicityWeight d)
    (c := strictMultiplicityInitialBasis d) r (x : StrictQuotient d.beta d.phi)
  exact hx

end PaperVerification.Fermion
