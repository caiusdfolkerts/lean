module
public import shared_results.part025
public import shared_results.part011
public import shared_results.part003

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealProjectiveDimension -/
section

/-! # Projective dimension from the actual ordinary Tor support

The bound is proved by constructing the graded free resolution obtained from
the polynomial diagonal complex. Its basis in degree p is a basis of the
actual degree-p Koszul homology, so vanishing Tor removes the corresponding
free terms. No projective-dimension characterisation is assumed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section
namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical CommAlg MvPolynomial CategoryTheory
open HomologicalPerturbation PolynomialModuleResolution
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
open scoped TensorProduct
universe u
variable {k V : Type u} [Field k] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))

private theorem fieldIdealHomologyFree (q p : ℕ) : Module.Free k (actualIdealOrdinaryHomology P hJ q p) :=
  inferInstance

private abbrev fieldIdealSplitAugmentation :=
  PolynomialPerturbation.splitAugmentation P.ideal
    (actualIdealTensorContraction P hJ (fieldIdealHomologyFree P hJ))
    (actualIdealTensorContraction_d P hJ (fieldIdealHomologyFree P hJ))
    (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
    (actualIdealCoefficientDegree P)
    (actualIdealTensorContraction_h_nonincreasing_polynomial P hJ (fieldIdealHomologyFree P hJ))

/-- Vanishing of all ordinary Tor entries above N bounds the genuine
Mathlib projective dimension of the literal homogeneous ideal. -/
theorem ideal_projectiveDimension_le_of_betti_vanishing (N : ℕ)
    (hvan : ∀ p, N < p → ∀ q, ordinaryIdealBettiNumber P hJ p q = 0) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) P.ideal) ≤ (N : WithBot ℕ∞) := by
  let hf := fieldIdealHomologyFree P hJ
  let b := actualIdealFreeBasis P hJ hf
  let degree := fun a : ActualIdealHomologyBasisIndex P hJ hf => a.2.1
  let D := (actualIdealFreeModel P hJ hf).targetD
  let ε := actualIdealFreeAugmentation P hJ hf
  let C := fieldIdealSplitAugmentation P hJ
  have hD : C.sourceD = D.restrictScalars k := rfl
  have hε : C.projection = ε.restrictScalars k :=
    PolynomialPerturbation.splitAugmentation_projection P.ideal
      (actualIdealTensorContraction P hJ hf) (actualIdealTensorContraction_d P hJ hf)
      (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading)
      (actualIdealCoefficientDegree P) (actualIdealTensorContraction_h_nonincreasing_polynomial P hJ hf)
  have ht : C.targetD = 0 := rfl
  have hp (p : ℕ) : ProjectedFreeResolution.projection b degree p =
      idealFreeHomologicalProjection P hJ p :=
    actualIdealFreeBasis_projection P hJ hf p
  have hlower (p : ℕ) : D.comp (ProjectedFreeResolution.projection b degree (p+1)) =
      (ProjectedFreeResolution.projection b degree p).comp D := by
    exact (congrArg D.comp (hp (p+1))).trans
      ((actualIdealFreeModel_d_projection P hJ hf p).trans
        (congrArg (fun f => f.comp D) (hp p).symm))
  have hzero : D.comp (ProjectedFreeResolution.projection b degree 0) = 0 := by
    exact (congrArg D.comp (hp 0)).trans (actualIdealFreeModel_d_projection_zero P hJ hf)
  have hεzero : ε.comp (ProjectedFreeResolution.projection b degree 0) = ε := by
    exact (congrArg ε.comp (hp 0)).trans (actualIdealFreeAugmentation_projection_zero P hJ hf)
  apply ProjectedFreeResolution.projectiveDimension_le b degree D ε C hD hε ht
    hlower hzero hεzero N
  intro a
  by_contra ha
  have hh := hvan a.2.1 (lt_of_not_ge ha) a.1
  rw [ordinaryIdealBettiNumber_eq_finrank] at hh
  letI := actualIdealOrdinaryPiece_finite P a.1 a.2.1
  letI : Module.Finite k (actualIdealOrdinaryHomology P hJ a.1 a.2.1) := by
    unfold actualIdealOrdinaryHomology FilteredHomology.Homology
    infer_instance
  letI : Subsingleton (actualIdealOrdinaryHomology P hJ a.1 a.2.1) :=
    Module.finrank_zero_iff.mp hh
  exact (Module.Free.chooseBasis k (actualIdealOrdinaryHomology P hJ a.1 a.2.1)).ne_zero
    a.2.2 (Subsingleton.elim _ _)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.ideal_projectiveDimension_le_of_betti_vanishing

end
end
end


end
