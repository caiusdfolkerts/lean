module
public import shared_results.part025
public import graph_results.closed_graph_integral_model
public import shared_results.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphTransferredGrading -/
section

/-! # Specializing the graded free transfer to the integral graph family -/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial DirectSum
open HomologicalPerturbation PolynomialModuleResolution
open scoped TensorProduct

section IntegralGraph

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)

abbrev IntegralGraphResolutionIndex := ActualIdealHomologyBasisIndex
  (integralGraphParameterData hG s) (integralGraphParameterHomogeneous hG s)
  (integralGraphHomologyPiece_free hG s hs)

def integralGraphResolutionBasis : Module.Basis (IntegralGraphResolutionIndex hG s hs)
    (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) :=
  actualIdealFreeBasis (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)

def integralGraphResolutionDegree (a : IntegralGraphResolutionIndex hG s hs) : ℕ := a.2.1

theorem integralGraphResolutionBasis_projection (p : ℕ) :
    Grading.projection (integralGraphResolutionBasis hG s hs)
      (integralGraphResolutionDegree hG s hs) p =
    idealFreeHomologicalProjection (integralGraphParameterData hG s)
      (integralGraphParameterHomogeneous hG s) p :=
  actualIdealFreeBasis_projection (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) p

theorem integralGraphResolutionIndex_finite : Finite (IntegralGraphResolutionIndex hG s hs) := by
  letI : ∀ q p, Module.Free GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) :=
    integralGraphHomologyPiece_free hG s hs
  letI : ∀ q p, Module.Finite GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) q p) :=
    integralGraphHomologyPiece_finite hG s hs
  apply gradedFreeIndex_finite
    (fun q p => actualIdealOrdinaryHomology (integralGraphParameterData hG s)
      (integralGraphParameterHomogeneous hG s) q p)
    (Fintype.card (GraphIntegralVariables N) * s) (Fintype.card (GraphIntegralVariables N))
  · intro q p hq
    dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
    exact intervalGraph_parameter_power_homology_zero_of_degree_gt hG
      (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero s q p hq
  · intro q p hp
    dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
    exact intervalGraph_parameter_power_homology_zero_of_exterior_degree_gt hG
      (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero s q p hp

theorem integralGraphResolutionDegree_le (a : IntegralGraphResolutionIndex hG s hs) :
    integralGraphResolutionDegree hG s hs a ≤ Fintype.card (GraphIntegralVariables N) := by
  by_contra h
  letI : Module.Free GraphIntegralCoefficientRing
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) a.1 a.2.1) :=
    integralGraphHomologyPiece_free hG s hs a.1 a.2.1
  letI : Subsingleton
      (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) a.1 a.2.1) := by
    dsimp only [integralGraphParameterData, integralGraphParameterHomogeneous]
    exact intervalGraph_parameter_power_homology_zero_of_exterior_degree_gt hG
      (Polynomial.X : Polynomial ℤ) Polynomial.X_ne_zero s a.1 a.2.1 (Nat.lt_of_not_ge h)
  exact (Module.Free.chooseBasis GraphIntegralCoefficientRing
    (actualIdealOrdinaryHomology (integralGraphParameterData hG s)
      (integralGraphParameterHomogeneous hG s) a.1 a.2.1)).ne_zero a.2.2
      (Subsingleton.elim _ _)

/-- The actual integral polynomial differential lowers the basis degree. -/
theorem integralGraphTransferred_d_projection (p : ℕ) :
    (integralGraphTransferredModel hG s hs).targetD.comp
      (Grading.projection (integralGraphResolutionBasis hG s hs)
        (integralGraphResolutionDegree hG s hs) (p+1)) =
    (Grading.projection (integralGraphResolutionBasis hG s hs)
      (integralGraphResolutionDegree hG s hs) p).comp
        (integralGraphTransferredModel hG s hs).targetD := by
  let D : Module.End (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) :=
    (integralGraphTransferredModel hG s hs).targetD
  have hl := congrArg
    (fun f : Module.End (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) => D.comp f)
    (integralGraphResolutionBasis_projection hG s hs (p+1))
  have hr := congrArg
    (fun f : Module.End (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) => f.comp D)
    (integralGraphResolutionBasis_projection hG s hs p)
  have he := actualIdealFreeModel_d_projection (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs) p
  exact hl.trans (he.trans hr.symm)

theorem integralGraphTransferred_d_projection_zero :
    (integralGraphTransferredModel hG s hs).targetD.comp
      (Grading.projection (integralGraphResolutionBasis hG s hs)
        (integralGraphResolutionDegree hG s hs) 0) = 0 := by
  have hl := congrArg
    (fun f : Module.End (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) =>
      (integralGraphTransferredModel hG s hs).targetD.comp f)
    (integralGraphResolutionBasis_projection hG s hs 0)
  have he := actualIdealFreeModel_d_projection_zero (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)
  exact hl.trans he

theorem integralGraphAugmentation_projection_zero :
    (integralGraphAugmentation hG s hs).comp
      (Grading.projection (integralGraphResolutionBasis hG s hs)
        (integralGraphResolutionDegree hG s hs) 0) = integralGraphAugmentation hG s hs := by
  change (actualIdealFreeAugmentation (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)).comp
      (Grading.projection (actualIdealFreeBasis (integralGraphParameterData hG s)
        (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs))
        (fun a => a.2.1) 0) = _
  rw [actualIdealFreeBasis_projection]
  exact actualIdealFreeAugmentation_projection_zero (integralGraphParameterData hG s)
    (integralGraphParameterHomogeneous hG s) (integralGraphHomologyPiece_free hG s hs)

end IntegralGraph
end FourPapers.Sublattice

end
end
end


end
