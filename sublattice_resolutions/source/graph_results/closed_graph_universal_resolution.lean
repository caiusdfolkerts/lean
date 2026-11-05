module
public import graph_results.closed_graph_transferred_grading
public import graph_results.closed_graph_ideal_base_change
public import graph_results.projected_resolution_base_change

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphUniversalResolution -/
section

/-!
# The integral chain resolution and arbitrary specialization

The resolved module is the literal power of the parameter ideal
`(x_i y_j - z^(j-i) x_j y_i)` over `ℤ[z]`. The chain terms are the actual
homological-degree pieces of the finite free transferred module, and the
augmentation is the actual polynomial-module action. A coefficient-linear
augmented contraction establishes exactness after arbitrary base change.

The internal grading and specialized matrix statements are supplied separately;
the construction here does not redefine a resolution to mean only a total
square-zero operator.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CategoryTheory HomologicalComplex
open scoped TensorProduct
attribute [local instance] integralGraphFreeModel_scalarTower integralGraphModule_scalarTower
attribute [local instance 2000] LinearMap.IsScalarTower.compatibleSMul

section ProjectedEntries
universe u
variable {R₀ S₀ F₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
  [AddCommGroup F₀] [Module S₀ F₀] [Module R₀ F₀] [IsScalarTower R₀ S₀ F₀]
  [AddCommGroup M₀] [Module S₀ M₀] [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀]
  {I₀ : Type*} (b : Module.Basis I₀ S₀ F₀) (degree : I₀ → ℕ)
  (D : Module.End S₀ F₀)
  (C₀ : HomologicalPerturbation.LinearDeformationRetract (R := R₀) (M := F₀) (H := M₀))
  (hD : C₀.sourceD = D.restrictScalars R₀)
  (hlower : ∀ p, D.comp (Grading.projection b degree (p+1)) =
    (Grading.projection b degree p).comp D)

private theorem projectedDifferential_entry (p : ℕ)
    (i : {i : I₀ // degree i = p+1}) (j : {j : I₀ // degree j = p}) :
    (ProjectedFreeResolution.pieceBasis b degree p).repr
      ((ProjectedFreeResolution.data b degree D C₀ hD hlower).differential p
        (ProjectedFreeResolution.pieceBasis b degree (p+1) i)) j =
      b.repr (D (b i.val)) j.val := by
  have hr := ProjectedFreeResolution.pieceBasis_repr (S := S₀) (F := F₀)
    b degree p ((ProjectedFreeResolution.data b degree D C₀ hD hlower).differential p
      (ProjectedFreeResolution.pieceBasis b degree (p+1) i)) j
  have hv : ((ProjectedFreeResolution.data b degree D C₀ hD hlower).differential p
      (ProjectedFreeResolution.pieceBasis b degree (p+1) i)).val = D (b i.val) := by
    change D (ProjectedFreeResolution.pieceBasis b degree (p+1) i).val = _
    rw [ProjectedFreeResolution.pieceBasis_val]
  exact hr.trans (congrArg (fun x : F₀ => b.repr x j.val) hv)

def projectedAugmentedContraction (ε : F₀ →ₗ[S₀] M₀)
    (hε : C₀.projection = ε.restrictScalars R₀) (ht : C₀.targetD = 0)
    (hzero : D.comp (Grading.projection b degree 0) = 0)
    (hεzero : ε.comp (Grading.projection b degree 0) = ε) :=
  ProjectedFreeResolution.augmentedContraction (R := R₀) (S := S₀) (F := F₀) (M := M₀)
    (I := I₀) b degree D ε C₀ hD hε ht hlower hzero hεzero

end ProjectedEntries

variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
  (s : ℕ) (hs : 0 < s)

abbrev IntegralGraphResolutionTerm (p : ℕ) :=
  ProjectedFreeResolution.piece (S := GraphIntegralPolynomialRing N)
    (F := IntegralGraphFreeModel hG s) (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs) p

def integralGraphResolutionData :
    SubmoduleComplexData (GraphIntegralPolynomialRing N) (IntegralGraphFreeModel hG s) :=
  ProjectedFreeResolution.data (R := GraphIntegralCoefficientRing)
    (S := GraphIntegralPolynomialRing N) (F := IntegralGraphFreeModel hG s)
    (M := IntegralGraphModule hG s) (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs)
    (integralGraphTransferredModel hG s hs).targetD
    (integralGraphSplitAugmentation hG s hs)
    (integralGraphSplitAugmentation_sourceD hG s hs)
    (integralGraphTransferred_d_projection hG s hs)

def integralGraphResolutionDifferential (p : ℕ) :
    IntegralGraphResolutionTerm hG s hs (p+1) →ₗ[GraphIntegralPolynomialRing N]
      IntegralGraphResolutionTerm hG s hs p :=
  (integralGraphResolutionData hG s hs).differential p

def integralGraphResolutionAugmentation :=
  ProjectedFreeResolution.augmentationZero (S := GraphIntegralPolynomialRing N)
    (F := IntegralGraphFreeModel hG s) (M := IntegralGraphModule hG s)
    (I := IntegralGraphResolutionIndex hG s hs)
    (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs) (integralGraphAugmentation hG s hs)

/-- A genuine Mathlib projective resolution of the displayed ideal power. -/
def integralGraphProjectiveResolution :
    ProjectiveResolution (ModuleCat.of (GraphIntegralPolynomialRing N) (IntegralGraphModule hG s)) :=
  ProjectedFreeResolution.resolution (R := GraphIntegralCoefficientRing)
    (S := GraphIntegralPolynomialRing N) (F := IntegralGraphFreeModel hG s)
    (M := IntegralGraphModule hG s) (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs)
    (integralGraphTransferredModel hG s hs).targetD (integralGraphAugmentation hG s hs)
    (integralGraphSplitAugmentation hG s hs)
    (integralGraphSplitAugmentation_sourceD hG s hs)
    (integralGraphSplitAugmentation_projection hG s hs)
    (integralGraphSplitAugmentation_targetD hG s hs)
    (integralGraphTransferred_d_projection hG s hs)
    (integralGraphTransferred_d_projection_zero hG s hs)
    (integralGraphAugmentation_projection_zero hG s hs)

abbrev IntegralGraphDegreeIndex (p : ℕ) :=
  {a : IntegralGraphResolutionIndex hG s hs | integralGraphResolutionDegree hG s hs a = p}

def integralGraphResolutionTermBasis (p : ℕ) :=
  ProjectedFreeResolution.pieceBasis (S := GraphIntegralPolynomialRing N)
    (F := IntegralGraphFreeModel hG s) (I := IntegralGraphResolutionIndex hG s hs)
    (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs) p

theorem integralGraphResolutionTerm_free (p : ℕ) :
    Module.Free (GraphIntegralPolynomialRing N) (IntegralGraphResolutionTerm hG s hs p) :=
  Module.Free.of_basis (integralGraphResolutionTermBasis hG s hs p)

theorem integralGraphResolutionTerm_finite (p : ℕ) :
    Module.Finite (GraphIntegralPolynomialRing N) (IntegralGraphResolutionTerm hG s hs p) := by
  letI := integralGraphResolutionIndex_finite hG s hs
  exact Module.Finite.of_basis (integralGraphResolutionTermBasis hG s hs p)

theorem integralGraphResolutionTerm_zero_above (p : ℕ)
    (hp : Fintype.card (GraphIntegralVariables N) < p) :
    Subsingleton (IntegralGraphResolutionTerm hG s hs p) := by
  have hz := ProjectedFreeResolution.piece_zero_above (S := GraphIntegralPolynomialRing N)
    (F := IntegralGraphFreeModel hG s) (I := IntegralGraphResolutionIndex hG s hs)
    (integralGraphResolutionBasis hG s hs)
    (integralGraphResolutionDegree hG s hs) (Fintype.card (GraphIntegralVariables N))
    (integralGraphResolutionDegree_le hG s hs) p hp
  exact hz

/-- These are the coefficients of the actual degreewise differential in
the displayed restricted bases, not coefficients of an unrelated model. -/
theorem integralGraphResolution_matrix_entry (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p) :
    (integralGraphResolutionTermBasis hG s hs p).repr
      (integralGraphResolutionDifferential hG s hs p
        (integralGraphResolutionTermBasis hG s hs (p+1) i)) j =
    (integralGraphResolutionBasis hG s hs).repr
      ((integralGraphTransferredModel hG s hs).targetD
        (integralGraphResolutionBasis hG s hs i.val)) j.val := by
  have he := projectedDifferential_entry (R₀ := GraphIntegralCoefficientRing)
    (S₀ := GraphIntegralPolynomialRing N) (F₀ := IntegralGraphFreeModel hG s)
    (M₀ := IntegralGraphModule hG s) (I₀ := IntegralGraphResolutionIndex hG s hs)
    (integralGraphResolutionBasis hG s hs) (integralGraphResolutionDegree hG s hs)
    (integralGraphTransferredModel hG s hs).targetD (integralGraphSplitAugmentation hG s hs)
    (integralGraphSplitAugmentation_sourceD hG s hs)
    (integralGraphTransferred_d_projection hG s hs) p i j
  exact he

theorem integralGraphResolution_entries_in_variableIdeal (p : ℕ)
    (i : IntegralGraphDegreeIndex hG s hs (p+1))
    (j : IntegralGraphDegreeIndex hG s hs p) :
    (integralGraphResolutionTermBasis hG s hs p).repr
      (integralGraphResolutionDifferential hG s hs p
        (integralGraphResolutionTermBasis hG s hs (p+1) i)) j ∈
      MvPolynomial.idealOfVars (GraphIntegralVariables N) GraphIntegralCoefficientRing := by
  rw [integralGraphResolution_matrix_entry]
  exact integralGraphModel_entries_in_variableIdeal hG s hs
    (integralGraphResolutionBasis hG s hs) i.val j.val

attribute [local irreducible] integralGraphResolutionBasis integralGraphResolutionDegree
  integralGraphTransferredModel

/-- Exactness is witnessed by actual degreewise coefficient-linear maps. -/
def integralGraphAugmentedContraction :=
  projectedAugmentedContraction (R₀ := GraphIntegralCoefficientRing)
    (S₀ := GraphIntegralPolynomialRing N) (F₀ := IntegralGraphFreeModel hG s)
    (M₀ := IntegralGraphModule hG s) (I₀ := IntegralGraphResolutionIndex hG s hs)
    (b := integralGraphResolutionBasis hG s hs)
    (degree := integralGraphResolutionDegree hG s hs)
    (D := (integralGraphTransferredModel hG s hs).targetD)
    (C₀ := integralGraphSplitAugmentation hG s hs)
    (hD := integralGraphSplitAugmentation_sourceD hG s hs)
    (hlower := by
      intro p
      exact integralGraphTransferred_d_projection hG s hs p)
    (ε := integralGraphAugmentation hG s hs)
    (hε := integralGraphSplitAugmentation_projection hG s hs)
    (ht := integralGraphSplitAugmentation_targetD hG s hs)
    (hzero := by
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (integralGraphTransferred_d_projection_zero hG s hs) x)
    (hεzero := by
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (integralGraphAugmentation_projection_zero hG s hs) x)

theorem integralGraphResolution_exact_at_augmentation :
    Function.Exact (integralGraphResolutionDifferential hG s hs 0)
      (integralGraphResolutionAugmentation hG s hs) :=
  (integralGraphAugmentedContraction hG s hs).exact_augmentation

theorem integralGraphResolution_exact_positive (p : ℕ) :
    Function.Exact (integralGraphResolutionDifferential hG s hs (p+1))
      (integralGraphResolutionDifferential hG s hs p) :=
  (integralGraphAugmentedContraction hG s hs).exact_positive p

variable (A : Type*) [CommRing A] [Algebra GraphIntegralCoefficientRing A]

abbrev IntegralGraphSpecializedResolutionTerm (p : ℕ) :=
  A ⊗[GraphIntegralCoefficientRing] IntegralGraphResolutionTerm hG s hs p

def integralGraphSpecializedResolutionDifferential (p : ℕ) :
    IntegralGraphSpecializedResolutionTerm hG s hs A (p+1) →ₗ[A]
      IntegralGraphSpecializedResolutionTerm hG s hs A p :=
  ((integralGraphResolutionDifferential hG s hs p).restrictScalars
    GraphIntegralCoefficientRing).baseChange A

/-- The augmentation after specialization has the explicitly defined
specialized ideal power as its codomain. -/
def integralGraphSpecializedResolutionAugmentation :
    IntegralGraphSpecializedResolutionTerm hG s hs A 0 →ₗ[A]
      IntegralGraphSpecializedModule (G := G) s A :=
  (integralGraphIdealBaseChangeEquiv hG s A).toLinearMap.comp
    (((integralGraphResolutionAugmentation hG s hs).restrictScalars
      GraphIntegralCoefficientRing).baseChange A)

theorem integralGraphSpecializedResolution_exact_at_augmentation :
    Function.Exact (integralGraphSpecializedResolutionDifferential hG s hs A 0)
      (integralGraphSpecializedResolutionAugmentation hG s hs A) := by
  have he := ((integralGraphAugmentedContraction hG s hs).baseChange A).exact_augmentation
  exact Function.Exact.comp_injective (g' := integralGraphIdealBaseChangeEquiv hG s A)
    he (integralGraphIdealBaseChangeEquiv hG s A).injective
    (integralGraphIdealBaseChangeEquiv hG s A).map_zero

theorem integralGraphSpecializedResolution_exact_positive (p : ℕ) :
    Function.Exact (integralGraphSpecializedResolutionDifferential hG s hs A (p+1))
      (integralGraphSpecializedResolutionDifferential hG s hs A p) :=
  ((integralGraphAugmentedContraction hG s hs).baseChange A).exact_positive p

theorem integralGraphSpecializedResolution_augmentation_surjective :
    Function.Surjective (integralGraphSpecializedResolutionAugmentation hG s hs A) :=
  (integralGraphIdealBaseChangeEquiv hG s A).surjective.comp
    (((integralGraphAugmentedContraction hG s hs).baseChange A).augmentation_surjective)

/-- This holds for all coefficient algebras, including the evaluations
z=0 and z=1 over every field; no flatness or characteristic hypothesis is used. -/
theorem integralGraphResolution_arbitrary_specialization :
    Function.Surjective (integralGraphSpecializedResolutionAugmentation hG s hs A) ∧
    Function.Exact (integralGraphSpecializedResolutionDifferential hG s hs A 0)
      (integralGraphSpecializedResolutionAugmentation hG s hs A) ∧
    ∀ p, Function.Exact (integralGraphSpecializedResolutionDifferential hG s hs A (p+1))
      (integralGraphSpecializedResolutionDifferential hG s hs A p) :=
  ⟨integralGraphSpecializedResolution_augmentation_surjective hG s hs A,
    integralGraphSpecializedResolution_exact_at_augmentation hG s hs A,
    integralGraphSpecializedResolution_exact_positive hG s hs A⟩

end FourPapers.Sublattice

end
end
end


end
