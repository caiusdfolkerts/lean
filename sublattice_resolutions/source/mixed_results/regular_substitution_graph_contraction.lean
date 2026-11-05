module
public import mixed_results.part001
public import mixed_results.prescribed_retraction_projection
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionGraphContraction -/
section

/-! # A split graph Koszul complex for regular-sequence substitution

The displayed complex has differential `t_v-f_v`. Its projection is
literal substitution followed by exterior augmentation. The contraction
is linear over the source polynomial ring and therefore survives tensoring
with any source algebra, without a flatness hypothesis on that algebra.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg MvPolynomial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → (MvPolynomial Y K)) (w : V → ℕ) (hhom : ∀ v, (f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v, 0 < w v)
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)] [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
  (hvars : ∀ v, algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v)

abbrev graphTransferred : LinearDeformationRetract
    («R» := S) (M := PolynomialModuleResolution.Bar («R» := K) (V := V) R)
    (H := S ⊗[K] Homology f w hhom) :=
  WeightedPolynomialPerturbation.transferred R (contraction f w hhom)
    (contraction_substitution_d f w hhom hvars) (MvPolynomial.basisMonomials Y K)
    Finsupp.degree w hw (contraction_h_nonincreasing f w hhom)

include hreg in
theorem graphTransferred_target_zero : (graphTransferred f w hhom hw hvars).targetD=0 :=
  WeightedPolynomialPerturbation.transferred_targetD_zero R (contraction f w hhom)
    (contraction_substitution_d f w hhom hvars) (MvPolynomial.basisMonomials Y K)
    Finsupp.degree w hw (contraction_h_nonincreasing f w hhom)
    (WeightedPolynomialPerturbation.externalDifferential_inclusion_zero R
      (contraction f w hhom) (MvPolynomial.basisMonomials Y K)
      (contraction_inclusion_mem_zero f w hhom hreg))

theorem graphTransferred_source : (graphTransferred f w hhom hw hvars).sourceD=
    PolynomialModuleResolution.differential («R» := K) (V := V) R :=
  WeightedPolynomialPerturbation.transferred_sourceD R (contraction f w hhom)
    (contraction_substitution_d f w hhom hvars) (MvPolynomial.basisMonomials Y K)
    Finsupp.degree w hw (contraction_h_nonincreasing f w hhom)

/-- A genuine source-polynomial-linear strong contraction onto `R`. -/
def graphContraction : LinearContraction
    («R» := S) (M := PolynomialModuleResolution.Bar («R» := K) (V := V) R) (H := R) :=
  (graphTransferred f w hhom hw hvars).strongWithProjection
    (graphTransferred_target_zero f w hhom hreg hw hvars)
    (PolynomialModuleResolution.augmentation («R» := K) (V := V) R)
    (freeModuleEquiv f w hhom hreg hw hvars)
    (by rw [graphTransferred_source]; exact PolynomialModuleResolution.augmentation_boundary R)
    (by rfl)

@[simp] theorem graphContraction_d : (graphContraction f w hhom hreg hw hvars).d=
    PolynomialModuleResolution.differential («R» := K) (V := V) R :=
  graphTransferred_source f w hhom hw hvars

@[simp] theorem graphContraction_projection :
    (graphContraction f w hhom hreg hw hvars).projection=
      PolynomialModuleResolution.augmentation («R» := K) (V := V) R := rfl

theorem graphContraction_projection_tmul (s : S) (r : R) (F : Finset V) :
    (graphContraction f w hhom hreg hw hvars).projection (s ⊗ₜ[K] (r ⊗ₜ[K] Simplicial.basis F))=
      if F=∅ then MvPolynomial.aeval f s * r else 0 := by
  rw [graphContraction_projection,PolynomialModuleResolution.augmentation_tmul_basis]
  rw [Algebra.smul_def]
  simp only [algebraMap_eq_aeval f hvars, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

variable (A : Type u) [CommRing A] [Algebra (MvPolynomial V K) A]

/-- The graph Koszul exactness after an arbitrary source-algebra change.
The coefficient target is the literal tensor product `A ⊗[S] R`. -/
def graphBaseChangeContraction : LinearContraction
    («R» := A) (M := A ⊗[S] PolynomialModuleResolution.Bar («R» := K) (V := V) R)
    (H := A ⊗[S] R) := (graphContraction f w hhom hreg hw hvars).baseChange A

@[simp] theorem graphBaseChangeContraction_projection :
    (graphBaseChangeContraction f w hhom hreg hw hvars A).projection=
      (PolynomialModuleResolution.augmentation («R» := K) (V := V) R).baseChange A := rfl

end FourPapers.PolynomialRegularSubstitution

end
end
end

end
