module
public import mixed_results.retraction_normalization

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.PrescribedRetractionProjection -/
section

/-! # Retractions with a prescribed augmentation

If a zero-target deformation retract induces an isomorphism under a given
augmentation, its projection can be replaced by that actual augmentation.
An explicit correction of the homotopy supplies the deformation identity.
No multiplicativity of the chosen splitting is required.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearDeformationRetract

variable {R M H N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  [AddCommGroup N] [Module R N]
  (C : LinearDeformationRetract (R := R) (M := M) (H := H))
  (hzero : C.targetD=0) (ε : M →ₗ[R] N) (e : H ≃ₗ[R] N)
  (hεd : ε.comp C.sourceD=0) (hεi : ε.comp C.inclusion=e.toLinearMap)

def prescribedInclusion : N →ₗ[R] M := C.inclusion.comp e.symm.toLinearMap

include hεi in
theorem augmentation_prescribedInclusion (x : N) :
    ε (prescribedInclusion C e x)=x := by
  have hh := LinearMap.congr_fun hεi (e.symm x)
  change ε (C.inclusion (e.symm x))=e (e.symm x) at hh
  exact hh.trans (e.apply_symm_apply x)

include hzero in
theorem prescribedInclusion_cycle (x : N) :
    C.sourceD (prescribedInclusion C e x)=0 := by
  change C.sourceD (C.inclusion (e.symm x))=0
  rw [C.inclusion_differential,hzero,LinearMap.zero_apply,map_zero]

def prescribedHomotopy : Module.End R M :=
  C.homotopy-(prescribedInclusion C e).comp (ε.comp C.homotopy)

include hzero hεd hεi in
theorem prescribed_deformation (x : M) :
    C.sourceD (prescribedHomotopy C ε e x) +
      prescribedHomotopy C ε e (C.sourceD x) = x-prescribedInclusion C e (ε x) := by
  have hh := LinearMap.congr_fun C.deformation x
  change C.sourceD (C.homotopy x)+C.homotopy (C.sourceD x)=
    x-C.inclusion (C.projection x) at hh
  have hε (y : M) : ε (C.sourceD y)=0 := by
    exact LinearMap.congr_fun hεd y
  have hε' : ε (C.homotopy (C.sourceD x))=ε x-e (C.projection x) := by
    have he := congrArg ε hh
    rw [map_add,map_sub,hε,zero_add] at he
    have hi := LinearMap.congr_fun hεi (C.projection x)
    change ε (C.inclusion (C.projection x))=e (C.projection x) at hi
    rwa [hi] at he
  have hei : prescribedInclusion C e (e (C.projection x))=C.inclusion (C.projection x) := by
    change C.inclusion (e.symm (e (C.projection x)))=_
    rw [e.symm_apply_apply]
  change C.sourceD (C.homotopy x-prescribedInclusion C e (ε (C.homotopy x)))+
    (C.homotopy (C.sourceD x)-prescribedInclusion C e (ε (C.homotopy (C.sourceD x))))=_
  rw [map_sub,prescribedInclusion_cycle C hzero e,sub_zero,hε',map_sub,hei]
  calc
    _ = (C.sourceD (C.homotopy x)+C.homotopy (C.sourceD x))-
        prescribedInclusion C e (ε x)+C.inclusion (C.projection x) := by abel
    _ = x-prescribedInclusion C e (ε x) := by rw [hh]; abel

/-- A deformation retract whose projection is exactly the supplied map. -/
def withProjection : LinearDeformationRetract (R := R) (M := M) (H := N) where
  sourceD := C.sourceD
  targetD := 0
  inclusion := prescribedInclusion C e
  projection := ε
  homotopy := prescribedHomotopy C ε e
  source_square := C.source_square
  target_square := by simp
  inclusion_chain := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.comp_apply,LinearMap.zero_apply,map_zero] using
      prescribedInclusion_cycle C hzero e x
  projection_chain := by simpa only [LinearMap.zero_comp] using hεd
  retract := by
    apply LinearMap.ext
    exact augmentation_prescribedInclusion C ε e hεi
  deformation := by
    apply LinearMap.ext
    exact prescribed_deformation C hzero ε e hεd hεi

/-- The same literal augmentation, with all strong side conditions. -/
def strongWithProjection : LinearContraction (R := R) (M := M) (H := N) :=
  (withProjection C hzero ε e hεd hεi).normalizeZeroTarget rfl

@[simp] theorem strongWithProjection_projection :
    (strongWithProjection C hzero ε e hεd hεi).projection=ε := rfl

end FourPapers.HomologicalPerturbation.LinearDeformationRetract

end
end
end


end
