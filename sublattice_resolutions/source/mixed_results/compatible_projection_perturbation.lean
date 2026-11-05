module
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.CompatibleProjectionPerturbation -/
section

/-! # Perturbations compatible with an existing algebra projection

When the original projection already intertwines the added differential,
the perturbation formula leaves that projection unchanged and transfers
exactly the displayed target differential. Together with a literal DGA
projection this gives multiplicative, rather than numerical, comparison.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearContraction
variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))
  (δ : Module.End R M) (Δ : Module.End R H) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M)=1+δ*C.h)
  (hp : C.projection.comp δ=Δ.comp C.projection)

include hu hp in
theorem projection_unit : C.projection.comp (u : Module.End R M)=C.projection := by
  apply LinearMap.ext
  intro x
  rw [hu]
  change C.projection (x+δ (C.h x))=C.projection x
  rw [map_add]
  have hh := LinearMap.congr_fun hp (C.h x)
  change C.projection (δ (C.h x))=Δ (C.projection (C.h x)) at hh
  rw [hh,C.projection_homotopy_apply,map_zero,add_zero]

include hu hp in
theorem projection_unit_inv :
    C.projection.comp ((u⁻¹ : (Module.End R M)ˣ) : Module.End R M)=C.projection := by
  calc
    _ = (C.projection.comp (u : Module.End R M)).comp
        ((u⁻¹ : (Module.End R M)ˣ) : Module.End R M) := by
      rw [projection_unit C δ Δ u hu hp]
    _ = C.projection := by
      rw [LinearMap.comp_assoc]
      have he : (u : Module.End R M).comp
          ((u⁻¹ : (Module.End R M)ˣ) : Module.End R M)=LinearMap.id :=
        Units.mul_inv u
      rw [he,LinearMap.comp_id]

include hu hp in
theorem projection_correction_apply (x : M) :
    C.projection (correction u δ x)=Δ (C.projection x) := by
  have hi := LinearMap.congr_fun (projection_unit_inv C δ Δ u hu hp) (δ x)
  have hh := LinearMap.congr_fun hp x
  change C.projection (((u⁻¹ : (Module.End R M)ˣ) : Module.End R M) (δ x))=
    C.projection (δ x) at hi
  change C.projection (δ x)=Δ (C.projection x) at hh
  exact hi.trans hh

include hu hp in
theorem transferredProjection_eq : C.transferredProjection δ u=C.projection := by
  apply LinearMap.ext
  intro x
  change C.projection (x-correction u δ (C.h x))=C.projection x
  rw [map_sub,projection_correction_apply C δ Δ u hu hp,
    C.projection_homotopy_apply,map_zero,sub_zero]

include hu hp in
theorem transferredDifferential_eq : C.transferredDifferential δ u=Δ := by
  apply LinearMap.ext
  intro x
  change C.projection (correction u δ (C.inclusion x))=Δ x
  rw [projection_correction_apply C δ Δ u hu hp,C.projection_inclusion_apply]

end FourPapers.HomologicalPerturbation.LinearContraction

end
end
end


end
