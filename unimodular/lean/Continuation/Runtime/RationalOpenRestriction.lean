module

public import Continuation.Runtime.IntrinsicReconstruction

/-!
# Local regularity under an open immersion

The actual isomorphism of stalks reflects membership in the local ring and
regularity of a rational inverse. These statements use the scheme's genuine
function field and its genuine generic-stalk map.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem regularAt_openImmersion_iff (j : Y ⟶ X) [IsOpenImmersion j]
    [IsDominant j] (y : Y) (r : X.functionField) :
    dominantFunctionFieldMap j r ∈ regularAtSubring Y y ↔
      r ∈ regularAtSubring X (j y) := by
  constructor
  · rintro ⟨s, hs⟩
    let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
    refine ⟨e.symm s, dominantFunctionFieldMap_injective j ?_⟩
    rw [dominantFunctionFieldMap_stalk]
    change algebraMap (Y.presheaf.stalk y) Y.functionField (e (e.symm s)) = _
    simpa only [RingEquiv.apply_symm_apply] using hs
  · exact dominantFunctionFieldMap_mem_regularAt j y r

theorem isRegularUnitAt_openImmersion_iff (j : Y ⟶ X)
    [IsOpenImmersion j] [IsDominant j] (y : Y) (r : X.functionField) :
    IsRegularUnitAt Y y (dominantFunctionFieldMap j r) ↔
      IsRegularUnitAt X (j y) r := by
  simp only [IsRegularUnitAt, ← map_inv₀,
    regularAt_openImmersion_iff j y]

end PaperVerification.ToricSchemes
