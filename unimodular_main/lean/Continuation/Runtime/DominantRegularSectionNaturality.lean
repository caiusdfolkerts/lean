module

public import Continuation.Runtime.IntrinsicReconstruction

/-!
# Regular restrictions and dominant rational pullback

The generic value of the actual restriction `appLE` is the actual
generic-stalk pullback of the original section. This is the ordinary
restriction compatibility of generic germs, with the smaller nonempty
source open made explicit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace PaperVerification.ToricSchemes

theorem dominantFunctionFieldMap_appLE_value
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, U)) :
    X.germToFunctionField V (f.appLE U V h r) =
      dominantFunctionFieldMap f (Y.germToFunctionField U r) := by
  letI : Nonempty (f ⁻¹ᵁ U) := dominant_preimage_nonempty f U
  change X.germToFunctionField V
    (X.presheaf.map (homOfLE h).op (f.app U r)) = _
  rw [germToFunctionField_restrict]
  exact (dominantFunctionFieldMap_germ f U r).symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.dominantFunctionFieldMap_appLE_value
