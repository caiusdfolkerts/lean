module

public import PaperVerification.ToricAffinePullbackSections
public import PaperVerification.ToricDominantFunctionField

@[expose] public section

/-! # Actual dominant rational pullback in commuting affine charts -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l]
    (f : Y ⟶ X) [IsDominant f] (φ : R ⟶ S)
    (hcomm : l ≫ f = Spec.map φ ≫ j)

include hcomm in
theorem dominantFunctionFieldMap_affineCoordinate (a : R) :
    dominantFunctionFieldMap f (affineOpenCoordinateMap R j a) =
      affineOpenCoordinateMap S l (φ a) := by
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  let V := l ''ᵁ (⊤ : (Spec S).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  letI : Nonempty V := openImmersion_image_nonempty l ⊤
  letI : Nonempty (f ⁻¹ᵁ U) := dominant_preimage_nonempty f U
  have hVU : V≤f ⁻¹ᵁ U := affineChartSquare_image_le R S j l f φ hcomm
  rw [← affineChartSection_germ R j a,dominantFunctionFieldMap_germ]
  calc
    Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U (affineChartSection R j a)) =
        Y.germToFunctionField V
          (f.appLE U V hVU (affineChartSection R j a)) := by
      change _=Y.germToFunctionField V
        (Y.presheaf.map (homOfLE hVU).op (f.app U (affineChartSection R j a)))
      exact (germToFunctionField_restrict Y (homOfLE hVU) _).symm
    _ = Y.germToFunctionField V (affineChartSection S l (φ a)) := by
      rw [affineChartSection_pullback R S j l f φ hcomm]
    _ = affineOpenCoordinateMap S l (φ a) := affineChartSection_germ S l _

end PaperVerification.ToricSchemes
