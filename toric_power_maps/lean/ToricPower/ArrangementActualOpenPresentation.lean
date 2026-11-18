module

public import ToricPower.ArrangementActualOpenStandardMorse
public import ToricPower.ArrangementMorseStandardComplexAssembly
public import ToricPower.MorseCategoryPresentations
public import ToricPower.ComplexHomDiagramPresentation

/-! # Explicit inherited structures at the actual open-coefficient boundary

The intrinsic Hom functor and its actual open-image comparison were
constructed with the inherited preadditive structures. These equalities
transport their complete proofs to the abelian-category presentation used
by the affine coresolution, before the latter theorem is specialized.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "H" => Cellular.homDiagram ℂ
  (universalCartierQuasicoherentSources fan nonempty regular basis rays)

theorem universalCartierHomDiagram_standard_additive : (H).Additive := by
  simpa only [morseDiagramPreadditivePresentation] using
    (Cellular.homDiagram_additive ℂ
      (universalCartierQuasicoherentSources fan nonempty regular basis rays))

local instance actualOpenPresentationAffine (cone : fan.cones) :
    IsAffineHom (toricDerivedChartOpen fan cone).ι :=
  toricDerivedChartOpen_isAffineHom fan cone

def universalChartOpenCoefficientDiagram_standardIso (cone : fan.cones) :
    universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone ≅
      quasicoherentAffinePushforward (toricDerivedChartOpen fan cone).ι ⋙ H := by
  simpa only [morseQuasicoherentPreadditivePresentation] using
    (universalChartOpenCoefficientDiagramIso fan nonempty regular basis rays cone)

/-- Additivity in the concrete complex-scalar presentation is sealed
before substituting coefficients into the intrinsic Hom functor. -/
theorem universalComplexCartierHomDiagram_additive :
    (Cellular.complexHomDiagram
      (universalCartierQuasicoherentSources fan nonempty regular basis rays)).Additive := by
  simpa only [morseDiagramPreadditivePresentation] using
    (Cellular.complexHomDiagram_additive
      (universalCartierQuasicoherentSources fan nonempty regular basis rays))

/-- The same original open coefficient comparison, composed with the
proved whole-functor scalar presentation isomorphism. -/
def universalChartOpenCoefficientDiagram_complexIso (cone : fan.cones) :
    universalChartOpenCoefficientDiagram fan nonempty regular basis rays cone ≅
      quasicoherentAffinePushforward (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.complexHomDiagram
          (universalCartierQuasicoherentSources fan nonempty regular basis rays) :=
  universalChartOpenCoefficientDiagram_standardIso fan nonempty regular basis rays cone ≪≫
    Functor.isoWhiskerLeft
      (quasicoherentAffinePushforward (toricDerivedChartOpen fan cone).ι)
      (Cellular.complexHomDiagramIso
        (universalCartierQuasicoherentSources fan nonempty regular basis rays)).symm

end ToricPower
end
