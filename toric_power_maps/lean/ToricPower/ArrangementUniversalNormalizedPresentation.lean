module

public import ToricPower.ArrangementUniversalNormalizedHom
public import ToricPower.MorseCategoryPresentations

/-! # The original normalized comparison in the affine assembly presentation

Only equal inherited preadditive structures are transported. The full
natural isomorphism, including every deck and coefficient map, is retained.
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

def universalNormalizedHomDiagram_standardIso :
    Cellular.homDiagram ℂ (universalCartierQuasicoherentSources fan nonempty regular basis rays) ≅
      Cellular.homDiagram ℂ (normalizedCartierQuasicoherentSources fan nonempty regular basis rays) ⋙
        (Functor.whiskeringLeft (UniversalIncidenceObject (fanArrangementMatrix fan basis rays))
          (IncidenceObject (fanArrangementMatrix fan basis rays)) (ModuleCat ℂ)).obj
          (universalCoverProjection (fanArrangementMatrix fan basis rays)) := by
  simpa only [morseQuasicoherentPreadditivePresentation] using
    (universalNormalizedHomDiagramIso fan nonempty regular basis rays)

end ToricPower
end
