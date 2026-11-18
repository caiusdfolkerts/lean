module

public import ToricPower.ReconstructionCompletionRawSquare
public import ToricPower.ReconstructionCompletionRawSectionTargetUnits

/-! # The original reconstruction square on arbitrary scalar sections

The two genuine target isomorphisms are compared before the cellular
objects are substituted. Their section coordinates are the same normalized
adjunct on the actual overlap.
-/

@[expose] public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "jσ" => fan.affineToricChartι σ
local notation "jτ" => fan.affineToricChartι τ
local notation "Uσ" => fan.affineToricChart σ
local notation "Uτ" => fan.affineToricChart τ
local notation "l" => fan.affineToricOverlapLeft σ τ
local notation "r" => fan.affineToricOverlapRight σ τ
local notation "m" => r ≫ jτ
local notation "W" => fan.affineToricOverlap σ τ
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))
local notation "Z" => Spec (CommRingCat.of (DiagonalChartRing ℂ (fanArrangementMatrix fan basis rays)
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)))
local notation "δ" => toricDiagonal fan
local notation "p" => toricDiagonalFirst fan
local notation "q" => toricDiagonalSecond fan
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "E" => (Scheme.Modules.pushforward jτ).obj (𝟙_ (Uτ).Modules)
local notation "Γσ" => FiniteCover.schemeBaseSections ℂ Uσ ⊤
local notation "Γτ" => FiniteCover.schemeBaseSections ℂ Uτ ⊤
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ Z ⊤

local instance reconstructionPointwiseOverlapLeft : IsOpenImmersion l :=
  fan.isOpenImmersion_affineToricOverlapLeft σ τ
local instance reconstructionPointwiseOverlapRight : IsOpenImmersion r :=
  fan.isOpenImmersion_affineToricOverlapRight σ τ
local instance reconstructionPointwiseChartAffine : IsAffineHom jτ :=
  toricChartInclusion_isAffineHom fan τ

/-- Actual evaluation and the actual diagonal quotient agree on arbitrary
sections whenever their original exterior and coefficient coordinates agree. -/
theorem reconstructionRawPointwise_square
    (L M : (X).Modules) (x : 𝟙_ (X).Modules ⟶ M ⊗ E)
    (β : L ⊗ M ⟶ J) (γ : schemeExteriorSheaf p q L M ⟶ H)
    (top : (Scheme.Modules.pullback δ).map γ =
      schemeExternalSectionRetractionMap δ p q
        (pullback.diagonal_fst fan.algebraicRealizationStructureMap)
        (pullback.diagonal_snd fan.algebraicRealizationStructureMap) L M ≫ β)
    (s₀ : (Γσ).obj ((Scheme.Modules.pullback jσ).obj L))
    (t₀ : (Γτ).obj ((Scheme.Modules.pullback jτ).obj M))
    (z₀ : (ΓP).obj ((Scheme.Modules.pullback chart).obj (schemeExteriorSheaf p q L M)))
    (coefficient : (moduleUnitActualSectionsLinearEquiv ℂ Uτ
        ((Scheme.Modules.pullback jτ).obj M)).symm t₀ =
      (Scheme.Modules.pullbackObjUnitIso jτ).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction jτ).homEquiv _ _).symm
          (x ≫ BondalThomsen.schemeProjectionFormulaMap jτ M))
    (exterior : (moduleUnitActualSectionsLinearEquiv ℂ Z
        ((Scheme.Modules.pullback chart).obj (schemeExteriorSheaf p q L M))).symm z₀ =
      reconstructionRawExteriorUnit fan basis rays σ τ L M
        ((moduleUnitActualSectionsLinearEquiv ℂ Uσ
          ((Scheme.Modules.pullback jσ).obj L)).symm s₀)
        ((moduleUnitActualSectionsLinearEquiv ℂ Uτ
          ((Scheme.Modules.pullback jτ).obj M)).symm t₀)) :
    (reconstructionRawEvaluationTargetIso fan nonempty regular basis rays σ τ).hom
        ((Γσ).map ((Scheme.Modules.pullback jσ).map
          ((ρ_ L).inv ≫ L ◁ x ≫ (α_ L M E).inv ≫ β ▷ E)) s₀) =
      (reconstructionRawDiagonalTargetIso fan nonempty regular basis rays σ τ).hom
        ((ΓP).map ((Scheme.Modules.pullback chart).map γ) z₀) := by
  apply (moduleUnitActualSectionsLinearEquiv ℂ W ((J).restrict m)).symm.injective
  change (moduleUnitActualSectionsLinearEquiv ℂ W ((J).restrict m)).symm
      ((((Γσ).mapIso
        (reconstructionRawEvaluationTargetSheafIso fan nonempty regular basis rays σ τ) ≪≫
        (pushforwardBaseSectionsLinearEquiv ℂ l ((J).restrict m) ⊤).toModuleIso).hom)
        ((Γσ).map ((Scheme.Modules.pullback jσ).map
          ((ρ_ L).inv ≫ L ◁ x ≫ (α_ L M E).inv ≫ β ▷ E)) s₀)) =
    (moduleUnitActualSectionsLinearEquiv ℂ W ((J).restrict m)).symm
      ((((ΓP).mapIso
        (reconstructionRawDiagonalTargetSheafIso fan nonempty regular basis rays σ τ) ≪≫
        (pushforwardBaseSectionsLinearEquiv ℂ g ((J).restrict m) ⊤).toModuleIso).hom)
        ((ΓP).map ((Scheme.Modules.pullback chart).map γ) z₀))
  erw [reconstruction_mappedPushforwardSections_target_unit ℂ l,
    reconstruction_mappedPushforwardSections_target_unit ℂ g, exterior]
  erw [reconstructionRawEvaluation_target_unit,
    reconstructionRawDiagonal_target_unit fan nonempty regular basis rays σ τ _ _ _ _ _ _ top]
  rw [coefficient]

end ToricPower

end
