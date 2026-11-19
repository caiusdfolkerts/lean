module

public import ToricPower.ReconstructionCompletionRawSections
public import ToricPower.ReconstructionCompletionAffineCoefficients
public import ToricPower.DiagonalTopAdjunctionChart
public import ToricPower.ReconstructionCompletionProjectionEvaluation
public import ToricPower.ReconstructionCompletionChartOver

/-! # The common actual overlap target

The two source complexes are compared using literal sections on the
intersection chart. Both target isomorphisms are made from the original
projection, original diagonal unit, and ordinary open base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

universe u

/-- The literal direct-image global sections retain the normalized
adjunct of each original unit-source section. -/
theorem reconstruction_pushforwardGlobalSections_unit
    (k : Type u) [Field k] {W Z : Scheme.{u}}
    [W.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (g : W ⟶ Z) [g.IsOver (Spec (.of k))] (M : W.Modules)
    (s : (FiniteCover.schemeBaseSections k Z ⊤).obj ((Scheme.Modules.pushforward g).obj M)) :
    (moduleUnitActualSectionsLinearEquiv k W M).symm
      ((pushforwardBaseSectionsLinearEquiv k g M ⊤) s) =
      (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          ((moduleUnitActualSectionsLinearEquiv k Z ((Scheme.Modules.pushforward g).obj M)).symm s) := by
  apply (moduleUnitActualSectionsLinearEquiv k W M).injective
  rw [LinearEquiv.apply_symm_apply]
  have actual : moduleUnitActualSectionsLinearEquiv k W M
      ((Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          ((moduleUnitActualSectionsLinearEquiv k Z ((Scheme.Modules.pushforward g).obj M)).symm s)) =
      (pushforwardBaseSectionsLinearEquiv k g M ⊤)
        (moduleUnitActualSectionsLinearEquiv k Z ((Scheme.Modules.pushforward g).obj M)
          ((moduleUnitActualSectionsLinearEquiv k Z ((Scheme.Modules.pushforward g).obj M)).symm s)) :=
    normalizedUnitAdjunct_section g M _ ⊤
  simpa only [LinearEquiv.apply_symm_apply] using actual.symm

/-- Successive pullback followed by genuine ordinary restriction. -/
def reconstructionOverlapRestrictionIso {W U X : Scheme.{u}}
    (r : W ⟶ U) (f : U ⟶ X) [IsOpenImmersion r] [IsOpenImmersion f]
    (M : X.Modules) :
    ((Scheme.Modules.pullback f).obj M).restrict r ≅ M.restrict (r ≫ f) :=
  (Scheme.Modules.restrictFunctorIsoPullback r).app ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp r f).app M ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (r ≫ f)).app M).symm

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "jσ" => fan.affineToricChartι σ
local notation "jτ" => fan.affineToricChartι τ
local notation "l" => fan.affineToricOverlapLeft σ τ
local notation "r" => fan.affineToricOverlapRight σ τ
local notation "m" => r ≫ jτ
local notation "W" => fan.affineToricChart (σ ⊓ τ)
local notation "Γσ" => FiniteCover.schemeBaseSections ℂ (fan.affineToricChart σ) ⊤
local notation "ΓW" => FiniteCover.schemeBaseSections ℂ W ⊤
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ _ ⊤
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))
local notation "δ" => toricDiagonal fan
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "Jq" => dualDiagonalLineQuasicoherent fan nonempty regular basis rays
local notation "E" => quasicoherentAffineUnitImage jτ

local instance reconstructionRawTargetOverlapLeft : IsOpenImmersion l :=
  fan.isOpenImmersion_affineToricOverlapLeft σ τ
local instance reconstructionRawTargetOverlapRight : IsOpenImmersion r :=
  fan.isOpenImmersion_affineToricOverlapRight σ τ
local instance reconstructionRawTargetChartAffine : IsAffineHom jτ :=
  toricChartInclusion_isAffineHom fan τ

/-- The original overlap square has precisely the required inverse-image open. -/
theorem reconstructionOverlapPreimage : jτ ⁻¹ᵁ (jσ).opensRange ≤ (r).opensRange := by
  let square := (fan.affineToricOverlap_isPullback σ τ).flip
  apply le_of_eq
  calc
    jτ ⁻¹ᵁ (jσ).opensRange = (pullback.fst jτ jσ).opensRange :=
      (Scheme.Hom.opensRange_pullbackFst jσ jτ).symm
    _ = (square.isoPullback.hom ≫ pullback.fst jτ jσ).opensRange :=
      (Scheme.Hom.opensRange_comp_of_isIso _ _).symm
    _ = (r).opensRange := by simp only [square.isoPullback_hom_fst]

/-- The projection and genuine open base change on the actual first chart. -/
def reconstructionRawEvaluationTargetSheafIso :
    (Scheme.Modules.pullback jσ).obj ((J) ⊗ (E).obj) ≅
      (Scheme.Modules.pushforward l).obj ((J).restrict m) := by
  letI := dualDiagonalLineSheaf_isInvertible fan nonempty regular basis rays
  letI := BondalThomsen.schemeProjectionFormulaMap_isIso_of_isInvertible jτ J
  exact (Scheme.Modules.pullback jσ).mapIso
      (asIso (BondalThomsen.schemeProjectionFormulaMap jτ J)) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback jσ).app
      ((Scheme.Modules.pushforward jτ).obj ((Scheme.Modules.pullback jτ).obj J))).symm ≪≫
    pushforwardRestrictionIso jτ l r jσ
      (fan.affineToricOverlap_isPullback σ τ).w.symm
      (reconstructionOverlapPreimage fan σ τ) ((Scheme.Modules.pullback jτ).obj J) ≪≫
    (Scheme.Modules.pushforward l).mapIso (reconstructionOverlapRestrictionIso r jτ J)

/-- The literal target of geometric evaluation is the common overlap module. -/
def reconstructionRawEvaluationTargetIso :
    (reconstructionRawSectionFunctor fan σ).obj ((tensorLeft Jq).obj E) ≅
      (ΓW).obj ((J).restrict m) :=
  (Γσ).mapIso (reconstructionRawEvaluationTargetSheafIso fan nonempty regular basis rays σ τ) ≪≫
    (pushforwardBaseSectionsLinearEquiv ℂ l ((J).restrict m) ⊤).toModuleIso

/-- The original diagonal square, with the displayed composite overlap inclusion. -/
theorem reconstructionDiagonalCompositeSquare : m ≫ δ = g ≫ chart := by
  rw [fan.affineToricOverlapRight_comp_affineToricChartι]
  exact (diagonalProductChart_isPullback fan basis rays σ τ).w

/-- Its inverse image is the same literal overlap open. -/
theorem reconstructionDiagonalCompositePreimage : δ ⁻¹ᵁ (chart).opensRange ≤ (m).opensRange := by
  apply le_of_eq
  calc
    δ ⁻¹ᵁ (chart).opensRange = (fan.affineToricChartι (σ ⊓ τ)).opensRange :=
      diagonalChart_preimage_opensRange fan basis rays σ τ
    _ = (m).opensRange := by
      apply TopologicalSpace.Opens.ext
      change Set.range (fan.affineToricChartι (σ ⊓ τ)) = Set.range (m)
      exact congrArg (fun f : W ⟶ X => Set.range f)
        (fan.affineToricOverlapRight_comp_affineToricChartι σ τ).symm

/-- The same overlap target through the actual diagonal adjunction unit. -/
def reconstructionRawDiagonalTargetSheafIso :
    (Scheme.Modules.pullback chart).obj H ≅
      (Scheme.Modules.pushforward g).obj ((J).restrict m) :=
  (Scheme.Modules.pullback chart).mapIso
      (dualDiagonalTopPushforwardIso fan nonempty regular basis rays) ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback chart).app
      ((Scheme.Modules.pushforward δ).obj J)).symm ≪≫
    pushforwardRestrictionIso δ g m chart
      (reconstructionDiagonalCompositeSquare fan basis rays σ τ)
      (reconstructionDiagonalCompositePreimage fan basis rays σ τ) J

/-- The diagonal quotient has that identical actual scalar target. -/
def reconstructionRawDiagonalTargetIso :
    (ΓP).obj ((Scheme.Modules.pullback chart).obj H) ≅
      (ΓW).obj ((J).restrict m) :=
  (ΓP).mapIso (reconstructionRawDiagonalTargetSheafIso fan nonempty regular basis rays σ τ) ≪≫
    (pushforwardBaseSectionsLinearEquiv ℂ g ((J).restrict m) ⊤).toModuleIso

end ToricPower

end
