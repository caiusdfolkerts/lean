module

public import ToricPower.ReconstructionCompletionRawTargets
public import ToricPower.ReconstructionCompletionDiagonalSectionSquare
public import ToricPower.ReconstructionCompletionOverlapEvaluation
public import ToricPower.DiagonalFactorFrameRestriction

/-! # The actual affine reconstruction square on arbitrary sections

The two normalized adjuncts meet on the literal overlap restriction.
The comparison is for arbitrary sections and arbitrary top maps, and
retains the original exterior retraction.
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
local notation "leftMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductFirstCoordinate fan basis rays σ τ)))
local notation "rightMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductSecondCoordinate fan basis rays σ τ)))

local instance reconstructionRawSquareOverlapLeft : IsOpenImmersion l :=
  fan.isOpenImmersion_affineToricOverlapLeft σ τ
local instance reconstructionRawSquareOverlapRight : IsOpenImmersion r :=
  fan.isOpenImmersion_affineToricOverlapRight σ τ
local instance reconstructionRawSquareChartAffine : IsAffineHom jτ :=
  toricChartInclusion_isAffineHom fan τ

/-- The first original chart section on the displayed overlap. -/
def reconstructionFirstOverlapUnit (L : (X).Modules)
    (a : 𝟙_ (Uσ).Modules ⟶ (Scheme.Modules.pullback jσ).obj L) :
    𝟙_ (W).Modules ⟶ L.restrict m :=
  (Scheme.Modules.pullbackObjUnitIso l).inv ≫ (Scheme.Modules.pullback l).map a ≫
    (Scheme.Modules.pullbackComp l jσ).hom.app L ≫
    (Scheme.Modules.pullbackCongr (fan.affineToricOverlap_isPullback σ τ).w).hom.app L ≫
    (Scheme.Modules.restrictFunctorIsoPullback m).inv.app L

/-- The second original chart section on the identical displayed overlap. -/
def reconstructionSecondOverlapUnit (M : (X).Modules)
    (b : 𝟙_ (Uτ).Modules ⟶ (Scheme.Modules.pullback jτ).obj M) :
    𝟙_ (W).Modules ⟶ M.restrict m :=
  (Scheme.Modules.pullbackObjUnitIso r).inv ≫ (Scheme.Modules.pullback r).map b ≫
    (Scheme.Modules.pullbackComp r jτ).hom.app M ≫
    (Scheme.Modules.restrictFunctorIsoPullback m).inv.app M

/-- The actual exterior product transported to the original product chart. -/
def reconstructionRawExteriorUnit (L M : (X).Modules)
    (a : 𝟙_ (Uσ).Modules ⟶ (Scheme.Modules.pullback jσ).obj L)
    (b : 𝟙_ (Uτ).Modules ⟶ (Scheme.Modules.pullback jτ).obj M) :
    𝟙_ (Z).Modules ⟶ (Scheme.Modules.pullback chart).obj (schemeExteriorSheaf p q L M) :=
  (λ_ (𝟙_ (Z).Modules)).inv ≫
    (externalSquareUnitSection p chart jσ leftMap
      (diagonalProductChartι_first fan basis rays σ τ) L a ⊗ₘ
      externalSquareUnitSection q chart jτ rightMap
        (diagonalProductChartι_second fan basis rays σ τ) M b) ≫
    (Scheme.Modules.pullbackTensorIsoOfOpenImmersion chart
      ((Scheme.Modules.pullback p).obj L) ((Scheme.Modules.pullback q).obj M)).inv

/-- The original evaluation target identifies its normalized adjunct
with the two original overlap sections and the specified target map. -/
theorem reconstructionRawEvaluation_target_unit
    (L M : (X).Modules) (x : 𝟙_ (X).Modules ⟶ M ⊗ E)
    (a : 𝟙_ (Uσ).Modules ⟶ (Scheme.Modules.pullback jσ).obj L)
    (β : L ⊗ M ⟶ J) :
    (Scheme.Modules.pullbackObjUnitIso l).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction l).homEquiv _ _).symm
          (a ≫ (Scheme.Modules.pullback jσ).map
            ((ρ_ L).inv ≫ L ◁ x ≫ (α_ L M E).inv ≫ β ▷ E) ≫
            (reconstructionRawEvaluationTargetSheafIso fan nonempty regular basis rays σ τ).hom) =
      (λ_ (𝟙_ (W).Modules)).inv ≫
        (reconstructionFirstOverlapUnit fan σ τ L a ⊗ₘ
          reconstructionSecondOverlapUnit fan σ τ M
            ((Scheme.Modules.pullbackObjUnitIso jτ).inv ≫
              ((Scheme.Modules.pullbackPushforwardAdjunction jτ).homEquiv _ _).symm
                (x ≫ BondalThomsen.schemeProjectionFormulaMap jτ M))) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor m) L M ≫
        (Scheme.Modules.restrictFunctor m).map β := by
  change (Scheme.Modules.pullbackObjUnitIso l).inv ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction l).homEquiv _ _).symm
      (a ≫ (Scheme.Modules.pullback jσ).map _ ≫
        (Scheme.Modules.pullback jσ).map (BondalThomsen.schemeProjectionFormulaMap jτ J) ≫
        (Scheme.Modules.restrictFunctorIsoPullback jσ).inv.app _ ≫
        pushforwardRestrictionMap jτ l r jσ (fan.affineToricOverlap_isPullback σ τ).w.symm _ ≫
        (Scheme.Modules.pushforward l).map (reconstructionOverlapRestrictionIso r jτ J).hom) = _
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [reconstruction_projectionFormulaMap_evaluation_map jτ L M J x β]
  rw [← Category.assoc _ _ ((Scheme.Modules.pushforward l).map
      (reconstructionOverlapRestrictionIso r jτ J).hom),
    ← Category.assoc _ _ ((Scheme.Modules.pushforward l).map
      (reconstructionOverlapRestrictionIso r jτ J).hom),
    ← Category.assoc _ _ ((Scheme.Modules.pushforward l).map
      (reconstructionOverlapRestrictionIso r jτ J).hom),
    (Scheme.Modules.pullbackPushforwardAdjunction l).homEquiv_naturality_right_symm]
  simpa only [reconstructionOverlapRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv,
    reconstructionFirstOverlapUnit, reconstructionSecondOverlapUnit, Category.assoc] using
    normalizedSquareTensorAdjunct_overlap jτ l r jσ
      (fan.affineToricOverlap_isPullback σ τ).w.symm L M J a
      ((Scheme.Modules.pullbackObjUnitIso jτ).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction jτ).homEquiv _ _).symm
          (x ≫ BondalThomsen.schemeProjectionFormulaMap jτ M)) β

/-- An arbitrary original top map retains its actual diagonal adjunct. -/
@[reassoc]
theorem reconstructionRawDiagonalTargetSheafIso_map {B : (Y).Modules} (γ : B ⟶ H) :
    (Scheme.Modules.pullback chart).map γ ≫
        (reconstructionRawDiagonalTargetSheafIso fan nonempty regular basis rays σ τ).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((pullbackSquareIso δ g m chart
            (reconstructionDiagonalCompositeSquare fan basis rays σ τ)).hom.app B ≫
          (Scheme.Modules.restrictFunctorIsoPullback m).inv.app ((Scheme.Modules.pullback δ).obj B) ≫
          (Scheme.Modules.restrictFunctor m).map ((Scheme.Modules.pullback δ).map γ)) := by
  have original := (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.naturality γ
  change γ ≫ (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H =
    (Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app B ≫
      (Scheme.Modules.pushforward δ).map ((Scheme.Modules.pullback δ).map γ) at original
  change (Scheme.Modules.pullback chart).map γ ≫
    (Scheme.Modules.pullback chart).map ((Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H) ≫
    (Scheme.Modules.restrictFunctorIsoPullback chart).inv.app ((Scheme.Modules.pushforward δ).obj J) ≫
    pushforwardRestrictionMap δ g m chart (reconstructionDiagonalCompositeSquare fan basis rays σ τ) J = _
  rw [← Functor.map_comp_assoc, original]
  exact pullback_pushforwardRestrictionMap_homEquiv δ g m chart
    (reconstructionDiagonalCompositeSquare fan basis rays σ τ) ((Scheme.Modules.pullback δ).map γ)

/-- Exterior sections and geometric tensor evaluation have the identical
normalized overlap map whenever their actual top maps agree under retraction. -/
theorem reconstructionRawDiagonal_target_unit
    (L M : (X).Modules)
    (a : 𝟙_ (Uσ).Modules ⟶ (Scheme.Modules.pullback jσ).obj L)
    (b : 𝟙_ (Uτ).Modules ⟶ (Scheme.Modules.pullback jτ).obj M)
    (β : L ⊗ M ⟶ J) (γ : schemeExteriorSheaf p q L M ⟶ H)
    (top : (Scheme.Modules.pullback δ).map γ =
      schemeExternalSectionRetractionMap δ p q
        (pullback.diagonal_fst fan.algebraicRealizationStructureMap)
        (pullback.diagonal_snd fan.algebraicRealizationStructureMap) L M ≫ β) :
    (Scheme.Modules.pullbackObjUnitIso g).inv ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
          (reconstructionRawExteriorUnit fan basis rays σ τ L M a b ≫
            (Scheme.Modules.pullback chart).map γ ≫
            (reconstructionRawDiagonalTargetSheafIso fan nonempty regular basis rays σ τ).hom) =
      (λ_ (𝟙_ (W).Modules)).inv ≫
        (reconstructionFirstOverlapUnit fan σ τ L a ⊗ₘ
          reconstructionSecondOverlapUnit fan σ τ M b) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor m) L M ≫
        (Scheme.Modules.restrictFunctor m).map β := by
  exact reconstructionDiagonalSectionAdjunct_rightComposite δ p q chart g jσ jτ
    leftMap rightMap l r
    (pullback.diagonal_fst fan.algebraicRealizationStructureMap)
    (pullback.diagonal_snd fan.algebraicRealizationStructureMap)
    (reconstructionDiagonalCompositeSquare fan basis rays σ τ)
    (diagonalProductChartι_first fan basis rays σ τ)
    (diagonalProductChartι_second fan basis rays σ τ)
    (diagonalChartToIntersection_first fan basis rays σ τ)
    (diagonalChartToIntersection_second fan basis rays σ τ)
    (fan.affineToricOverlap_isPullback σ τ).w H L M a b β γ
    (reconstructionRawDiagonalTargetSheafIso fan nonempty regular basis rays σ τ).hom
    (reconstructionRawDiagonalTargetSheafIso_map fan nonempty regular basis rays σ τ γ) top


end ToricPower

end
