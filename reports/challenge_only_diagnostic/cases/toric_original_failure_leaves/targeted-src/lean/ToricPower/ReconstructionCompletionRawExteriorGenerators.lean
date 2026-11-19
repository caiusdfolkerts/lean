module

public import ToricPower.ReconstructionCompletionRawComplex
public import ToricPower.ReconstructionCompletionDiagonalGenerators
public import ToricPower.ReconstructionCompletionExternalRetraction

/-! # Original generators in the raw affine source comparison

Every Hom coefficient and every affine section remains visible. The
exterior coefficient is the original product of unit-source maps.
-/

@[expose] public noncomputable section

set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric Opposite
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "Qq" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "P₀" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays
local notation "jσ" => fan.affineToricChartι σ
local notation "jτ" => fan.affineToricChartι τ
local notation "Ringσ" => CommRingCat.of (affineCoordinateRing fan.lattice σ.val)
local notation "Ringτ" => CommRingCat.of (affineCoordinateRing fan.lattice τ.val)
local notation "Qσ" => (Q ⋙ Scheme.Modules.pullback jσ) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec Ringσ) ⊤
local notation "Rτ" => (R ⋙ Scheme.Modules.pullback jτ) ⋙
  FiniteCover.schemeBaseSections ℂ (Spec Ringτ) ⊤
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A
  (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ))
local notation "ΓP" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "Pull" => Scheme.Modules.pullback chart
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "F" => reconstructionRawSectionFunctor fan σ
local notation "Ext" => exteriorLabelDiagram fan Q R
local notation "S" => Cellular.covariantCopowerDiagram ℂ Qσ Rτ
local notation "E" => quasicoherentAffineUnitImage jτ
local notation "M" => (Cellular.homDiagram ℂ P₀).obj E
local notation "leftMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductFirstCoordinate fan basis rays σ τ)))
local notation "rightMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductSecondCoordinate fan basis rays σ τ)))

local instance reconstructionRawExteriorGeneratorsQCohBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawExteriorGeneratorsSheafBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance reconstructionRawExteriorGeneratorsChartAffine (κ : fan.cones) : IsAffineHom (fan.affineToricChartι κ) :=
  toricChartInclusion_isAffineHom fan κ
local instance reconstructionRawExteriorGeneratorsCells (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

/-- The raw scalar diagonal comparison retains the original top quotient. -/
@[reassoc]
theorem reconstructionRawDiagonalScalar_top (d : NormalizedCell A n) :
    arrangementCellularCochainInclusion A ℂ S n d ≫
        (reconstructionRawDiagonalScalarIso fan nonempty regular basis rays σ τ).inv.f n ≫
        (Pull ⋙ ΓP).map (dualDiagonalTopQuotient fan nonempty regular basis rays) =
      (diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app ⟨n,d⟩ ≫
        (ΓP).map ((diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app ⟨n,d⟩) ≫
        (Pull ⋙ ΓP).map (reconstructionDiagonalExternalTop fan nonempty regular basis rays d) := by
  change _ ≫ ((arrangementCellularCochainFunctor A ℂ).map
      (diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom).f n ≫
    ((arrangementCellularCochainFunctor A ℂ).map
      (Functor.whiskerRight
        (diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv ΓP)).f n ≫
    (cellularCoefficientTermIso A ℂ (Pull ⋙ ΓP) Ext n).inv ≫
    (Pull ⋙ ΓP).map ((diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays).inv.f n) ≫
    (Pull ⋙ ΓP).map (dualDiagonalTopQuotient fan nonempty regular basis rays) = _
  rw [cellularCochainMap_inclusion_assoc, cellularCochainMap_inclusion_assoc]
  have inclusion :
      arrangementCellularCochainInclusion A ℂ ((Ext ⋙ Pull) ⋙ ΓP) n d ≫
        (cellularCoefficientTermIso A ℂ (Pull ⋙ ΓP) Ext n).inv =
      (Pull ⋙ ΓP).map (arrangementCellularCochainInclusion A ℂ Ext n d) :=
    (Iso.comp_inv_eq (cellularCoefficientTermIso A ℂ (Pull ⋙ ΓP) Ext n)).mpr
      (cellularCoefficientTermIso_inclusion A ℂ (Pull ⋙ ΓP) Ext n d).symm
  have mappedInclusion := congrArg (fun u => u ≫
      (Pull ⋙ ΓP).map ((diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays).inv.f n) ≫
      (Pull ⋙ ΓP).map (dualDiagonalTopQuotient fan nonempty regular basis rays)) inclusion
  have mappedTop :
      (Pull ⋙ ΓP).map (arrangementCellularCochainInclusion A ℂ Ext n d) ≫
        (Pull ⋙ ΓP).map ((diagonalInternalDualExteriorCochainIso fan nonempty regular basis rays).inv.f n) ≫
        (Pull ⋙ ΓP).map (dualDiagonalTopQuotient fan nonempty regular basis rays) =
      (Pull ⋙ ΓP).map (reconstructionDiagonalExternalTop fan nonempty regular basis rays d) := by
    simpa only [Functor.map_comp] using congrArg (Pull ⋙ ΓP).map
      (reconstructionDiagonalExterior_top fan nonempty regular basis rays d)
  simpa only [Category.assoc, Functor.whiskerRight_app] using congrArg (fun u =>
    (diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app ⟨n,d⟩ ≫
      (ΓP).map ((diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app ⟨n,d⟩) ≫ u)
    (mappedInclusion.trans mappedTop)

/-- The original exterior coefficient on two arbitrary pulled chart sections. -/
theorem reconstructionRawExterior_unit (c : C)
    (s : (Qσ).obj c) (t : (Rτ).obj c) :
    (moduleUnitActualSectionsLinearEquiv ℂ (Spec Ring) ((Pull).obj ((Ext).obj c))).symm
      ((ΓP).map ((diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app c)
        ((diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app c
          (Cellular.vectorCopowerInclusion ℂ ((Qσ).obj c) ((Rτ).obj c) t s))) =
      (λ_ (𝟙_ (Spec Ring).Modules)).inv ≫
        (externalSquareUnitSection (toricDiagonalFirst fan) chart jσ leftMap
          (diagonalProductChartι_first fan basis rays σ τ) ((Q).obj c)
          ((moduleUnitActualSectionsLinearEquiv ℂ (fan.affineToricChart σ)
            ((Scheme.Modules.pullback jσ).obj ((Q).obj c))).symm s) ⊗ₘ
        externalSquareUnitSection (toricDiagonalSecond fan) chart jτ rightMap
          (diagonalProductChartι_second fan basis rays σ τ) ((R).obj c)
          ((moduleUnitActualSectionsLinearEquiv ℂ (fan.affineToricChart τ)
            ((Scheme.Modules.pullback jτ).obj ((R).obj c))).symm t)) ≫
        (Scheme.Modules.pullbackTensorIsoOfOpenImmersion chart
          ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj ((Q).obj c))
          ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj ((R).obj c))).inv := by
  have natural := moduleUnitActualSectionsLinearEquiv_symm_naturality ℂ
    ((diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app c)
    ((diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app c
      (Cellular.vectorCopowerInclusion ℂ ((Qσ).obj c) ((Rτ).obj c) t s))
  refine natural.trans ?_
  have coefficient :
      (diagonalAffineExteriorSectionDiagramIso fan nonempty regular basis rays σ τ).hom.app c
      (Cellular.vectorCopowerInclusion ℂ ((Qσ).obj c) ((Rτ).obj c) t s) =
      schemeExternalSection ℂ leftMap rightMap
        ((Scheme.Modules.pullback jσ).obj ((Q).obj c))
        ((Scheme.Modules.pullback jτ).obj ((R).obj c)) s t :=
    affineExternalSectionDiagramIso_inclusion ℂ Ringσ Ringτ Ring
      (AlgEquiv.symm (diagonalProductCoordinateEquiv fan basis rays σ τ))
      (Q ⋙ Scheme.Modules.pullback jσ) (R ⋙ Scheme.Modules.pullback jτ)
      (fun c => toricCartierPullbackFrame fan nonempty regular
        (arrangementDualLeftCoefficients fan basis rays c) σ)
      (fun c => toricCartierPullbackFrame fan nonempty regular
        (arrangementDualRightCoefficients fan basis rays c) τ) c s t
  refine (congrArg (fun v => (moduleUnitActualSectionsLinearEquiv ℂ (Spec Ring) _).symm v ≫
    (diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app c) coefficient).trans ?_
  rw [schemeExternalSection]
  erw [LinearEquiv.symm_apply_apply]
  have chartInverse :
      (diagonalExteriorChartDiagramIso fan nonempty regular basis rays σ τ).inv.app c =
      ((diagonalFirstPullbackComparison fan basis rays σ τ).inv.app ((Q).obj c) ⊗ₘ
        (diagonalSecondPullbackComparison fan basis rays σ τ).inv.app ((R).obj c)) ≫
      (Scheme.Modules.pullbackTensorIsoOfOpenImmersion chart
        ((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj ((Q).obj c))
        ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj ((R).obj c))).inv := by
    rfl
  rw [chartInverse]
  change ((λ_ (𝟙_ (Spec Ring).Modules)).inv ≫ (_ ⊗ₘ _)) ≫
    ((_ ⊗ₘ _) ≫ _) = _
  rw [Category.assoc, tensorHom_comp_tensorHom_assoc]
  all_goals dsimp only [externalSquareUnitSection, diagonalFirstPullbackComparison,
    diagonalSecondPullbackComparison]
  all_goals simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    schemePullbackUnitHomLinearMap, LinearMap.comp_apply, Linear.leftComp_apply,
    Functor.coe_mapLinearMap, Category.assoc]

end ToricPower

end
