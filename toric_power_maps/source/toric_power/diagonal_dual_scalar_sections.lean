module

public import ToricPower.DiagonalTopQuotientChart
public import ToricPower.DiagonalAffineTopQuotient
public import ToricPower.DiagonalTopQuotient
public import ToricPower.AffineTildeMappedSections

/-!
# Actual scalar sections of the original dual diagonal

The specified product-chart comparison and the literal affine tilde
section map identify the full dual sheaf complex with its original
ring-linear matrix after scalar restriction. The top quotient retains
its original component through this comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "Ring" => CommRingCat.of (DiagonalChartRing ℂ A S T)
local notation "U" => Spec Ring
local notation "Sections" => FiniteCover.schemeBaseSections ℂ U ⊤
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "Framed" => toricDiagonalFramedDualComplex fan regular basis rays σ τ
local notation "B" => dualDiagonalBoundaryModule A S T ℂ

/-- Every original differential is retained in the complete affine
scalar comparison. -/
def diagonalInternalDualScalarSectionsIso :
    ((Sections).mapHomologicalComplex (.up ℕ)).obj
      (((P).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((ModuleCat.restrictScalars (algebraMap ℂ Ring)).mapHomologicalComplex (.up ℕ)).obj Framed :=
  ((Sections).mapHomologicalComplex (.up ℕ)).mapIso
    (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ ≪≫
      (toricDiagonalFramedDualInternalIso fan regular basis rays σ τ).symm) ≪≫
    (affineTildeMappedSectionsIso ℂ Ring (.up ℕ)).app Framed

/-- The actual top sheaf has the original scalar boundary-module
coordinates, using the same specified chart augmentation. -/
def diagonalTopScalarSectionsIso :
    (Sections).obj ((P).obj (dualDiagonalTopSheaf fan nonempty regular basis rays)) ≅
      (ModuleCat.restrictScalars (algebraMap ℂ Ring)).obj B :=
  (Sections).mapIso (diagonalGlobalInternalDualTopChartIso fan nonempty regular basis rays σ τ) ≪≫
    (affineTildeBaseSectionsIso ℂ Ring).symm.app B

/-- In its original affine scalar coordinates, the genuine global top
quotient is the independently verified ring-linear top quotient. -/
theorem diagonalTopScalarSections_quotient :
    (Sections).map ((P).map (dualDiagonalTopQuotient fan nonempty regular basis rays)) ≫
      (diagonalTopScalarSectionsIso fan nonempty regular basis rays σ τ).hom =
    (diagonalInternalDualScalarSectionsIso fan nonempty regular basis rays σ τ).hom.f n ≫
      (ModuleCat.restrictScalars (algebraMap ℂ Ring)).map
        (diagonalFramedDualTopQuotient ℂ A S T
          (toricDiagonalCellFrames fan regular basis rays σ τ)) := by
  let e := diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ
  let a := toricDiagonalFramedDualInternalIso fan regular basis rays σ τ
  let t := toricDiagonalInternalDualBoundaryAugmentation fan regular basis rays σ τ
  have component : singleAugmentationComponent t =
      a.inv.f n ≫ tilde.map (diagonalFramedDualTopQuotient ℂ A S T
        (toricDiagonalCellFrames fan regular basis rays σ τ)) := by
    apply (cancel_epi (a.hom.f n)).mp
    rw [← Category.assoc]
    have inverse : a.hom.f n ≫ a.inv.f n = 𝟙 _ :=
      congrArg (fun f => f.f n) a.hom_inv_id
    rw [inverse, Category.id_comp]
    exact toricDiagonalInternalDualBoundaryAugmentation_component fan regular basis rays σ τ
  have quotient := diagonalGlobalInternalDualTopChartIso_quotient
    fan nonempty regular basis rays σ τ
  change (P).map (dualDiagonalTopQuotient fan nonempty regular basis rays) ≫
      (diagonalGlobalInternalDualTopChartIso fan nonempty regular basis rays σ τ).hom =
        e.hom.f n ≫ singleAugmentationComponent t at quotient
  rw [component] at quotient
  simp only [diagonalTopScalarSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, ← Functor.map_comp_assoc]
  rw [quotient, (Sections).map_comp, (Sections).map_comp]
  have natural := (affineTildeBaseSectionsIso ℂ Ring).inv.naturality
    (diagonalFramedDualTopQuotient ℂ A S T
      (toricDiagonalCellFrames fan regular basis rays σ τ))
  change (Sections).map (tilde.map _) ≫ _ = _ at natural
  simp only [Category.assoc]
  rw [natural]
  change _ = ((Sections).map (e.hom.f n ≫ a.inv.f n) ≫
    (affineTildeBaseSectionsIso ℂ Ring).inv.app ((Framed).X n)) ≫ _
  rw [(Sections).map_comp]
  simp only [Category.id_comp, Category.assoc]
  rfl

end ToricPower

end
