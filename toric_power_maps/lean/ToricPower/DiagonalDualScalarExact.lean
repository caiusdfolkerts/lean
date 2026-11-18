module

public import ToricPower.DiagonalDualScalarSections
public import ToricPower.SingleAugmentationComparison

/-!
# Exactness of the original scalar dual-diagonal augmentation

The map below uses the genuine global top quotient. The previously
verified affine component equality identifies this specified map with
the independently kernel-checked full ring-linear augmentation. Every
character and every coordinate-ring scalar is retained.
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
local notation "Sections" => FiniteCover.schemeBaseSections ℂ (Spec Ring) ⊤
local notation "Pull" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "Framed" => toricDiagonalFramedDualComplex fan regular basis rays σ τ
local notation "B" => dualDiagonalBoundaryModule A S T ℂ
local notation "Scalars" => ModuleCat.restrictScalars (algebraMap ℂ Ring)

/-- The original global quotient, in actual scalar sections on the
literal product chart. -/
def diagonalDualScalarAugmentation :
    ((Sections).mapHomologicalComplex (.up ℕ)).obj
      (((Pull).mapHomologicalComplex (.up ℕ)).obj K) ⟶
    (HomologicalComplex.single (ModuleCat ℂ) (.up ℕ) n).obj
      ((Sections).obj ((Pull).obj H)) :=
  HomologicalComplex.mkHomToSingle
    ((Sections).map ((Pull).map (dualDiagonalTopQuotient fan nonempty regular basis rays)))
    (fun q relation => by
      change (Sections).map ((Pull).map ((K).d q n)) ≫
        (Sections).map ((Pull).map (dualDiagonalTopQuotient fan nonempty regular basis rays)) = 0
      rw [← Functor.map_comp, ← Functor.map_comp,
        dualDiagonalTopQuotient_boundary, Functor.map_zero, Functor.map_zero])

@[simp]
theorem diagonalDualScalarAugmentation_component :
    singleAugmentationComponent (diagonalDualScalarAugmentation fan nonempty regular basis rays σ τ) =
      (Sections).map ((Pull).map (dualDiagonalTopQuotient fan nonempty regular basis rays)) := by
  simp only [singleAugmentationComponent, diagonalDualScalarAugmentation,
    HomologicalComplex.mkHomToSingle_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual specified scalar augmentation is a quasi-isomorphism. -/
theorem diagonalDualScalarAugmentation_quasiIso :
    QuasiIso (diagonalDualScalarAugmentation fan nonempty regular basis rays σ τ) := by
  let ringAug := diagonalFramedDualAugmentation ℂ A S T
    (toricDiagonalCellFrames fan regular basis rays σ τ)
  let scalarAug := ((Scalars).mapHomologicalComplex (.up ℕ)).map ringAug ≫
    (HomologicalComplex.singleMapHomologicalComplex Scalars (.up ℕ) n).hom.app B
  letI := diagonalFramedDualAugmentation_quasiIso ℂ A S T
    (toricDiagonalCellFrames fan regular basis rays σ τ)
  haveI : QuasiIso scalarAug := inferInstance
  apply singleAugmentation_quasiIso_of_comparison _ scalarAug
    (diagonalInternalDualScalarSectionsIso fan nonempty regular basis rays σ τ)
    (diagonalTopScalarSectionsIso fan nonempty regular basis rays σ τ)
  rw [diagonalDualScalarAugmentation_component]
  have component : singleAugmentationComponent ringAug =
      diagonalFramedDualTopQuotient ℂ A S T
        (toricDiagonalCellFrames fan regular basis rays σ τ) := by
    simp only [ringAug, singleAugmentationComponent, diagonalFramedDualAugmentation,
      augmentationOfTopHomology, HomologicalComplex.mkHomToSingle_f,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have mapped := singleAugmentationComponent_map Scalars ringAug
  change singleAugmentationComponent scalarAug = _ at mapped
  rw [mapped, component]
  exact diagonalTopScalarSections_quotient fan nonempty regular basis rays σ τ

end ToricPower

end
