module

public import ToricPower.SingleAugmentationComponent
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Comparing specified single-target augmentations by their actual components -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} {M N : C} {n : ℕ}

/-- Actual single-target maps are determined by their specified top component. -/
theorem singleAugmentation_ext
    {f g : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M}
    (same : singleAugmentationComponent f = singleAugmentationComponent g) : f = g := by
  apply HomologicalComplex.to_single_hom_ext
  exact (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom).mp same

@[simp]
theorem singleAugmentationComponent_singleMap
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) (g : M ⟶ N) :
    singleAugmentationComponent (f ≫ (HomologicalComplex.single C (.up ℕ) n).map g) =
      singleAugmentationComponent f ≫ g := by
  simp only [singleAugmentationComponent, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The original square of actual augmentation maps follows from its
original component square, without choosing unrelated homology maps. -/
theorem singleAugmentation_comparison
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M)
    (g : L ⟶ (HomologicalComplex.single C (.up ℕ) n).obj N)
    (e : K ⟶ L) (t : M ⟶ N)
    (square : singleAugmentationComponent f ≫ t = e.f n ≫ singleAugmentationComponent g) :
    f ≫ (HomologicalComplex.single C (.up ℕ) n).map t = e ≫ g := by
  apply singleAugmentation_ext
  rw [singleAugmentationComponent_singleMap, singleAugmentationComponent_comp]
  exact square

/-- An isomorphic specified augmentation has the same actual
quasi-isomorphism property. -/
theorem singleAugmentation_quasiIso_of_comparison
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M)
    (g : L ⟶ (HomologicalComplex.single C (.up ℕ) n).obj N)
    (e : K ≅ L) (t : M ≅ N)
    (square : singleAugmentationComponent f ≫ t.hom = e.hom.f n ≫ singleAugmentationComponent g)
    [QuasiIso g] : QuasiIso f := by
  haveI : QuasiIso (f ≫ (HomologicalComplex.single C (.up ℕ) n).map t.hom) := by
    rw [singleAugmentation_comparison f g e.hom t.hom square]
    infer_instance
  exact (quasiIso_iff_comp_right f
    ((HomologicalComplex.single C (.up ℕ) n).map t.hom)).mp inferInstance

end ToricPower

end
