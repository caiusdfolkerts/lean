module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Single

/-! # The canonical image of a single-source augmentation

An additive functor carries an actual degree-zero augmentation through
its specified single-complex comparison. These formulas retain the
given degree-zero map, including an independent scalar coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

variable {A D : Type*} [Category* A] [Category* D]
  [Preadditive A] [Preadditive D] [HasZeroObject A] [HasZeroObject D]
  (F : A ⥤ D) [F.Additive] {Z : A} {I : CochainComplex A ℕ}

theorem mappedSingleAugmentation_core_zero
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Z ≫
      (F.mapHomologicalComplex (.up ℕ)).map ι).f 0 = F.map (ι.f 0) := by
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f,CochainComplex.single₀ObjXSelf,
    Iso.refl_hom,Iso.refl_inv,F.map_id,Category.id_comp]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

def mappedSingleAugmentation {V : D} (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (CochainComplex.single₀ D).obj V ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I :=
  (CochainComplex.single₀ D).map a ≫
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Z ≫
      (F.mapHomologicalComplex (.up ℕ)).map ι

theorem mappedSingleAugmentation_zero {V : D} (a : V ⟶ F.obj Z)
    (ι : (CochainComplex.single₀ A).obj Z ⟶ I) :
    (mappedSingleAugmentation F a ι).f 0 = a ≫ F.map (ι.f 0) := by
  change ((CochainComplex.single₀ D).map a).f 0 ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Z ≫
      (F.mapHomologicalComplex (.up ℕ)).map ι).f 0 = _
  rw [mappedSingleAugmentation_core_zero]
  rw [CochainComplex.single₀_map_f_zero]

end ToricPower

end
