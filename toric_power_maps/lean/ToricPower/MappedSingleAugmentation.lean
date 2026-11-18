module

public import Mathlib.Algebra.Homology.Additive
public import ToricPower.MappedSingleSourceAugmentation
public import ToricPower.TopHomologyAugmentation

/-!
# An actual augmentation component under an additive functor

The canonical comparison with a single complex retains the original
top component. This is a statement about the specified chain map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  {K : CochainComplex C ℕ} (n : ℕ) (M : C)
  (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M)

/-- Exact equality of the original component after the canonical
single-complex comparison. No exactness of the functor is required. -/
theorem mapHomToSingle_component :
    (((F.mapHomologicalComplex (.up ℕ)).map f).f n) ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M).f n ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) n (F.obj M)).hom =
      F.map (f.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom) := by
  change F.map (f.f n) ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M).f n ≫
      (HomologicalComplex.singleObjXSelf (.up ℕ) n (F.obj M)).hom = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, F.map_comp]

end ToricPower

end
