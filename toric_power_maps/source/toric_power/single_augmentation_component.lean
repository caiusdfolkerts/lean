module

public import Mathlib.Algebra.Homology.Additive
public import ToricPower.TopSingleQuotient

/-!
# The specified component of a single-target augmentation

This small interface retains the original chain map while hiding only
the implementation of the single complex. Its formulas concern actual
components and their actual behavior under composition and functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v'

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {K L : CochainComplex C ℕ} {n : ℕ} {M : C}

/-- The original degree-`n` component, followed by the canonical
identification of the nonzero term of the single complex. -/
def singleAugmentationComponent
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) : K.X n ⟶ M :=
  f.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n M).hom

@[reassoc]
theorem singleAugmentationComponent_comp
    (g : L ⟶ K) (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) :
    singleAugmentationComponent (g ≫ f) = g.f n ≫ singleAugmentationComponent f := by
  simp only [singleAugmentationComponent, HomologicalComplex.comp_f, Category.assoc]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]

theorem singleAugmentationComponent_map
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) :
    singleAugmentationComponent
      ((F.mapHomologicalComplex (.up ℕ)).map f ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M) =
      F.map (singleAugmentationComponent f) := by
  simp only [singleAugmentationComponent, HomologicalComplex.comp_f,
    Category.assoc]
  change F.map (f.f n) ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app M).f n ≫
      (HomologicalComplex.singleObjXSelf (.up ℕ) n (F.obj M)).hom = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, F.map_comp]

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : CochainComplex C ℕ} {n : ℕ} {M : C}

theorem topHomologyQuotient_toComponent
    (outgoing : K.d n (n+1) = 0)
    (f : K ⟶ (HomologicalComplex.single C (.up ℕ) n).obj M) :
    K.pOpcycles n ≫ (K.isoHomologyι n (n+1) (by simp) outgoing).inv ≫
      HomologicalComplex.homologyMap f n ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) n M).hom =
      singleAugmentationComponent f :=
  topHomologyQuotient_toSingle outgoing f

end Abelian

end ToricPower

end
