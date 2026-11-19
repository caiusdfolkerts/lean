module

public import ToricPower.ExactDerivedHomology
public import ToricPower.DerivedHomologyProperty
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The precise essential image of a bounded derived inclusion

For an exact functor whose actual bounded derived functor is full, its
essential image consists exactly of bounded objects with all homology
in the original abelian essential image. The reverse direction constructs
a lift by finite truncation triangles; no coherent roof or bounded
complex lifting is assumed without proof.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace ToricPower

universe u v u' v' w w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

abbrev boundedDerivedInclusion : DerivedCategory.Bounded A ⥤ DerivedCategory B :=
  DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory

/-- The original abelian essential image contains the actual zero
objects because the exact functor is additive. -/
instance exactFunctor_essImage_containsZero : F.essImage.ContainsZero where
  exists_zero := ⟨F.obj 0, F.map_isZero (isZero_zero A), F.obj_mem_essImage 0⟩

theorem boundedDerived_single_mem_essImage (M : A) (q : ℤ) :
    (boundedDerivedInclusion F).essImage ((DerivedCategory.singleFunctor B q).obj (F.obj M)) := by
  let X : DerivedCategory.Bounded A :=
    ⟨(DerivedCategory.singleFunctor A q).obj M,
      ⟨⟨q, inferInstance⟩, ⟨q, inferInstance⟩⟩⟩
  exact ⟨X, ⟨(F.mapDerivedCategorySingleFunctor q).app M⟩⟩

theorem boundedDerived_essImage_implies_homology
    {X : DerivedCategory B} (member : (boundedDerivedInclusion F).essImage X) :
    DerivedCategory.TStructure.t.bounded X ∧ derivedHomologyIn F.essImage X := by
  obtain ⟨Y, ⟨e⟩⟩ := member
  constructor
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso e
      (exactDerived_preserves_bounded F Y.obj Y.property)
  · intro q
    exact ⟨(DerivedCategory.homologyFunctor A q).obj Y.obj,
      ⟨(exactDerivedHomologyIso F Y.obj q).symm ≪≫
        (DerivedCategory.homologyFunctor B q).mapIso e⟩⟩

variable [(boundedDerivedInclusion F).Full]

/-- Fullness of the actual bounded derived functor lifts the connecting
morphisms of truncation triangles, yielding the entire essential image. -/
theorem boundedDerived_mem_essImage_of_homology (X : DerivedCategory B)
    (bounded : DerivedCategory.TStructure.t.bounded X)
    (members : derivedHomologyIn F.essImage X) :
    (boundedDerivedInclusion F).essImage X := by
  apply bounded_mem_of_homology_in F.essImage (boundedDerivedInclusion F).essImage
    (fun M q hM => ?_) X bounded members
  obtain ⟨M', ⟨e⟩⟩ := hM
  exact (boundedDerivedInclusion F).essImage.prop_of_iso
    ((DerivedCategory.singleFunctor B q).mapIso e)
    (boundedDerived_single_mem_essImage F M' q)

/-- Equality of mathematical content, in both directions. -/
theorem boundedDerived_essImage_iff (X : DerivedCategory B) :
    (boundedDerivedInclusion F).essImage X ↔
      DerivedCategory.TStructure.t.bounded X ∧ derivedHomologyIn F.essImage X :=
  ⟨boundedDerived_essImage_implies_homology F,
    fun h => boundedDerived_mem_essImage_of_homology F X h.1 h.2⟩

end ToricPower

end
