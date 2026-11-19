module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Actual homology and bounds under an exact derived functor

The comparison is assembled from the canonical localization comparison,
the actual homology functors, and exact preservation of homology on
ordinary complexes. It retains the literal induced derived functor.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v u' v' w w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def exactDerivedHomologyIso (X : DerivedCategory A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor A q).obj X) :=
  let K := (DerivedCategory.Q (C := A)).objPreimage X
  let e := (DerivedCategory.Q (C := A)).objObjPreimageIso X
  (DerivedCategory.homologyFunctor B q).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor B q).mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
    (DerivedCategory.homologyFunctorFactors B q).app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≪≫
    (K.sc q).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors A q).app K).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor A q).mapIso e)

theorem exactDerived_preserves_isGE (X : DerivedCategory A) (a : ℤ) [X.IsGE a] :
    (F.mapDerivedCategory.obj X).IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro q hq
  exact (exactDerivedHomologyIso F X q).isZero_iff.mpr
    (F.map_isZero (DerivedCategory.isZero_of_isGE X a q hq))

theorem exactDerived_preserves_isLE (X : DerivedCategory A) (b : ℤ) [X.IsLE b] :
    (F.mapDerivedCategory.obj X).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro q hq
  exact (exactDerivedHomologyIso F X q).isZero_iff.mpr
    (F.map_isZero (DerivedCategory.isZero_of_isLE X b q hq))

theorem exactDerived_preserves_bounded (X : DerivedCategory A)
    (bounded : DerivedCategory.TStructure.t.bounded X) :
    DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj X) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bounded
  letI := ha
  letI := hb
  exact ⟨⟨a, exactDerived_preserves_isGE F X a⟩,
    ⟨b, exactDerived_preserves_isLE F X b⟩⟩

end ToricPower

end
