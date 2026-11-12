module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Conservativity of a faithful exact functor after derived localization

A faithful exact functor detects zero homology. Its actual induced functor
on unbounded derived categories therefore detects zero objects. Applying
this to the cone of a morphism proves conservativity. This conclusion does
not assert full faithfulness on derived morphisms.

-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace ToricPower

universe u v u' v' w w'

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [F.Faithful]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- A faithful exact functor detects zero objects after the actual
unbounded derived localization. -/
theorem exactDerived_reflects_isZero (Y : DerivedCategory A)
    (hY : IsZero (F.mapDerivedCategory.obj Y)) : IsZero Y := by
  let K : CochainComplex A ℤ := DerivedCategory.Q.objPreimage Y
  let e : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have hQ : IsZero (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) :=
    (F.mapDerivedCategory.mapIso e).isZero_iff.mpr hY
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hFK : IsZero (DerivedCategory.Q.obj FK) :=
    (F.mapDerivedCategoryFactors.app K).isZero_iff.mp hQ
  have hH (n : ℤ) : IsZero (K.homology n) := by
    have hh : IsZero (FK.homology n) :=
      ((DerivedCategory.homologyFunctorFactors B n).app FK).isZero_iff.mp
        ((DerivedCategory.homologyFunctor B n).map_isZero hFK)
    have hFh : IsZero (F.obj (K.homology n)) :=
      ((K.sc n).mapHomologyIso F).isZero_iff.mp hh
    apply (IsZero.iff_id_eq_zero _).mpr
    apply F.map_injective
    simpa only [F.map_id, F.map_zero] using
      (IsZero.iff_id_eq_zero _).mp hFh
  let z : K ⟶ (0 : CochainComplex A ℤ) := 0
  have hz : QuasiIso z := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hH n).isIso
      ((HomologicalComplex.homologyFunctor A (.up ℤ) n).map_isZero (isZero_zero _)) _
  letI := hz
  have hK : IsZero (DerivedCategory.Q.obj K) :=
    (asIso (DerivedCategory.Q.map z)).isZero_iff.mpr
      (DerivedCategory.Q.map_isZero (isZero_zero _))
  exact e.isZero_iff.mp hK

theorem exactDerived_isZero_iff (Y : DerivedCategory A) :
    IsZero (F.mapDerivedCategory.obj Y) ↔ IsZero Y :=
  ⟨exactDerived_reflects_isZero F Y, fun h => F.mapDerivedCategory.map_isZero h⟩

/-- Reflection of isomorphisms follows from the actual distinguished cone
triangle and the preceding zero-object detection theorem. -/
theorem exactDerived_isIso_of_isIso_map {Y Z : DerivedCategory A}
    (f : Y ⟶ Z) [IsIso (F.mapDerivedCategory.map f)] : IsIso f := by
  obtain ⟨K, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hmap : F.mapDerivedCategory.mapTriangle.obj T ∈ distTriang (DerivedCategory B) :=
    F.mapDerivedCategory.map_distinguished T hT
  have hK : IsZero (F.mapDerivedCategory.obj K) :=
    Triangle.isZero₃_of_isIso₁ _ hmap (by
      change IsIso (F.mapDerivedCategory.map f)
      infer_instance)
  exact (Triangle.isZero₃_iff_isIso₁ T hT).mp
    (exactDerived_reflects_isZero F K hK)

/-- This declaration supplies a conservativity instance only after all
faithfulness and exactness hypotheses on the original functor are proved. -/
def exactDerivedReflectsIsomorphisms : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects f _ := exactDerived_isIso_of_isIso_map F f

end ToricPower

end
