module

public import ToricPower.BoundedSingleGeneration

/-! # Exact images of bounded objects from the actual single-object cases -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace ToricPower

universe u v w u' v'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  (F : DerivedCategory A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (P : ObjectProperty D) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- The finite truncation induction uses actual exact triangles and
actual shift isomorphisms. It requires no termwise bounded representative. -/
theorem derivedBoundedProperty_of_singles
    (single : ∀ M : A, P (F.obj ((DerivedCategory.singleFunctor A 0).obj M)))
    (K : DerivedCategory A) (bounded : DerivedCategory.TStructure.t.bounded K) :
    P (F.obj K) := by
  apply prop_of_tBounded_of_prop_concentrated DerivedCategory.TStructure.t
    (P.inverseImage F) ?_ K bounded
  intro L n hge hle
  letI := hge
  letI := hle
  obtain ⟨M, ⟨e⟩⟩ := L.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  have shifted := P.le_shift (-n) _ (single M)
  exact P.prop_of_iso
    (((F.commShiftIso (-n)).app ((DerivedCategory.singleFunctor A 0).obj M)).symm ≪≫
      F.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M) ≪≫
      F.mapIso e.symm) shifted

end ToricPower
end
