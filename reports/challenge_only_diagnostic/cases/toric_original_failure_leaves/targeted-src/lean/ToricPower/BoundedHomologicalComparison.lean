module

public import ToricPower.HomologicalComparisonClosure
public import ToricPower.BoundedSingleGeneration
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Comparisons on single sheaves extend to every bounded complex

This is finite truncation induction in the literal derived category.
Both covariant and contravariant homological comparisons are covered.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace ToricPower

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {A : Type*} [Category* A] [Abelian A]

/-- A comparison between covariant homological functors is invertible
on all bounded complexes if it is invertible on all single objects. -/
theorem homologicalComparison_isIso_of_bounded
    (H G : DerivedCategory C ⥤ A) [H.IsHomological] [G.IsHomological]
    (α : H ⟶ G)
    (hsingle : ∀ (X : C) (n : ℤ),
      IsIso (α.app ((DerivedCategory.singleFunctor C n).obj X)))
    (K : DerivedCategory C) (hK : (DerivedCategory.TStructure.t (C := C)).bounded K) :
    IsIso (α.app K) := by
  let P := homologicalComparisonLocus H G α
  have hP : P K := by
    apply prop_of_tBounded_of_prop_concentrated (DerivedCategory.TStructure.t (C := C)) P
    · intro L n hge hle
      letI := hge
      letI := hle
      obtain ⟨X, ⟨e⟩⟩ := L.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
      apply P.prop_of_iso e.symm
      intro p
      let es := ((DerivedCategory.singleFunctors C).shiftIso p (n-p) n (by omega)).app X
      exact (NatTrans.isIso_app_iff_of_iso α es).mpr (hsingle X (n-p))
    · exact hK
  exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorZero (DerivedCategory C) ℤ).app K)).mp
    (hP 0)

/-- The contravariant version uses the genuine opposite triangulated
category, whose integer shift reverses sign. -/
theorem homologicalComparison_isIso_of_bounded_op
    (H G : (DerivedCategory C)ᵒᵖ ⥤ A) [H.IsHomological] [G.IsHomological]
    (α : H ⟶ G)
    (hsingle : ∀ (X : C) (n : ℤ),
      IsIso (α.app (op ((DerivedCategory.singleFunctor C n).obj X))))
    (K : DerivedCategory C) (hK : (DerivedCategory.TStructure.t (C := C)).bounded K) :
    IsIso (α.app (op K)) := by
  let P := (homologicalComparisonLocus H G α).unop
  have hP : P K := by
    apply prop_of_tBounded_of_prop_concentrated (DerivedCategory.TStructure.t (C := C)) P
    · intro L n hge hle
      letI := hge
      letI := hle
      obtain ⟨X, ⟨e⟩⟩ := L.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
      apply P.prop_of_iso e.symm
      intro p
      change IsIso (α.app (op (((DerivedCategory.singleFunctor C n).obj X)⟦-p⟧)))
      let es := ((DerivedCategory.singleFunctors C).shiftIso (-p) (n+p) n (by omega)).app X
      exact (NatTrans.isIso_app_iff_of_iso α es.op).mp (hsingle X (n+p))
    · exact hK
  exact (NatTrans.isIso_app_iff_of_iso α
    ((shiftFunctorZero ((DerivedCategory C)ᵒᵖ) ℤ).app (op K))).mp (hP 0)

end ToricPower

end
