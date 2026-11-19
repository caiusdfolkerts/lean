module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# The isomorphism locus of a homological comparison

A natural comparison between homological functors is an isomorphism
on a strictly full triangulated subcategory, provided all shifts are
included. The proof applies the actual five lemma to the five adjacent
terms of a distinguished triangle. This is the finite extension step
needed to pass from comparisons on sheaves to bounded complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ComposableArrows
open scoped ZeroObject

namespace ToricPower

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (H G : C ⥤ A) [H.IsHomological] [G.IsHomological]

/-- The literal five-term segment surrounding the middle object. -/
def homologicalComparisonSegment (T : Triangle C) : ComposableArrows A 4 :=
  mk₄ (H.map T.invRotate.mor₁) (H.map T.mor₁) (H.map T.mor₂) (H.map T.mor₃)

theorem homologicalComparisonSegment_exact (T : Triangle C) (hT : T ∈ distTriang C) :
    (homologicalComparisonSegment H T).Exact :=
  exact_of_δ₀
    (H.map_distinguished_exact T.invRotate (inv_rot_of_distTriang T hT)).exact_toComposableArrows
    (exact_of_δ₀ (H.map_distinguished_exact T hT).exact_toComposableArrows
      (H.map_distinguished_exact T.rotate (rot_of_distTriang T hT)).exact_toComposableArrows)

/-- Naturality supplies the actual commuting five-term diagram. -/
def homologicalComparisonSegmentMap (α : H ⟶ G) (T : Triangle C) :
    homologicalComparisonSegment H T ⟶ homologicalComparisonSegment G T :=
  homMk₄ (α.app T.invRotate.obj₁) (α.app T.obj₁) (α.app T.obj₂)
    (α.app T.obj₃) (α.app (T.obj₁⟦(1 : ℤ)⟧))
    (α.naturality T.invRotate.mor₁) (α.naturality T.mor₁)
    (α.naturality T.mor₂) (α.naturality T.mor₃)

/-- The five lemma proves the comparison on the extension object. -/
theorem homologicalComparison_isIso_middle (α : H ⟶ G)
    (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (α.app T.invRotate.obj₁)] [IsIso (α.app T.obj₁)]
    [IsIso (α.app T.obj₃)] [IsIso (α.app (T.obj₁⟦(1 : ℤ)⟧))] :
    IsIso (α.app T.obj₂) :=
  CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (homologicalComparisonSegment_exact H T hT)
    (homologicalComparisonSegment_exact G T hT)
    (homologicalComparisonSegmentMap H G α T)
    (by change Epi (α.app T.invRotate.obj₁); infer_instance)
    (by change IsIso (α.app T.obj₁); infer_instance)
    (by change IsIso (α.app T.obj₃); infer_instance)
    (by change Mono (α.app (T.obj₁⟦(1 : ℤ)⟧)); infer_instance)

/-- Isomorphisms in every shift, with no restriction on the object. -/
def homologicalComparisonLocus (α : H ⟶ G) : ObjectProperty C :=
  fun X => ∀ n : ℤ, IsIso (α.app (X⟦n⟧))

instance homologicalComparisonLocus_isoClosed (α : H ⟶ G) :
    (homologicalComparisonLocus H G α).IsClosedUnderIsomorphisms where
  of_iso e hX n :=
    (NatTrans.isIso_app_iff_of_iso α ((shiftFunctor C n).mapIso e)).mp (hX n)

instance homologicalComparisonLocus_shiftStable (α : H ⟶ G) :
    (homologicalComparisonLocus H G α).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun X hX b =>
    (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorAdd C a b).app X)).mp (hX (a+b))⟩

instance homologicalComparisonLocus_isTriangulated (α : H ⟶ G) :
    (homologicalComparisonLocus H G α).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun n => by
    have hz := (shiftFunctor C n).map_isZero (isZero_zero C)
    exact (H.map_isZero hz).isIso (G.map_isZero hz) _⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n => by
    let S := T⟦n⟧
    have hS : S ∈ distTriang C := Triangle.shift_distinguished T hT n
    haveI : IsIso (α.app S.obj₁) := h₁ n
    haveI : IsIso (α.app S.obj₃) := h₃ n
    haveI : IsIso (α.app S.invRotate.obj₁) :=
      (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorAdd C n (-1)).app T.obj₃)).mp
        (h₃ (n + -1))
    haveI : IsIso (α.app (S.obj₁⟦(1 : ℤ)⟧)) :=
      (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorAdd C n 1).app T.obj₁)).mp (h₁ (n+1))
    exact homologicalComparison_isIso_middle H G α S hS)

end ToricPower

end
