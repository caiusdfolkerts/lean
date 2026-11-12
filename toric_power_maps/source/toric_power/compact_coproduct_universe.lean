module

public import ToricPower.CoproductFiniteFactorization

/-!
# Restricting compactness to small coproducts

The universe of the set indexing all maps from a generator can be larger
than the countable telescope index. This file transfers the explicit
finite-support condition across the actual coproduct reindexing by ULift.
No universe-specific compactness assumption is added to the final theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v w
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasCoproducts.{w} C] [HasCoproducts.{0} C]

theorem CoproductCompact.small {X : C} (compact : CoproductCompact.{u, v, w} X) :
    CoproductCompact.{u, v, 0} X := by
  classical
  intro I family f
  let equivalence : ULift.{w} I ≃ I := Equiv.ulift
  let lifted : ULift.{w} I → C := family ∘ equivalence
  let e : (∐ lifted) ≅ ∐ family := Sigma.reindex equivalence family
  obtain ⟨s, lift, factor⟩ := compact (ULift.{w} I) lifted (f ≫ e.inv)
  let t : Finset I := s.image ULift.down
  let collapse : (∐ fun i : s => lifted i) ⟶ ∐ fun i : t => family i :=
    Sigma.desc (fun i : s => Sigma.ι (fun j : t => family j)
      ⟨i.val.down, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩)
  have collapseEq : collapse ≫ finiteCoproductInclusion family t =
      finiteCoproductInclusion lifted s ≫ e.hom := by
    apply Sigma.hom_ext
    intro i
    simp only [collapse, finiteCoproductInclusion, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc]
    exact (Sigma.ι_reindex_hom equivalence family i.val).symm
  refine ⟨t, lift ≫ collapse, ?_⟩
  rw [Category.assoc, collapseEq, ← Category.assoc, factor, Category.assoc,
    e.inv_hom_id, Category.comp_id]

end ToricPower.CompactExtraction

end

