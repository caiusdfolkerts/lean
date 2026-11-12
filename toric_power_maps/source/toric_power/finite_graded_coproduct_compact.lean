module

public import ToricPower.CoproductProjectorMap
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Compactness of finitely supported graded objects

Only finitely many source grades are nonzero. A common finite support
for the component maps is assembled with the canonical coproduct
projector. The target grading and the coproduct family are unrestricted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{v} C]

theorem finiteGraded_coproductCompact (P : Discrete ℤ ⥤ C)
    (grades : Finset ℤ)
    (outside : ∀ q, q ∉ grades → IsZero (P.obj ⟨q⟩))
    (compact : ∀ q ∈ grades, CoproductCompact.{u,v,v} (P.obj ⟨q⟩)) :
    CoproductCompact P := by
  classical
  apply coproductCompact_iff_projector.mpr
  intro I family f
  let ev (q : ℤ) := (evaluation (Discrete ℤ) C).obj ⟨q⟩
  let components (q : ℤ) :=
    (ev q).map f ≫ (PreservesCoproduct.iso (ev q) family).hom
  have support (q : grades) : ∃ s : Finset I,
      components q ≫ finiteCoproductProjector (fun i => (ev q).obj (family i)) s =
        components q :=
    (coproductCompact_iff_projector.mp (compact q q.property)) I _ (components q)
  choose supports supported using support
  let common := Finset.univ.biUnion supports
  refine ⟨common,?_⟩
  apply NatTrans.ext
  funext q
  by_cases inside : q.as ∈ grades
  · exact support_of_mapped_support (ev q.as) family f common
      (finiteSupport_mono _ (components q.as)
        (Finset.subset_biUnion_of_mem supports (Finset.mem_univ (⟨q.as,inside⟩ : grades)))
        (supported ⟨q.as,inside⟩))
  · exact (outside q.as inside).eq_of_src _ _

end ToricPower.CompactExtraction

end
