module

public import ToricPower.CechSingular.RealizationEquivalence

/-! # Equality of full cover nerves retains their actual realizations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open ToricPower.NegativeSupportCech
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ClosedConvexNerveComparison

attribute [local instance] Classical.decEq

namespace ToricPower.NerveCongruence

variable {Index : Type}

def activeComplex (active : Index → Prop) (complex : PreAbstractSimplicialComplex Index)
    (vertices : ∀ i, ({i} : Finset Index) ∈ complex ↔ active i) :
    AbstractSimplicialComplex {i : Index // active i} where
  faces := {face | face.image Subtype.val ∈ complex}
  isRelLowerSet_faces := by
    intro face present
    have nonempty : face.Nonempty := by
      obtain ⟨i,hi⟩ := (complex.isRelLowerSet_faces present).1
      obtain ⟨j,hj,_⟩ := Finset.mem_image.mp hi
      exact ⟨j,hj⟩
    refine ⟨nonempty,?_⟩
    intro smaller contained smaller_nonempty
    exact complex.isRelLowerSet_faces.mem_of_le present
      (Finset.image_subset_image contained) (smaller_nonempty.image _)
  singleton_mem := by
    intro i
    change (Finset.image Subtype.val {i} : Finset Index) ∈ complex
    simpa only [Finset.image_singleton] using (vertices i.val).mpr i.property

theorem activeComplex_contractible_congr
    (active other : Index → Prop) (complex target : PreAbstractSimplicialComplex Index)
    (vertices : ∀ i, ({i} : Finset Index) ∈ complex ↔ active i)
    (otherVertices : ∀ i, ({i} : Finset Index) ∈ target ↔ other i)
    (sameActive : active = other) (sameComplex : complex = target) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeComplex active complex vertices)) ↔
      ContractibleSpace (AbstractSimplicialComplex.Realization
        (activeComplex other target otherVertices)) := by
  subst other target
  rfl

theorem patch_nonempty_iff_vertex {E : Type*} (patches : Index → Set E) (i : Index) :
    (patches i).Nonempty ↔ ({i} : Finset Index) ∈ coverNerve patches := by
  rw [mem_coverNerve_iff]
  simp only [Finset.singleton_nonempty,true_and,Finset.mem_singleton,forall_eq]
  rfl

theorem activeNerve_contractible_congr {E F : Type*}
    (patches : Index → Set E) (other : Index → Set F)
    (same : coverNerve patches = coverNerve other) :
    ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve patches)) ↔
      ContractibleSpace (AbstractSimplicialComplex.Realization (activeNerve other)) := by
  have sameActive : (fun i => (patches i).Nonempty) = (fun i => (other i).Nonempty) := by
    funext i
    apply propext
    rw [patch_nonempty_iff_vertex,patch_nonempty_iff_vertex,same]
  exact activeComplex_contractible_congr _ _ _ _
    (fun i => (patch_nonempty_iff_vertex patches i).symm)
    (fun i => (patch_nonempty_iff_vertex other i).symm) sameActive same

end ToricPower.NerveCongruence

end
