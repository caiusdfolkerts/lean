module
public import graph_foundation.part014
public import shared_results.part020_homogeneous_weight_filtration

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomologySelectedEquiv -/
section

/-! # Selected homogeneous cycle classes under an actual algebra equivalence -/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.ParityDifferential

open IntegerFiltered.MultiplicativeFiltration

variable {K A B : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
  (D : ParityDifferential K A) (E : ParityDifferential K B)
  (e : A ≃ₐ[K] B) (hd : ∀ x,e (D.d x)=E.d (e x))
  (W : Submodule K A)

theorem selectedHomologyClasses_image :
    homologyEquiv D E e hd '' selectedHomologyClasses D W =
      selectedHomologyClasses E (W.map e.toLinearMap) := by
  ext u
  constructor
  · rintro ⟨v,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨cyclesEquiv D E e hd x,⟨x.val,hx,rfl⟩,
      (homologyEquiv_classMap D E e hd x).symm⟩
  · rintro ⟨y,⟨x,hx,he⟩,rfl⟩
    change e x = y.val at he
    have hdx : D.d x=0 := by
      apply e.injective
      rw [hd,he,show E.d y.val=0 from y.property,map_zero]
    refine ⟨D.classMap ⟨x,hdx⟩,⟨⟨x,hdx⟩,hx,rfl⟩,?_⟩
    rw [homologyEquiv_classMap]
    apply congrArg E.classMap
    exact Subtype.ext he

include hd in
theorem selected_generation_of_equiv
    (hgen : Algebra.adjoin K (selectedHomologyClasses E (W.map e.toLinearMap))=⊤) :
    Algebra.adjoin K (selectedHomologyClasses D W)=⊤ := by
  let H := homologyEquiv D E e hd
  let L := Algebra.adjoin K (selectedHomologyClasses D W)
  have htop : (⊤ : Subalgebra K E.Homology)≤L.map H.toAlgHom := by
    rw [← hgen,← selectedHomologyClasses_image D E e hd W]
    exact le_of_eq (Algebra.adjoin_image K H.toAlgHom _)
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := htop (show H x∈(⊤ : Subalgebra K E.Homology) from trivial)
  exact (H.injective he : y=x) ▸ hy

end FourPapers.ParityDifferential

end
end
end


end
