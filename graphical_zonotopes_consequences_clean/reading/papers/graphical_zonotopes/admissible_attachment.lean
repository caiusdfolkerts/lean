module

public import Papers.GraphicalZonotopes.FourPartThreeTreeCounts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adding a tetrahedron at a triangle with a free incidence slot preserves
admissibility on every old and new triangle. -/
theorem ThreeTreeOn.admissible_attach {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hA : Admissible G) {u : V} (hu : u∉S)
    {T : Finset V} (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T)
    (hfree : triangleMultiplicity G T<3) : Admissible (G⊔attachmentStar u T) := by
  intro U hU hcU
  rw [triangleMultiplicity_after_attachment h hu hT hTS hcl]
  by_cases huU : u∈U
  · rw [h.triangleMultiplicity_eq_zero_of_outside hu huU]
    split_ifs <;> omega
  · have hold : G.IsClique U := clique_before_attachment huU hcU
    have hb := hA U hU hold
    by_cases hsub : U⊆insert u T
    · have hUT : U⊆T := by
        intro v hv
        have hm := hsub hv
        rcases mem_insert.mp hm with he | he
        · exact False.elim (huU (he ▸ hv))
        · exact he
      have heq : U=T := eq_of_subset_of_card_le hUT (by omega)
      subst U
      rw [if_pos hsub]
      omega
    · rw [if_neg hsub]
      omega

theorem proper_attachment {c : V → Fin 4} {G : SimpleGraph V}
    (hc : FourPartThreeTreeCounts.Proper c G) {u : V} {T : Finset V}
    (havoid : FourPartThreeTreeCounts.Avoids c (c u) T) :
    FourPartThreeTreeCounts.Proper c (G⊔attachmentStar u T) := by
  intro v w h
  rcases h with h | h
  · exact hc v w h
  · rcases h.2 with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Ne.symm (havoid w hw)
    · exact havoid v hv

theorem sum_color_counts (S : Finset V) (c : V → Fin 4) :
    (∑ i : Fin 4,(S.filter (fun v => c v=i)).card)=S.card := by
  simpa using sum_card_fiberwise_eq_card_filter S (univ : Finset (Fin 4)) c

theorem color_count_insert (S : Finset V) (c : V → Fin 4) {u : V} (hu : u∉S)
    (i : Fin 4) : ((insert u S).filter (fun v => c v=i)).card=
      (S.filter (fun v => c v=i)).card+(if c u=i then 1 else 0) := by
  rw [filter_insert]
  split_ifs with hi
  · rw [card_insert_of_notMem (fun hm => hu (mem_filter.mp hm).1)]
  · simp

end GraphicalZonotopes
