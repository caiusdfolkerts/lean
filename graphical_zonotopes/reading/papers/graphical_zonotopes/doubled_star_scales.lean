module

public import Papers.GraphicalZonotopes.DoubledConnectivity

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_four_clique_containing_three (hI : 4≤Fintype.card I)
    (a b c : I×Fin 2) (hab : a.1≠b.1) (hac : a.1≠c.1) (hbc : b.1≠c.1) :
    ∃ C : Finset (I×Fin 2),C.card=4 ∧ (graph I).IsClique C ∧ a∈C ∧ b∈C ∧ c∈C := by
  obtain ⟨T,hST,hTU,hT⟩ := exists_subsuperset_card_eq
    (subset_univ ({a.1,b.1,c.1} : Finset I))
    (show ({a.1,b.1,c.1} : Finset I).card≤4 by
      have h : ({a.1,b.1,c.1} : Finset I).card≤3 := card_le_three
      omega)
    (show 4≤(univ : Finset I).card by simpa using hI)
  let bits : I → Fin 2 := fun i => if i=a.1 then a.2 else if i=b.1 then b.2
    else if i=c.1 then c.2 else 0
  refine ⟨selectedClique T bits,by simpa using hT,selectedClique_isClique T bits,?_,?_,?_⟩
  · simp [bits,hST (by simp : a.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hab,hST (by simp : b.1∈({a.1,b.1,c.1} : Finset I))]
  · simp [bits,Ne.symm hac,Ne.symm hbc,
      hST (by simp : c.1∈({a.1,b.1,c.1} : Finset I))]

abbrev AtVertex (a : I×Fin 2) := {v : I×Fin 2 // (graph I).Adj a v}

theorem exists_star_vertex (hI : 2≤Fintype.card I) (a : I×Fin 2) : Nonempty (AtVertex a) := by
  obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a.1} : Finset I).card<(univ : Finset I).card by simp only [card_singleton,card_univ]; omega)
  have hia : i≠a.1 := by simpa using hn
  exact ⟨⟨(i,0),Ne.symm hia⟩⟩

/-- Every locally determined scale on an edge at one fixed vertex is the
same, using only nonzero four-clique coefficients and arbitrary r≥4. -/
theorem star_scales_constant (hI : 4≤Fintype.card I) (a : I×Fin 2)
    (z f : SetFunction (I×Fin 2))
    (hnon : ∀ C : Finset (I×Fin 2),C.card=4 → (graph I).IsClique C → mobius z C≠0)
    (scale : AtVertex a → ℝ)
    (hscale : ∀ v : AtVertex a,∀ S : Finset (I×Fin 2),a∉S → v.1∉S →
      delta f a v.1 S=scale v*delta z a v.1 S) :
    ∃ t : ℝ,∀ v : AtVertex a,scale v=t := by
  letI := exists_star_vertex (by omega : 2≤Fintype.card I) a
  obtain ⟨v₀⟩ := ‹Nonempty (AtVertex a)›
  have hdiff (v w : AtVertex a) (hvw : v.1.1≠w.1.1) : scale v=scale w := by
    obtain ⟨C,hcard,hC,ha,hv,hw⟩ :=
      exists_four_clique_containing_three hI a v.1 w.1 v.2 w.2 hvw
    have hv' := mobius_scale_of_delta_scale ((graph I).ne_of_adj v.2)
      (scale v) (hscale v) ha hv
    have hw' := mobius_scale_of_delta_scale ((graph I).ne_of_adj w.2)
      (scale w) (hscale w) ha hw
    exact mul_right_cancel₀ (hnon C hcard hC) (hv'.symm.trans hw')
  refine ⟨scale v₀,?_⟩
  intro v
  by_cases hparts : v.1.1≠v₀.1.1
  · exact hdiff v v₀ hparts
  · obtain ⟨i,hi,hn⟩ := exists_mem_notMem_of_card_lt_card
      (show ({a.1,v.1.1} : Finset I).card<(univ : Finset I).card by
        have h : ({a.1,v.1.1} : Finset I).card≤2 := card_le_two
        simpa only [card_univ] using (lt_of_le_of_lt h (by omega : 2<Fintype.card I)))
    have hn' : i≠a.1 ∧ i≠v.1.1 := by simpa using hn
    let w : AtVertex a := ⟨(i,0),Ne.symm hn'.1⟩
    have hp : v.1.1=v₀.1.1 := not_not.mp hparts
    exact (hdiff v w (Ne.symm hn'.2)).trans (hdiff w v₀ (by simpa [w,← hp] using hn'.2))

end DoubledParts
end GraphicalZonotopes
