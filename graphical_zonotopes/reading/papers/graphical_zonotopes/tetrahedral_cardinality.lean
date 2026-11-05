module

public import Papers.GraphicalZonotopes.TetrahedralGrowth

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty triangle-connected family of four-element sets covers at most
three more vertices than it has members. The finite maximal-family argument
counts the actual selected sets, rather than a larger ambient clique family. -/
theorem connected_tetrahedra_union_card (F : Finset (Finset V))
    (hne : F.Nonempty) (hfour : ∀ C∈F,C.card=4)
    (hconn : (tetrahedronGraph F).Preconnected) :
    (F.biUnion id).card≤F.card+3 := by
  classical
  obtain ⟨C₀,hC₀⟩ := hne
  let candidates : Finset (Finset (Finset V)) := univ.filter
    (fun A => C₀∈A ∧ A⊆F ∧ (A.biUnion id).card≤A.card+3)
  have hbase : {C₀}∈candidates := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,by simp,?_,?_⟩
    · exact singleton_subset_iff.mpr hC₀
    · simp [hfour C₀ hC₀]
  obtain ⟨A,hA,hmax⟩ := candidates.exists_max_image Finset.card ⟨{C₀},hbase⟩
  obtain ⟨hC₀A,hAF,hcard⟩ := (mem_filter.mp hA).2
  have hclosed : ∀ C∈A,∀ D∈F,3≤(C∩D).card → D∈A := by
    intro C hC D hD hover
    by_contra hnot
    have hinter : 3≤(D∩A.biUnion id).card := by
      refine hover.trans (card_le_card ?_)
      intro v hv
      exact mem_inter.mpr ⟨(mem_inter.mp hv).2,
        mem_biUnion.mpr ⟨C,hC,(mem_inter.mp hv).1⟩⟩
    have hsum := card_union_add_card_inter D (A.biUnion id)
    have hDfour := hfour D hD
    have hcand : insert D A∈candidates := by
      apply mem_filter.mpr
      refine ⟨mem_univ _,mem_insert_of_mem hC₀A,insert_subset hD hAF,?_⟩
      rw [biUnion_insert,card_insert_of_notMem hnot]
      dsimp only [id_eq]
      omega
    have hmax' := hmax (insert D A) hcand
    rw [card_insert_of_notMem hnot] at hmax'
    omega
  have hall : ∀ C : {C : Finset V // C∈F},C.1∈A := by
    intro C
    have hp := (SimpleGraph.reachable_iff_reflTransGen
      (G:=tetrahedronGraph F) ⟨C₀,hC₀⟩ C).mp (hconn _ _)
    induction hp with
    | refl => exact hC₀A
    | @tail D E hp hDE ih => exact hclosed D.1 ih E.1 E.2 hDE.2
  have hFA : F⊆A := fun C hC => hall ⟨C,hC⟩
  have he : A=F := subset_antisymm hAF hFA
  simpa only [he] using hcard

end GraphicalZonotopes
