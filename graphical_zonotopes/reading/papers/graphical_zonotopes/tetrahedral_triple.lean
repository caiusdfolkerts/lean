module

public import Papers.GraphicalZonotopes.TetrahedralCardinality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected finite graph with at least three vertices contains a path of
length two with distinct endpoints. No acyclicity is assumed. -/
theorem preconnected_three_path (G : SimpleGraph V) (hG : G.Preconnected)
    (hcard : 3≤Fintype.card V) : ∃ a b c : V,a≠c ∧ G.Adj a b ∧ G.Adj b c := by
  classical
  by_contra hnot
  have hthin : ∀ a b c : V,G.Adj a b → G.Adj b c → a=c := by
    intro a b c hab hbc
    by_contra hne
    exact hnot ⟨a,b,c,hne,hab,hbc⟩
  have hne : (univ : Finset V).Nonempty := card_pos.mp (by simpa using (show 0<Fintype.card V by omega))
  obtain ⟨a,ha⟩ := hne
  obtain ⟨c,hc,hca⟩ := exists_mem_ne (s:=(univ : Finset V))
    (by simpa using (show 1<Fintype.card V by omega)) a
  obtain ⟨b,hab⟩ := (hG a c).nonempty_neighborSet_left (Ne.symm hca)
  have hall : ∀ x : V,x=a ∨ x=b := by
    intro x
    have hp := (SimpleGraph.reachable_iff_reflTransGen (G:=G) a x).mp (hG a x)
    induction hp with
    | refl => exact Or.inl rfl
    | @tail y z hp hyz ih =>
      rcases ih with hy | hy
      · subst y
        exact Or.inr (hthin b a z (G.adj_symm hab) hyz).symm
      · subst y
        exact Or.inl (hthin a b z hab hyz).symm
  have hsub : (univ : Finset V)⊆{a,b} := by intro x hx; simpa using hall x
  have hb := card_le_card hsub
  have hpair : ({a,b} : Finset V).card≤2 := card_le_two
  rw [card_univ] at hb
  omega

/-- Three successive tetrahedra contain a common pair: their two shared
triangles intersect inside the middle four-element set. -/
theorem tetrahedra_path_shared_pair {A B C : Finset V} (hB : B.card=4)
    (hAB : 3≤(A∩B).card) (hBC : 3≤(B∩C).card) :
    ∃ e : Finset V,e.card=2 ∧ e⊆A ∧ e⊆B ∧ e⊆C := by
  have hunion : (A∩B)∪(B∩C)⊆B := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact (mem_inter.mp h).2
    · exact (mem_inter.mp h).1
  have hub := card_le_card hunion
  have hsum := card_union_add_card_inter (A∩B) (B∩C)
  have hcommon : 2≤((A∩B)∩(B∩C)).card := by omega
  obtain ⟨e,he,hcard⟩ := exists_subset_card_eq hcommon
  refine ⟨e,hcard,?_,?_,?_⟩
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).1).1
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).1).2
  · intro v hv
    exact (mem_inter.mp (mem_inter.mp (he hv)).2).2

/-- The purely combinatorial step yielding the sharp integer dilation2:
a connected family of at least three tetrahedra has a pair contained in at
least three distinct members. -/
theorem connected_tetrahedra_pair_multiplicity (F : Finset (Finset V))
    (hfour : ∀ C∈F,C.card=4) (hconn : (tetrahedronGraph F).Preconnected)
    (hcard : 3≤F.card) :
    ∃ e : Finset V,e.card=2 ∧ 3≤(F.filter (fun C => e⊆C)).card := by
  classical
  have hc : 3≤Fintype.card {C : Finset V // C∈F} := by simpa using hcard
  obtain ⟨A,B,C,hAC,hAB,hBC⟩ := preconnected_three_path (tetrahedronGraph F) hconn hc
  obtain ⟨e,he,heA,heB,heC⟩ := tetrahedra_path_shared_pair
    (hfour B.val B.property) hAB.2 hBC.2
  refine ⟨e,he,?_⟩
  have hAB' : A.val≠B.val := fun he => hAB.1 (Subtype.ext he)
  have hAC' : A.val≠C.val := fun he => hAC (Subtype.ext he)
  have hBC' : B.val≠C.val := fun he => hBC.1 (Subtype.ext he)
  have hsub : ({A.val,B.val,C.val} : Finset (Finset V))⊆F.filter (fun D => e⊆D) := by
    intro D hD
    simp only [mem_insert,mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact mem_filter.mpr ⟨A.property,heA⟩
    · exact mem_filter.mpr ⟨B.property,heB⟩
    · exact mem_filter.mpr ⟨C.property,heC⟩
  have hcount := card_le_card hsub
  simpa [hAB',hAC',hBC'] using hcount

end GraphicalZonotopes
