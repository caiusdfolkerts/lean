module

public import Papers.GraphicalZonotopes.ThreeTreeCliques
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph induced on the common neighbors of an edge, with all other
ambient vertices isolated. This ambient form avoids deleting any zero weights
when the link is used as a Boolean interaction graph. -/
def edgeLink (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Adj u a ∧ G.Adj v a ∧ G.Adj u b ∧ G.Adj v b
  symm := ⟨fun a b h => ⟨G.adj_symm h.1,h.2.2.2.1,h.2.2.2.2,h.2.1,h.2.2.1⟩⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

@[simp] theorem edgeLink_comm (G : SimpleGraph V) (u v : V) :
    edgeLink G u v=edgeLink G v u := by
  ext a b
  simp only [edgeLink]
  tauto

theorem isAcyclic_cliqueGraph_of_card_le_two {C : Finset V} (hC : C.card≤2) :
    (cliqueGraph C).IsAcyclic := by
  by_cases htwo : C.card=2
  · obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp htwo
    have he : cliqueGraph ({a,b} : Finset V)=SimpleGraph.edge a b := by
      ext x y
      simp only [cliqueGraph,mem_insert,mem_singleton,SimpleGraph.edge_adj]
      constructor
      · rintro ⟨hxy,hx,hy⟩
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact False.elim (hxy rfl)
        · exact ⟨Or.inl ⟨rfl,rfl⟩,hxy⟩
        · exact ⟨Or.inr ⟨rfl,rfl⟩,hxy⟩
        · exact False.elim (hxy rfl)
      · rintro ⟨hxy,hne⟩
        rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hab,Ne.symm hab]
    rw [he]
    have h := SimpleGraph.IsAcyclic.sup_edge_of_not_reachable
      (G:=(⊥ : SimpleGraph V)) (u:=a) (v:=b)
      (by simpa only [SimpleGraph.reachable_bot] using hab) SimpleGraph.isAcyclic_bot
    simpa only [bot_sup_eq] using h
  · have hone : C.card≤1 := by omega
    have he : cliqueGraph C=(⊥ : SimpleGraph V) := by
      ext a b
      simp only [SimpleGraph.bot_adj,iff_false]
      intro h
      exact h.1 ((card_le_one.mp hone) a h.2.1 b h.2.2)
    rw [he]
    exact SimpleGraph.isAcyclic_bot

theorem adj_before_attachment {G : SimpleGraph V} {w a b : V} {T : Finset V}
    (ha : a≠w) (hb : b≠w) (hab : (G⊔attachmentStar w T).Adj a b) : G.Adj a b := by
  rcases hab with h | h
  · exact h
  · rcases h.2 with ⟨he,_⟩ | ⟨he,_⟩
    · exact False.elim (ha he)
    · exact False.elim (hb he)

theorem edgeLink_new_le_clique {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {w : V} (hw : w∉S) {T : Finset V} (hTS : T⊆S)
    (v : V) : edgeLink (G⊔attachmentStar w T) w v≤cliqueGraph (T.erase v) := by
  intro a b hab
  have ha := (attached_vertex_adj_iff h hw hTS a).mp hab.2.1
  have hb := (attached_vertex_adj_iff h hw hTS b).mp hab.2.2.2.1
  exact ⟨(G⊔attachmentStar w T).ne_of_adj hab.1,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1),ha⟩,
    mem_erase.mpr ⟨Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2),hb⟩⟩

theorem ThreeTreeOn.edgeLink_acyclic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u v : V} (huv : G.Adj u v) :
    (edgeLink G u v).IsAcyclic := by
  induction h generalizing u v with
  | tetrahedron C hC =>
    have hu := huv.2.1
    have hv := huv.2.2
    have hne := huv.1
    have hcard : ((C.erase u).erase v).card≤2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hv⟩),card_erase_of_mem hu,hC]
    apply (isAcyclic_cliqueGraph_of_card_le_two hcard).anti
    intro a b hab
    refine ⟨hab.1.1,?_,?_⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.1.1,
        mem_erase.mpr ⟨Ne.symm hab.2.1.1,hab.1.2.1⟩⟩
    · exact mem_erase.mpr ⟨Ne.symm hab.2.2.2.2.1,
        mem_erase.mpr ⟨Ne.symm hab.2.2.2.1.1,hab.1.2.2⟩⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    by_cases huw : u=w
    · subst u
      have hv := (attached_vertex_adj_iff h hw hTS v).mp huv
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase v) (by
        rw [card_erase_of_mem hv,hT])).anti
      exact edgeLink_new_le_clique h hw hTS v
    by_cases hvw : v=w
    · subst v
      rw [edgeLink_comm]
      have hu := (attached_vertex_adj_iff h hw hTS u).mp
        ((G⊔attachmentStar w T).adj_symm huv)
      apply (isAcyclic_cliqueGraph_of_card_le_two (C:=T.erase u) (by
        rw [card_erase_of_mem hu,hT])).anti
      exact edgeLink_new_le_clique h hw hTS u
    have hold := adj_before_attachment huw hvw huv
    have hi := ih (u:=u) (v:=v) hold
    by_cases hboth : u∈T ∧ v∈T
    · have hne : u≠v := G.ne_of_adj hold
      have hcard : ((T.erase u).erase v).card=1 := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hne,hboth.2⟩),
          card_erase_of_mem hboth.1,hT]
      obtain ⟨r,hr⟩ := card_eq_one.mp hcard
      have hrmem : r∈(T.erase u).erase v := by rw [hr]; simp
      have hrT := mem_of_mem_erase (mem_of_mem_erase hrmem)
      have hrw : r≠w := by intro he; subst r; exact hw (hTS hrT)
      have hnotreach : ¬(edgeLink G u v).Reachable w r := by
        intro hreach
        obtain ⟨x,hx⟩ := hreach.nonempty_neighborSet_left (Ne.symm hrw)
        exact hw (h.edges_supported hx.1).1
      have hforest := hi.sup_edge_of_not_reachable hnotreach
      apply hforest.anti
      intro a b hab
      by_cases haw : a=w
      · subst a
        right
        have hbT := (attached_vertex_adj_iff h hw hTS b).mp hab.1
        have hbu := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.1)
        have hbv := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.2.2)
        have hb : b∈(T.erase u).erase v := mem_erase.mpr ⟨hbv,mem_erase.mpr ⟨hbu,hbT⟩⟩
        rw [hr,mem_singleton] at hb
        subst b
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,Ne.symm hrw⟩
      by_cases hbw : b=w
      · subst b
        right
        have haT := (attached_vertex_adj_iff h hw hTS a).mp
          ((G⊔attachmentStar w T).adj_symm hab.1)
        have hau := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.1)
        have hav := Ne.symm ((G⊔attachmentStar w T).ne_of_adj hab.2.2.1)
        have ha : a∈(T.erase u).erase v := mem_erase.mpr ⟨hav,mem_erase.mpr ⟨hau,haT⟩⟩
        rw [hr,mem_singleton] at ha
        subst a
        exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hrw⟩
      exact Or.inl ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩
    · apply hi.anti
      intro a b hab
      have haw : a≠w := by
        intro he
        subst a
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.1)⟩
      have hbw : b≠w := by
        intro he
        subst b
        exact hboth ⟨(attached_vertex_adj_iff h hw hTS u).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.1),
          (attached_vertex_adj_iff h hw hTS v).mp
          ((G⊔attachmentStar w T).adj_symm hab.2.2.2.2)⟩
      exact ⟨adj_before_attachment haw hbw hab.1,
        adj_before_attachment huw haw hab.2.1,
        adj_before_attachment hvw haw hab.2.2.1,
        adj_before_attachment huw hbw hab.2.2.2.1,
        adj_before_attachment hvw hbw hab.2.2.2.2⟩

end GraphicalZonotopes
