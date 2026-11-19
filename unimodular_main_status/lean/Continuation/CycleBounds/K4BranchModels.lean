module

public import Unimodular.SeriesParallelGraphMinors
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Choose

@[expose] public section

/-! # Finite connected branch models give literal graph minors

This file supplies the graph-minor implication used in Proposition 6.8. Its
hypotheses are finite connected vertex sets and edges between them. The conclusion
uses the independently defined edge-deletion/edge-contraction relation.
-/

noncomputable section
open scoped BigOperators
open Set

namespace Unimodular.CycleBounds
attribute [local instance] Classical.propDecidable
open SeriesParallel SeriesParallel.IncidenceGraph

variable {V E : Type*}

/-- Undirected adjacency, with loops ignored. -/
def Adj (G : IncidenceGraph V E) (a b : V) : Prop :=
  a ≠ b ∧ ∃ e ∈ G.edges,
    (G.source e = a ∧ G.target e = b) ∨
    (G.source e = b ∧ G.target e = a)

/-- Reachability using only vertices of a specified finite branch set. -/
def ConnectedIn (G : IncidenceGraph V E) (S : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (fun x y ↦ x ∈ S ∧ y ∈ S ∧ Adj G x y) a b

theorem minor_trans {G H J : IncidenceGraph V E}
    (hJH : J.IsMinor H) (hHG : H.IsMinor G) : J.IsMinor G := by
  induction hJH with
  | refl => exact hHG
  | delete h D ih => exact .delete (ih hHG) D
  | contract h e he hne ih => exact .contract (ih hHG) e he hne

theorem adj_contract_of_ne (G : IncidenceGraph V E) (e : E) {x y : V}
    (hxy : Adj G x y)
    (hne : merge (G.source e) (G.target e) x ≠
      merge (G.source e) (G.target e) y) :
    Adj (G.contract e) (merge (G.source e) (G.target e) x)
      (merge (G.source e) (G.target e) y) := by
  classical
  obtain ⟨_, j, hj, hor⟩ := hxy
  have hje : j ≠ e := by
    rintro rfl
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [merge] at hne
  refine ⟨hne, j, ⟨hj, by simpa using hje⟩, ?_⟩
  rcases hor with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl ⟨congrArg (merge (G.source e) (G.target e)) hs,
      congrArg (merge (G.source e) (G.target e)) ht⟩
  · exact Or.inr ⟨congrArg (merge (G.source e) (G.target e)) hs,
      congrArg (merge (G.source e) (G.target e)) ht⟩

theorem connected_contract (G : IncidenceGraph V E) (e : E)
    (S : Finset V) {a b : V} (h : ConnectedIn G S a b) :
    ConnectedIn (G.contract e) (S.image (merge (G.source e) (G.target e)))
      (merge (G.source e) (G.target e) a) (merge (G.source e) (G.target e) b) := by
  classical
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih =>
    by_cases heq : merge (G.source e) (G.target e) y =
        merge (G.source e) (G.target e) z
    · exact heq ▸ ih
    · exact ih.tail ⟨Finset.mem_image.mpr ⟨y, hyz.1, rfl⟩,
        Finset.mem_image.mpr ⟨z, hyz.2.1, rfl⟩,
        adj_contract_of_ne G e hyz.2.2 heq⟩

/-- Four disjoint nonempty finite connected vertex sets, with an edge between
 every pair. A label function expresses disjointness and survives contractions. -/
structure K4BranchModel (G : IncidenceGraph V E) where
  branch : Option (Fin 3) → Finset V
  label : V → Option (Fin 3)
  nonempty : ∀ i, (branch i).Nonempty
  label_mem : ∀ i x, x ∈ branch i → label x = i
  connected : ∀ i a, a ∈ branch i → ∀ b, b ∈ branch i → ConnectedIn G (branch i) a b
  between : ∀ i j, i ≠ j → ∃ e ∈ G.edges,
    (G.source e ∈ branch i ∧ G.target e ∈ branch j) ∨
    (G.source e ∈ branch j ∧ G.target e ∈ branch i)

/-- Build a branch model from the usual pairwise-disjoint formulation. -/
def K4BranchModel.ofDisjoint {G : IncidenceGraph V E}
    (S : Option (Fin 3) → Finset V) (hne : ∀ i, (S i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hconn : ∀ i a, a ∈ S i → ∀ b, b ∈ S i → ConnectedIn G (S i) a b)
    (hedge : ∀ i j, i ≠ j → ∃ e ∈ G.edges,
      (G.source e ∈ S i ∧ G.target e ∈ S j) ∨
      (G.source e ∈ S j ∧ G.target e ∈ S i)) : K4BranchModel G where
  branch := S
  label x := if h : ∃ i, x ∈ S i then h.choose else none
  nonempty := hne
  label_mem i x hx := by
    have hh : ∃ i, x ∈ S i := ⟨i, hx⟩
    simp only [dif_pos hh]
    by_contra hni
    exact Finset.disjoint_left.mp (hdis _ i hni) hh.choose_spec hx
  connected := hconn
  between := hedge

theorem ConnectedIn.mono {G : IncidenceGraph V E} {S T : Finset V} {a b : V}
    (h : ConnectedIn G S a b) (hst : S ⊆ T) : ConnectedIn G T a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy ↦ ⟨hst hxy.1, hst hxy.2.1, hxy.2.2⟩) a b h

theorem Adj.symm {G : IncidenceGraph V E} {a b : V} (h : Adj G a b) : Adj G b a := by
  obtain ⟨hne, e, he, hor⟩ := h
  exact ⟨hne.symm, e, he, hor.symm⟩

theorem ConnectedIn.symm {G : IncidenceGraph V E} {S : Finset V} {a b : V}
    (h : ConnectedIn G S a b) : ConnectedIn G S b a := by
  induction h with
  | refl => exact .refl
  | @tail x y h hxy ih =>
    exact (Relation.ReflTransGen.single ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩).trans ih

namespace K4BranchModel

variable {G : IncidenceGraph V E} (B : K4BranchModel G)

def size : ℕ := ∑ i, (B.branch i).card

theorem merge_label (e : E) (i : Option (Fin 3))
    (hs : G.source e ∈ B.branch i) (ht : G.target e ∈ B.branch i) (x : V) :
    B.label (merge (G.source e) (G.target e) x) = B.label x := by
  classical
  by_cases hx : x = G.source e
  · subst x
    simp only [merge, if_pos rfl]
    exact (B.label_mem i _ ht).trans (B.label_mem i _ hs).symm
  · simp [merge, hx]

/-- Contract an internal branch edge; the remaining branch sets are its images. -/
def contract (e : E) (i : Option (Fin 3))
    (hs : G.source e ∈ B.branch i) (ht : G.target e ∈ B.branch i) :
    K4BranchModel (G.contract e) where
  branch j := (B.branch j).image (merge (G.source e) (G.target e))
  label := B.label
  nonempty j := (B.nonempty j).image _
  label_mem j x hx := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [B.merge_label e i hs ht]
    exact B.label_mem j y hy
  connected j a ha b hb := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact connected_contract G e (B.branch j) (B.connected j x hx y hy)
  between j k hjk := by
    obtain ⟨f, hf, hfk⟩ := B.between j k hjk
    have hfe : f ≠ e := by
      intro heq
      subst f
      rcases hfk with ⟨hj, hk⟩ | ⟨hk, hj⟩
      · exact hjk ((B.label_mem j _ hj).symm.trans
          ((B.label_mem i _ hs).trans
            ((B.label_mem i _ ht).symm.trans (B.label_mem k _ hk))))
      · exact hjk ((B.label_mem j _ hj).symm.trans
          ((B.label_mem i _ ht).trans
            ((B.label_mem i _ hs).symm.trans (B.label_mem k _ hk))))
    refine ⟨f, ⟨hf, by simpa using hfe⟩, ?_⟩
    rcases hfk with ⟨hj, hk⟩ | ⟨hk, hj⟩
    · exact Or.inl ⟨Finset.mem_image.mpr ⟨_, hj, rfl⟩,
        Finset.mem_image.mpr ⟨_, hk, rfl⟩⟩
    · exact Or.inr ⟨Finset.mem_image.mpr ⟨_, hk, rfl⟩,
        Finset.mem_image.mpr ⟨_, hj, rfl⟩⟩

theorem image_merge_eq_erase {S : Finset V} {a b : V} (hab : a ≠ b)
    (ha : a ∈ S) (hb : b ∈ S) : S.image (merge a b) = S.erase a := by
  classical
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases hya : y = a
    · subst y
      simp [merge, hab.symm, hb]
    · simp [merge, hya, hy]
  · intro hx
    obtain ⟨hxa, hxS⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨x, hxS, by simp [merge, hxa]⟩

theorem contract_size_lt (e : E) (i : Option (Fin 3))
    (hs : G.source e ∈ B.branch i) (ht : G.target e ∈ B.branch i)
    (hne : G.source e ≠ G.target e) : (B.contract e i hs ht).size < B.size := by
  classical
  unfold size
  apply Finset.sum_lt_sum
  · intro j _
    exact Finset.card_image_le
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    change ((B.branch i).image (merge (G.source e) (G.target e))).card < _
    rw [image_merge_eq_erase hne hs ht]
    exact Finset.card_erase_lt_of_mem hs

theorem exists_internal_edge (h : ∃ i, 1 < (B.branch i).card) :
    ∃ e ∈ G.edges, G.source e ≠ G.target e ∧
      ∃ i, G.source e ∈ B.branch i ∧ G.target e ∈ B.branch i := by
  classical
  obtain ⟨i, hi⟩ := h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
  obtain heq | ⟨c, hc, _⟩ := (B.connected i a ha b hb).cases_head
  · exact (hab heq).elim
  obtain ⟨hne, e, he, hor⟩ := hc.2.2
  refine ⟨e, he, ?_, i, ?_⟩
  · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact hne.symm
  · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hc.2.1⟩
    · exact ⟨hc.2.1, ha⟩

private theorem k4_endpoints_injective (i j : Fin 6)
    (h : (K4Network.source i = K4Network.source j ∧
        K4Network.target i = K4Network.target j) ∨
      (K4Network.source i = K4Network.target j ∧
        K4Network.target i = K4Network.source j)) : i = j := by
  fin_cases i <;> fin_cases j <;> norm_num [K4Network] at *

/-- Singleton branch sets already give a K4 restriction after deleting every
other edge. Edge labels are proved distinct from their unordered endpoints. -/
theorem hasK4Minor_of_singletons (h : ∀ i, (B.branch i).card ≤ 1) : G.HasK4Minor := by
  classical
  have hs : ∀ i, ∃ v, B.branch i = {v} := by
    intro i
    apply Finset.card_eq_one.mp
    have := (B.nonempty i).card_pos
    have := h i
    omega
  choose v hv using hs
  have hvi : Function.Injective v := by
    intro i j hij
    have hi : B.label (v i) = i := B.label_mem i _ (by rw [hv]; simp)
    have hj : B.label (v j) = j := B.label_mem j _ (by rw [hv]; simp)
    exact hi.symm.trans ((congrArg B.label hij).trans hj)
  have hedges : ∀ k : Fin 6, ∃ e ∈ G.edges,
      (G.source e = v (K4Network.source k) ∧ G.target e = v (K4Network.target k)) ∨
      (G.source e = v (K4Network.target k) ∧ G.target e = v (K4Network.source k)) := by
    intro k
    obtain ⟨e, he, hor⟩ := B.between _ _ (K4Network_loopless k)
    refine ⟨e, he, ?_⟩
    simpa only [hv, Finset.mem_singleton] using hor
  choose f hf hor using hedges
  have hfi : Function.Injective f := by
    intro i j hij
    apply k4_endpoints_injective
    rcases hor i with hi | hi <;> rcases hor j with hj | hj
    · exact Or.inl ⟨hvi (hi.1.symm.trans ((congrArg G.source hij).trans hj.1)),
        hvi (hi.2.symm.trans ((congrArg G.target hij).trans hj.2))⟩
    · exact Or.inr ⟨hvi (hi.1.symm.trans ((congrArg G.source hij).trans hj.1)),
        hvi (hi.2.symm.trans ((congrArg G.target hij).trans hj.2))⟩
    · exact Or.inr ⟨hvi (hi.2.symm.trans ((congrArg G.target hij).trans hj.2)),
        hvi (hi.1.symm.trans ((congrArg G.source hij).trans hj.1))⟩
    · exact Or.inl ⟨hvi (hi.2.symm.trans ((congrArg G.target hij).trans hj.2)),
        hvi (hi.1.symm.trans ((congrArg G.source hij).trans hj.1))⟩
  let H := G.delete (G.edges \ Set.range f)
  refine ⟨H, .delete (.refl G) _, ⟨⟨v, hvi⟩, ⟨f, hfi⟩, ?_, ?_⟩⟩
  · change G.edges \ (G.edges \ Set.range f) = Set.range f
    ext e
    constructor
    · rintro ⟨he, hnot⟩
      by_contra hn
      exact hnot ⟨he, hn⟩
    · rintro ⟨k, rfl⟩
      exact ⟨hf k, fun hh ↦ hh.2 ⟨k, rfl⟩⟩
  · exact hor

include B in
/-- A finite connected branch model gives a literal sequence of ordinary graph
edge deletions and nonloop edge contractions producing K4. -/
theorem hasK4Minor : G.HasK4Minor := by
  classical
  have main : ∀ n : ℕ, ∀ (G : IncidenceGraph V E) (B : K4BranchModel G),
      B.size = n → G.HasK4Minor := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    intro G B hn
    by_cases hsmall : ∀ i, (B.branch i).card ≤ 1
    · exact B.hasK4Minor_of_singletons hsmall
    · have hlarge : ∃ i, 1 < (B.branch i).card := by simpa only [not_forall, not_le] using hsmall
      obtain ⟨e, he, hne, i, hs, ht⟩ := B.exists_internal_edge hlarge
      obtain ⟨H, hH, hK⟩ := ih (B.contract e i hs ht).size
        (by simpa only [hn] using B.contract_size_lt e i hs ht hne)
        (G.contract e) (B.contract e i hs ht) rfl
      exact ⟨H, minor_trans hH (.contract (.refl G) e he hne), hK⟩
  exact main B.size G B rfl

end K4BranchModel
end Unimodular.CycleBounds
