module

public import Papers.GraphicalZonotopes.PathTight
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

instance graph_decidableAdj (n : ℕ) : DecidableRel (graph n).Adj := by
  dsimp [graph]
  infer_instance

theorem clique_card_le_four {n : ℕ} {C : Finset (Fin n)}
    (hcl : (graph n).IsClique C) : C.card ≤ 4 := by
  by_cases hc : 2 ≤ C.card
  · obtain ⟨i,T,hT,hbound,rfl⟩ := clique_window_classification hc
      (fun u hu v hv huv => hcl hu hv huv)
    rw [window_card T hbound]
    simp only [masks, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · omega

theorem graph_cliqueFree_five (n : ℕ) : (graph n).CliqueFree 5 := by
  intro C hC
  have h := clique_card_le_four hC.isClique
  rw [hC.card_eq] at h
  omega

abbrev EdgeIndex (n : ℕ) := Fin (n-1) ⊕ (Fin (n-2) ⊕ Fin (n-3))

def indexedEdge (n : ℕ) : EdgeIndex n → Finset (Fin n)
  | Sum.inl i => window n i.val {0,1}
  | Sum.inr (Sum.inl i) => window n i.val {0,2}
  | Sum.inr (Sum.inr i) => window n i.val {0,3}

theorem indexedEdge_mem (n : ℕ) (i : EdgeIndex n) : indexedEdge n i ∈ edgeFamily (graph n) := by
  rw [mem_edgeFamily]
  rcases i with i | i | i
  all_goals
    refine ⟨?_, ?_⟩
    · rw [indexedEdge, window_card _ (by
        intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
      norm_num
    · apply window_clique
      intro k hk
      simp only [mem_insert, mem_singleton] at hk ⊢
      tauto

theorem indexedEdge_injective (n : ℕ) : Function.Injective (indexedEdge n) := by
  intro i j he
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals
    dsimp [indexedEdge] at he
    have h := (window_eq_iff (by simp) (by simp)
      (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)
      (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)).mp he
    first
    | have hval : i = j := Fin.ext h.1
      subst j
      rfl
    | have hbad := h.2
      exfalso
      revert hbad
      decide

theorem indexedEdge_surjective (n : ℕ) {C : Finset (Fin n)}
    (hC : C ∈ edgeFamily (graph n)) : ∃ i, indexedEdge n i = C := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hC
  obtain ⟨i,T,hT,hbound,rfl⟩ := clique_window_classification (by omega) hcl
  have hcard := window_card T hbound
  simp only [masks, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := hbound 1 (by simp)
    exact ⟨Sum.inl ⟨i,by omega⟩,rfl⟩
  · have h := hbound 2 (by simp)
    exact ⟨Sum.inr (Sum.inl ⟨i,by omega⟩),rfl⟩
  · have h := hbound 3 (by simp)
    exact ⟨Sum.inr (Sum.inr ⟨i,by omega⟩),rfl⟩
  all_goals norm_num at hcard; omega

theorem edgeFamily_card (n : ℕ) :
    (edgeFamily (graph n)).card = (n-1)+(n-2)+(n-3) := by
  let f : EdgeIndex n → {C : Finset (Fin n) // C ∈ edgeFamily (graph n)} :=
    fun i => ⟨indexedEdge n i,indexedEdge_mem n i⟩
  have hfinj : Function.Injective f := by
    intro i j he
    exact indexedEdge_injective n (congrArg Subtype.val he)
  have hfsurj : Function.Surjective f := by
    intro C
    obtain ⟨i,hi⟩ := indexedEdge_surjective n C.2
    exact ⟨i,Subtype.ext hi⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩)
  simpa only [Fintype.card_coe, EdgeIndex, Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h.symm

theorem graph_edge_count {n : ℕ} (hn : 4 ≤ n) :
    (edgeFamily (graph n)).card = 3*n-6 := by
  rw [edgeFamily_card]
  omega

abbrev NeighborIndex {n : ℕ} (u : Fin n) :=
  Fin (min u.val 3) ⊕ Fin (min (n-1-u.val) 3)

def indexedNeighbor {n : ℕ} (u : Fin n) : NeighborIndex u → Fin n
  | Sum.inl i => ⟨u.val-(i.val+1),by have h := u.isLt; omega⟩
  | Sum.inr i => ⟨u.val+i.val+1,by have h := u.isLt; omega⟩

theorem indexedNeighbor_adj {n : ℕ} (u : Fin n) (i : NeighborIndex u) :
    (graph n).Adj u (indexedNeighbor u i) := by
  rcases i with i | i
  all_goals
    change u ≠ _ ∧ u.val ≤ _ + 3 ∧ _ ≤ u.val + 3
    dsimp only [indexedNeighbor, Fin.val_mk]
    refine ⟨?_,by omega,by omega⟩
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_mk] at h
    omega

theorem indexedNeighbor_injective {n : ℕ} (u : Fin n) :
    Function.Injective (indexedNeighbor u) := by
  intro i j he
  have hv := congrArg Fin.val he
  rcases i with i | i <;> rcases j with j | j
  all_goals
    dsimp [indexedNeighbor] at hv
    first
    | have h : i = j := Fin.ext (by omega)
      subst j
      rfl
    | omega

theorem indexedNeighbor_surjective {n : ℕ} (u v : Fin n)
    (hadj : (graph n).Adj u v) : ∃ i, indexedNeighbor u i = v := by
  obtain ⟨hne,hlo,hhi⟩ := hadj
  have hval : u.val ≠ v.val := by intro h; exact hne (Fin.ext h)
  by_cases hlt : v.val < u.val
  · refine ⟨Sum.inl ⟨u.val-v.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [indexedNeighbor]
    omega
  · refine ⟨Sum.inr ⟨v.val-u.val-1,by have h := v.isLt; omega⟩,?_⟩
    apply Fin.ext
    dsimp [indexedNeighbor]
    omega

theorem graph_degree {n : ℕ} (u : Fin n) :
    (graph n).degree u = min u.val 3 + min (n-1-u.val) 3 := by
  let f : NeighborIndex u → (graph n).neighborSet u :=
    fun i => ⟨indexedNeighbor u i,indexedNeighbor_adj u i⟩
  have hfinj : Function.Injective f := by
    intro i j he
    exact indexedNeighbor_injective u (congrArg Subtype.val he)
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨i,hi⟩ := indexedNeighbor_surjective u v.1 v.2
    exact ⟨i,Subtype.ext hi⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree] at h
  simpa [NeighborIndex] using h.symm

theorem graph_maxDegree {n : ℕ} (hn : 4 ≤ n) :
    (graph n).maxDegree = min (n-1) 6 := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro u
    rw [graph_degree]
    have h := u.isLt
    omega
  · have h := (graph n).degree_le_maxDegree (⟨3,by omega⟩ : Fin n)
    rw [graph_degree] at h
    simp only [Fin.val_mk] at h
    convert h using 1 <;> omega

end Path
end GraphicalZonotopes
