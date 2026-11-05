module

public import Papers.GraphicalZonotopes.SparseFamilyGeometry
public import Papers.GraphicalZonotopes.TreewidthOperations

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset BooleanModule

def baseBags : Fin 6 → Finset (Fin 10) :=
  ![{0,1,2,3,4},{0,1,2,3,5},{0,1,2,3,6},
    {0,1,2,3,7},{0,1,2,3,8},{0,1,2,3,9}]

theorem baseBag_occurrence (v : Fin 10) :
    {i : Fin 6 | v ∈ baseBags i} = Set.univ ∨
      ∃ j : Fin 6, {i : Fin 6 | v ∈ baseBags i} = {j} := by
  fin_cases v
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · left; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨0,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨1,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨2,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨3,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨4,?_⟩; ext i; fin_cases i <;> simp [baseBags]
  · right; refine ⟨5,?_⟩; ext i; fin_cases i <;> simp [baseBags]

def base_decomposition : RootedTreeDecomposition DiamondGeometry.graph 4 ({0,1,6} : Finset (Fin 10)) where
  Index := Fin 6
  tree := SimpleGraph.pathGraph 6
  bag := baseBags
  root := 2
  isTree := SimpleGraph.isTree_pathGraph_add_one 5
  size := by decide +kernel
  cover := by decide +kernel
  edge := by decide +kernel
  occurrence := by
    intro v
    rcases baseBag_occurrence v with h | ⟨i,h⟩
    · rw [h]
      exact (SimpleGraph.induceUnivIso _).connected_iff.mpr
        (SimpleGraph.connected_pathGraph_add_one 5)
    · rw [h,SimpleGraph.induce_singleton_eq_top]
      letI : Nonempty ({i} : Set (Fin 6)) := ⟨⟨i,by simp⟩⟩
      exact SimpleGraph.connected_top
  boundary := by decide +kernel

def rooted_decomposition : (m : ℕ) →
    RootedTreeDecomposition (graph m) 4 ({first m,second m,tip m} : Finset (Vertex m))
  | 0 => base_decomposition
  | m+1 =>
    ((rooted_decomposition m).append (by rw [frame_card]; omega)).restrictBoundary (by
      intro x hx
      simp only [frame,first,second,tip,mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp)

theorem width_at_most_four (m : ℕ) : HasTreewidthAtMost (graph m) 4 :=
  (rooted_decomposition m).hasTreewidthAtMost

def coreEmbedding : Fin 6 ↪ Fin 10 where
  toFun := ![0,1,2,3,8,9]
  inj' := by decide +kernel

def coreGraph : SimpleGraph (Fin 6) := DiamondGeometry.graph.comap coreEmbedding

instance coreGraphDecidable : DecidableRel coreGraph.Adj := by
  unfold coreGraph
  infer_instance

/-- The induced six-vertex `K₂ * C₄` core has minimum degree four. -/
theorem core_minimum_degree : ∀ v : Fin 6, 4 ≤ coreGraph.degree v := by
  decide +kernel

theorem base_not_width_three : ¬HasTreewidthAtMost DiamondGeometry.graph 3 := by
  intro h
  have hc : HasTreewidthAtMost coreGraph 3 := h.comap coreEmbedding
  obtain ⟨v,hv⟩ := hc.exists_degree_le
  have hm := core_minimum_degree v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hv hm
  omega

def baseEmbedding : (m : ℕ) → Fin 10 ↪ Vertex m
  | 0 => Function.Embedding.refl _
  | m+1 => (baseEmbedding m).trans SingleVertexGraph.old

theorem graph_comap_base (m : ℕ) : (graph m).comap (baseEmbedding m) = DiamondGeometry.graph := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : (graph (m+1)).comap (baseEmbedding (m+1)) = (graph m).comap (baseEmbedding m) := rfl
    exact he.trans ih

theorem not_width_three (m : ℕ) : ¬HasTreewidthAtMost (graph m) 3 := by
  intro h
  have hb := h.comap (baseEmbedding m)
  rw [graph_comap_base] at hb
  exact base_not_width_three hb

end GraphicalZonotopes.SparseFamily
