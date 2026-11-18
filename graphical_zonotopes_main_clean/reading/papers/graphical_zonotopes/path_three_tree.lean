module

public import Papers.GraphicalZonotopes.PathGraph
public import Papers.GraphicalZonotopes.TetrahedralGrowth

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset

def initialVertices (n k : ℕ) : Finset (Fin n) := univ.filter (fun v => v.val<k)

@[simp] theorem mem_initialVertices (n k : ℕ) (v : Fin n) :
    v∈initialVertices n k ↔ v.val<k := by simp [initialVertices]

theorem initialVertices_four (n : ℕ) :
    initialVertices n 4=window n 0 {0,1,2,3} := by
  ext v
  simp only [mem_initialVertices,mem_window,Nat.zero_le,Nat.sub_zero,true_and,
    mem_insert,mem_singleton]
  omega

theorem initialVertices_next {n k : ℕ} (hk : k<n) :
    initialVertices n (k+1)=insert (⟨k,hk⟩ : Fin n) (initialVertices n k) := by
  ext v
  simp only [mem_initialVertices,mem_insert,Fin.ext_iff]
  omega

/-- The actual path cube has a tetrahedral growth at every prefix: the next
vertex attaches to its three immediate predecessors. -/
theorem initialVertices_growth (n t : ℕ) (hbound : t+4≤n) :
    TetrahedralGrowth (graph n) (initialVertices n (t+4)) := by
  revert hbound
  induction t with
  | zero =>
    intro hbound
    rw [Nat.zero_add,initialVertices_four]
    apply TetrahedralGrowth.base
    · rw [window_card _ (by
        intro k hk
        simp only [mem_insert,mem_singleton] at hk
        omega)]
      decide
    · intro u hu v hv huv
      exact window_clique (subset_refl _) u hu v hv huv
  | succ t ih =>
    intro hbound
    have ht : t+4<n := by omega
    have hg := ih (by omega)
    let w : Fin n:=⟨t+4,ht⟩
    let T:=window n (t+1) {0,1,2}
    have hTcard : T.card=3 := by
      rw [window_card _ (by
        intro k hk
        simp only [mem_insert,mem_singleton] at hk
        omega)]
      decide
    have hTS : T⊆initialVertices n (t+4) := by
      intro v hv
      have hv' := (mem_window _ _ _ v).mp hv
      simp only [mem_insert,mem_singleton] at hv'
      apply (mem_initialVertices _ _ _).mpr
      omega
    have hTcl : (graph n).IsClique T := by
      intro u hu v hv huv
      exact window_clique (by simp) u hu v hv huv
    have hAdj : ∀ v∈T,(graph n).Adj w v := by
      intro v hv
      have hv' := (mem_window _ _ _ v).mp hv
      simp only [mem_insert,mem_singleton] at hv'
      refine ⟨?_,?_,?_⟩
      · intro he
        have he' := congrArg Fin.val he
        change t+4=v.val at he'
        omega
      · change t+4≤v.val+3
        omega
      · change v.val≤t+4+3
        omega
    have hg' := TetrahedralGrowth.attach hg w (by simp [w]) T hTcard hTS hTcl hAdj
    have he : t+1+4=(t+4)+1 := by omega
    simpa only [Nat.succ_eq_add_one,he,initialVertices_next ht,w] using hg'

/-- The equality witness used in Theorem9.1 really belongs to the class of
3-trees; this is proved independently of the lower dilation conclusion. -/
theorem graph_isThreeTree {n : ℕ} (hn : 4≤n) : IsThreeTree (graph n) := by
  have hg := initialVertices_growth n (n-4) (by omega)
  have he : n-4+4=n := by omega
  have hu : initialVertices n n=univ := by ext v; simp [v.isLt]
  rw [he,hu] at hg
  have hc := hg.edge_bound_and_equality.2
  simp only [inducedOn_univ,card_univ,Fintype.card_fin] at hc
  exact hc (graph_edge_count hn)

end Path
end GraphicalZonotopes
