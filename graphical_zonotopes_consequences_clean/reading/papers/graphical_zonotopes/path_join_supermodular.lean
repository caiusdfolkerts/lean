module

public import Papers.GraphicalZonotopes.PathJoinSpokeBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem delta_swap {n : ℕ} (f : SetFunction (Vertex n)) (u v : Vertex n)
    (S : Finset (Vertex n)) : delta f u v S=delta f v u S := by
  unfold delta
  rw [insert_comm]
  ring

theorem dilation_ge_one (n : ℕ) : (1 : ℝ)≤((n+2)/2 : ℕ) := by
  have h : 1≤(n+2)/2 := by omega
  exact_mod_cast h

theorem delta_private_bounds {n : ℕ} (i j : Fin (n+2)) (hij : i≠j)
    (S : Finset (Vertex n)) (hi : vertex i∉S) (hj : vertex j∉S) :
    0≤delta (setFunction n) (vertex i) (vertex j) S ∧
      delta (setFunction n) (vertex i) (vertex j) S≤1 := by
  by_cases hadj : (graph n).Adj (vertex i) (vertex j)
  · rcases (graph_vertices i j).mp hadj with h | h
    · let k : Fin (n+1) := ⟨i.val,by omega⟩
      have hk0 : k.castSucc=i := Fin.ext rfl
      have hk1 : k.succ=j := Fin.ext h
      rw [←hk0] at hi ⊢
      rw [←hk1] at hj ⊢
      rcases delta_path_boolean k S hi hj with h | h <;> rw [h] <;> norm_num
    · let k : Fin (n+1) := ⟨j.val,by omega⟩
      have hk0 : k.castSucc=j := Fin.ext rfl
      have hk1 : k.succ=i := Fin.ext h
      rw [delta_swap]
      rw [←hk0] at hj ⊢
      rw [←hk1] at hi ⊢
      rcases delta_path_boolean k S hj hi with h | h <;> rw [h] <;> norm_num
  · rw [graphical n _ _ (by simpa using hij) hadj S hi hj]
    norm_num

theorem slack_bounds {n : ℕ} (u v : Vertex n) (huv : u≠v)
    (S : Finset (Vertex n)) (hu : u∉S) (hv : v∉S) :
    0≤delta (setFunction n) u v S ∧
      delta (setFunction n) u v S≤((n+2)/2 : ℕ) := by
  have hbound : ∀ x : ℝ,0≤x ∧ x≤1 → 0≤x ∧ x≤((n+2)/2 : ℕ) :=
    fun x hx => ⟨hx.1,hx.2.trans (dilation_ge_one n)⟩
  rcases vertex_cases u with rfl | rfl | ⟨i,rfl⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact (huv rfl).elim
    · exact delta_hub_bounds S hu hv
    · exact hbound _ (delta_a_bounds j S hu hv)
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · rw [delta_swap]; exact delta_hub_bounds S hv hu
    · exact (huv rfl).elim
    · exact hbound _ (delta_b_bounds j S hu hv)
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · rw [delta_swap]; exact hbound _ (delta_a_bounds i S hv hu)
    · rw [delta_swap]; exact hbound _ (delta_b_bounds i S hv hu)
    · exact hbound _ (delta_private_bounds i j (by simpa using huv) S hu hv)

theorem supermodular (n : ℕ) : Supermodular (setFunction n) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  exact (slack_bounds u v huv S hu hv).1

@[simp] theorem neighborBit_empty {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    neighborBit i j ∅=0 := by simp [neighborBit,bit]

@[simp] theorem coloredNeighbor_empty {n : ℕ} (p : ℕ) (i : Fin (n+2)) :
    coloredNeighbor p i ∅=0 := by simp [coloredNeighbor]

theorem delta_a_empty {n : ℕ} (i : Fin (n+2)) :
    delta (setFunction n) (hubA n) (vertex i) ∅=1 := by
  rw [delta_a_colored i ∅ (notMem_empty _) (notMem_empty _)]
  simp [bit]

theorem function_ne_zero (n : ℕ) : setFunction n≠0 := by
  intro h
  have he := delta_a_empty (0 : Fin (n+2))
  rw [h] at he
  norm_num [delta] at he

end GraphicalZonotopes.PathJoin
