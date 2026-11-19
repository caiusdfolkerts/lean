module

public import Papers.GraphicalZonotopes.PathDimension
public import Papers.GraphicalZonotopes.ExposedSegments

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset

theorem delta_swap {V : Type*} [Fintype V] [DecidableEq V]
    (f : SetFunction V) (u v : V) (S : Finset V) :
    delta f u v S = delta f v u S := by
  unfold delta
  rw [insert_comm u v]
  ring

/-- All three permitted edge lengths have a positive slack, including the
boundary positions of the path. -/
theorem edge_positive_slack {n : ℕ} (hn : 4 ≤ n) {u v : Fin n}
    (hadj : (graph n).Adj u v) :
    ∃ S : Finset (Fin n), u ∉ S ∧ v ∉ S ∧ delta (setFunction n) u v S = 1 := by
  suffices h : ∀ (u v : Fin n), u < v → v.val ≤ u.val+3 →
      ∃ S : Finset (Fin n), u ∉ S ∧ v ∉ S ∧ delta (setFunction n) u v S = 1 by
    rcases lt_or_gt_of_ne hadj.1 with huv | hvu
    · exact h u v huv hadj.2.2
    · obtain ⟨S,hv,hu,hδ⟩ := h v u hvu hadj.2.1
      exact ⟨S,hu,hv,(delta_swap _ _ _ _).trans hδ⟩
  intro u v huv hdist
  have hlt : u.val < v.val := huv
  by_cases h1 : v.val = u.val+1
  · have hi : u.val < n-1 := by omega
    obtain ⟨S,hu,hv,hδ⟩ := consecutive_positive_slack hn (⟨u.val,hi⟩ : Fin (n-1))
    have hu' : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
    have hv' : (⟨u.val+1, by omega⟩ : Fin n) = v := Fin.ext h1.symm
    refine ⟨S, ?_, ?_, ?_⟩
    · simpa only [hu'] using hu
    · simpa only [hv'] using hv
    · simpa only [hu',hv'] using hδ
  · by_cases h2 : v.val = u.val+2
    · let w : Fin n := ⟨u.val+1,by omega⟩
      have hu : u ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      have hv : v ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      refine ⟨{w},hu,hv,?_⟩
      rw [delta_formula huv hu hv]
      have h1z : (v.val : ℤ) ≠ (u.val : ℤ)+1 := by omega
      have h2z : (v.val : ℤ) = (u.val : ℤ)+2 := by omega
      rw [if_neg h1z,if_pos h2z]
      have ha : integerBit {w} ((u.val : ℤ)+1) = 1 := by simp [w]
      have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      have hc : integerBit {w} ((u.val : ℤ)+3) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      rw [ha,hb,hc]
      norm_num
    · have h3 : v.val = u.val+3 := by omega
      let w : Fin n := ⟨u.val+2,by omega⟩
      have hu : u ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      have hv : v ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      refine ⟨{w},hu,hv,?_⟩
      rw [delta_formula huv hu hv]
      have h1z : (v.val : ℤ) ≠ (u.val : ℤ)+1 := by omega
      have h2z : (v.val : ℤ) ≠ (u.val : ℤ)+2 := by omega
      have h3z : (v.val : ℤ) = (u.val : ℤ)+3 := by omega
      rw [if_neg h1z,if_neg h2z,if_pos h3z]
      have ha : integerBit {w} ((u.val : ℤ)+2) = 1 := by simp [w]
      have hb : integerBit {w} ((u.val : ℤ)+1) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      rw [ha,hb]
      norm_num

/-- Every edge of the path cube is realized by a genuine exposed edge of Q_n. -/
theorem graph_edge_is_actual {n : ℕ} (hn : 4 ≤ n) {u v : Fin n}
    (hadj : (graph n).Adj u v) : ActualRootEdge (polytope n) u v := by
  obtain ⟨S,hu,hv,hδ⟩ := edge_positive_slack hn hadj
  exact exposedSegment_of_positive_delta (setFunction_normalized n).1
    (setFunction_supermodular n) hadj.1 hu hv (by rw [hδ]; norm_num)

end Path
end GraphicalZonotopes
