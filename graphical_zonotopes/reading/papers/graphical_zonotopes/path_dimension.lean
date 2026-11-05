module

public import Papers.GraphicalZonotopes.PathPolytope
public import Papers.GraphicalZonotopes.AffineDimension

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators Pointwise

@[simp] theorem integerBit_singleton {n : ℕ} (v : Fin n) (k : ℤ) :
    integerBit {v} k = if (v.val : ℤ) = k then 1 else 0 := by
  simp [integerBit]

/-- Each consecutive path edge has a positive slack, including the final edge. -/
theorem consecutive_positive_slack {n : ℕ} (hn : 4 ≤ n) (i : Fin (n-1)) :
    ∃ S : Finset (Fin n),
      (⟨i.val, by omega⟩ : Fin n) ∉ S ∧ (⟨i.val+1, by omega⟩ : Fin n) ∉ S ∧
      delta (setFunction n) ⟨i.val, by omega⟩ ⟨i.val+1, by omega⟩ S = 1 := by
  let u : Fin n := ⟨i.val, by omega⟩
  let v : Fin n := ⟨i.val+1, by omega⟩
  have huv : u < v := by
    change (i.val : ℕ) < i.val + 1
    omega
  by_cases hlast : i.val+2<n
  · let w : Fin n := ⟨i.val+2,hlast⟩
    have hu : u ∉ ({w} : Finset (Fin n)) := by simp [u,w,Fin.ext_iff]
    have hv : v ∉ ({w} : Finset (Fin n)) := by simp [v,w,Fin.ext_iff]
    refine ⟨{w},hu,hv,?_⟩
    rw [delta_formula huv hu hv]
    have hd : (v.val : ℤ) = u.val+1 := by simp [u,v]
    rw [if_pos hd]
    have ha : integerBit {w} ((u.val : ℤ)-2) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hc : integerBit {w} (u.val+2) = 1 := by simp [u,w]
    have hd : integerBit {w} (u.val+3) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    rw [ha,hb,hc,hd]
    norm_num
  · have hi2 : 2 ≤ i.val := by omega
    let w : Fin n := ⟨i.val-2,by omega⟩
    have hu : u ∉ ({w} : Finset (Fin n)) := by
      simp only [mem_singleton, Fin.ext_iff]
      dsimp [u,w]
      omega
    have hv : v ∉ ({w} : Finset (Fin n)) := by
      simp only [mem_singleton, Fin.ext_iff]
      dsimp [v,w]
      omega
    refine ⟨{w},hu,hv,?_⟩
    rw [delta_formula huv hu hv]
    have hd : (v.val : ℤ) = u.val+1 := by simp [u,v]
    rw [if_pos hd]
    have ha : integerBit {w} ((u.val : ℤ)-2) = 1 := by
      rw [integerBit_singleton, if_pos]
      dsimp [u,w]
      omega
    have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hc : integerBit {w} (u.val+2) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hd : integerBit {w} (u.val+3) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    rw [ha,hb,hc,hd]
    norm_num

/-- Full affine dimension is proved in the ambient standard coordinate space. -/
theorem polytope_dimension {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank ℝ (vectorSpan ℝ (polytope n)) = n-1 := by
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (polytope_nonempty n)
  intro i
  obtain ⟨S,hu,hv,hδ⟩ := consecutive_positive_slack hn i
  exact root_mem_vectorSpan_of_delta_ne_zero (setFunction_normalized n).1
    (setFunction_supermodular n) (by simp [Fin.ext_iff]) hu hv (by rw [hδ]; norm_num)

end Path
end GraphicalZonotopes
