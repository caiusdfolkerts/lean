module

public import Papers.GraphicalZonotopes.PathPlaneGeometry
public import Papers.GraphicalZonotopes.PathGraph

@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- An actual straight-line drawing in the real plane: vertices are distinct,
no vertex lies on an unrelated edge, and two different edges intersect only at
a common endpoint. This gives a concrete plane embedding, not a combinatorial
proxy for planarity. -/
def HasPlaneStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → (Fin 2 → ℝ), Function.Injective p ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v →
      p w ∉ segment ℝ (p u) (p v)) ∧
    ∀ u v a b, G.Adj u v → G.Adj a b → ∀ x : Fin 2 → ℝ,
      x ∈ segment ℝ (p u) (p v) → x ∈ segment ℝ (p a) (p b) →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        ∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ x = p w

namespace PathDrawing

theorem ordered_plane_segment (i j : ℕ) :
    segment ℝ (planePoint (min i j)) (planePoint (max i j)) =
      segment ℝ (planePoint i) (planePoint j) := by
  by_cases h : i ≤ j
  · simp [min_eq_left h,max_eq_right h]
  · have h' : j ≤ i := by omega
    rw [min_eq_right h',max_eq_left h']
    exact segment_symm ℝ _ _

theorem path_plane_drawing (n : ℕ) : HasPlaneStraightLineDrawing (Path.graph n) := by
  let p : Fin n → Plane := fun v => planePoint v.val
  refine ⟨p,?_,?_,?_⟩
  · intro u v h
    exact Fin.ext (planePoint_injective h)
  · intro u v w huv hwu hwv
    have huv' : u.val ≠ v.val := fun h => huv.1 (Fin.ext h)
    have hwu' : w.val ≠ u.val := fun h => hwu (Fin.ext h)
    have hwv' : w.val ≠ v.val := fun h => hwv (Fin.ext h)
    have huBound := huv.2.1
    have hvBound := huv.2.2
    have h1 : min u.val v.val < max u.val v.val := by omega
    have h2 : max u.val v.val ≤ min u.val v.val+3 := by omega
    have h3 : w.val ≠ min u.val v.val := by omega
    have h4 : w.val ≠ max u.val v.val := by omega
    have h := plane_vertex_not_on_edge h1 h2 h3 h4
    rw [ordered_plane_segment] at h
    exact h
  · intro u v a b huv hab x hx hy
    have huv' : u.val ≠ v.val := fun h => huv.1 (Fin.ext h)
    have hab' : a.val ≠ b.val := fun h => hab.1 (Fin.ext h)
    have huBound := huv.2.1
    have hvBound := huv.2.2
    have haBound := hab.2.1
    have hbBound := hab.2.2
    have h1 : min u.val v.val < max u.val v.val := by omega
    have h2 : max u.val v.val ≤ min u.val v.val+3 := by omega
    have h3 : min a.val b.val < max a.val b.val := by omega
    have h4 : max a.val b.val ≤ min a.val b.val+3 := by omega
    have hx' : x ∈ segment ℝ (planePoint (min u.val v.val))
        (planePoint (max u.val v.val)) := by
      rw [ordered_plane_segment]
      exact hx
    have hy' : x ∈ segment ℝ (planePoint (min a.val b.val))
        (planePoint (max a.val b.val)) := by
      rw [ordered_plane_segment]
      exact hy
    rcases plane_ordered_edges_meet h1 h2 h3 h4 hx' hy' with ⟨hmin,hmax⟩ | ⟨w,hw,hz,he⟩
    · have h : (u.val = a.val ∧ v.val = b.val) ∨
          (u.val = b.val ∧ v.val = a.val) := by omega
      rcases h with ⟨hua,hvb⟩ | ⟨hub,hva⟩
      · exact Or.inl ⟨Fin.ext hua,Fin.ext hvb⟩
      · exact Or.inr (Or.inl ⟨Fin.ext hub,Fin.ext hva⟩)
    · have hw' : w = u.val ∨ w = v.val := by omega
      have hz' : w = a.val ∨ w = b.val := by omega
      have hwn : w < n := by rcases hw' with h | h <;> omega
      let W : Fin n := ⟨w,hwn⟩
      refine Or.inr (Or.inr ⟨W,?_,?_,he⟩)
      · rcases hw' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · rcases hz' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)

end PathDrawing
end GraphicalZonotopes
