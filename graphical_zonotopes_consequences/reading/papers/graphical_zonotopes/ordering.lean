module

public import Papers.GraphicalZonotopes.BasePolytope

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every set occurs as a prefix of a linear ordering. -/
theorem exists_prefix_enumeration (S : Finset V) :
    ∃ (e : Fin (Fintype.card V) ≃ V) (j : ℕ), j ≤ Fintype.card V ∧
      orderPrefix e j = S := by
  classical
  let w : V → ℝ := fun v => if v ∈ S then 1 else 0
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  let j := (univ.filter (fun i : Fin (Fintype.card V) => (1 : ℝ) ≤ w (e i))).card
  refine ⟨e, j, ?_, ?_⟩
  · exact (card_filter_le _ _).trans (by simp)
  · ext v
    simp only [orderPrefix, mem_filter, mem_univ, true_and]
    have h := Tuple.lt_card_ge_iff_apply_ge_of_antitone (j := e.symm v) (a := (1 : ℝ)) he
    by_cases hv : v ∈ S <;> norm_num [j, w, hv] at h ⊢ <;> exact h

/-- An arbitrary conditioning set can be followed by either specified ordered pair. -/
theorem exists_pair_enumeration (S : Finset V) {u v : V} (huv : u ≠ v)
    (hu : u ∉ S) (hv : v ∉ S) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      orderPrefix e (e.symm u).val = S ∧
      orderPrefix e (e.symm v).val = insert u S := by
  classical
  let w : V → ℝ := fun x => if x ∈ S then 3 else if x = u then 2 else if x = v then 1 else 0
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  have wu : w u = 2 := by simp [w, hu]
  have wv : w v = 1 := by simp [w, hv, Ne.symm huv]
  have hmono : ∀ x y, e.symm x ≤ e.symm y → w y ≤ w x := by
    intro x y hxy
    simpa using he hxy
  refine ⟨e, ?_, ?_⟩
  · ext x
    simp only [orderPrefix, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      by_contra hxS
      have hxu : x ≠ u := by intro h; subst x; omega
      have hwx : w x ≤ 1 := by simp only [w, if_neg hxS, if_neg hxu]; split <;> norm_num
      have h := hmono x u (by exact le_of_lt hx)
      rw [wu] at h
      linarith
    · intro hxS
      have hwx : w x = 3 := by simp [w, hxS]
      by_contra hx
      have h := hmono u x (by omega)
      rw [wu, hwx] at h
      norm_num at h
  · ext x
    simp only [orderPrefix, mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hx
      by_contra hnot
      push_neg at hnot
      have hxv : x ≠ v := by intro h; subst x; omega
      have hwx : w x = 0 := by simp [w, hnot.1, hnot.2, hxv]
      have h := hmono x v (by exact le_of_lt hx)
      rw [wv, hwx] at h
      norm_num at h
    · intro hx
      have hwx : 2 ≤ w x := by
        rcases hx with rfl | hxS
        · rw [wu]
        · norm_num [w, hxS]
      by_contra hnot
      have h := hmono v x (by omega)
      rw [wv] at h
      linarith

end GraphicalZonotopes
