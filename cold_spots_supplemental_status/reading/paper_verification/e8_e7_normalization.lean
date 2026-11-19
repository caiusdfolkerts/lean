module

public import PaperVerification.E8IntegralBasis
public import PaperVerification.E7Roots


@[expose] public section
/-! # Minimal squared norm of the E8 and E7 root lattices

The coordinate lattices used by the principal cold-spot endpoints have exactly
the root normalization printed in the paper.  E7* is already identified with
the ordinary integral dual of this E7 lattice in its Euclidean hyperplane.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

theorem sqDist_zero_pos_of_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < sqDist x 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  unfold sqDist
  simp only [Pi.zero_apply, sub_zero]
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem e8_nonzero_squared_norm_lower {x : Fin 8 → ℝ}
    (hx : x ∈ dPlusSet 8) (hne : x ≠ 0) : 2 ≤ sqDist x 0 := by
  obtain ⟨t, rfl⟩ := (e8_mem_iff_integer_root_coordinates x).mp hx
  have hp := sqDist_zero_pos_of_ne_zero hne
  rw [e8RootSum_norm] at hp ⊢
  have hq : 0 < e8IntegralQ t := by exact_mod_cast (by linarith : (0 : ℝ) < e8IntegralQ t)
  have hq' : (1 : ℝ) ≤ e8IntegralQ t := by exact_mod_cast (by omega : (1 : ℤ) ≤ e8IntegralQ t)
  linarith

theorem e8_minimal_squared_norm :
    (∀ x ∈ dPlusSet 8, x ≠ 0 → 2 ≤ sqDist x 0) ∧
      ∃ x ∈ dPlusSet 8, x ≠ 0 ∧ sqDist x 0 = 2 := by
  refine ⟨fun _ hx hne => e8_nonzero_squared_norm_lower hx hne,
    e8SimpleRoot 1, e8SimpleRoot_mem 1, ?_, ?_⟩
  · intro h
    have he := congrFun h 0
    norm_num [e8SimpleRoot] at he
  · norm_num [sqDist, e8SimpleRoot, Fin.sum_univ_succ]

theorem e7_minimal_squared_norm :
    (∀ x ∈ e7Set, x ≠ 0 → 2 ≤ sqDist x.val 0) ∧
      ∃ x ∈ e7Set, x ≠ 0 ∧ sqDist x.val 0 = 2 := by
  constructor
  · intro x hx hne
    apply e8_nonzero_squared_norm_lower hx
    intro h
    exact hne (Subtype.ext h)
  · refine ⟨e7SimpleRoot 1, e7SimpleRoot_mem 1, ?_, ?_⟩
    · intro h
      have he := congrArg (fun x : zeroSumSpace => x.val 0) h
      norm_num [e7SimpleRoot, e7RootVector] at he
    · norm_num [sqDist, e7SimpleRoot, e7RootVector, Fin.sum_univ_succ]

end PaperVerification.ColdSpots
