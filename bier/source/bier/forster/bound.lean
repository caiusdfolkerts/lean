import bier.forster.factor_bound

/-! # Forster's sign-rank bound, with all rank and cardinality cases

The hypothesis on `L` is precisely the squared Euclidean operator bound of
the sign matrix. Every realizing matrix is covered, including degenerate
placements; general position is proved internally by perturbation.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {R C : Type*} [Fintype R] [Fintype C]

theorem SquaredOperatorBound.card_columns_le [Nonempty R]
    (H : Matrix R C ℝ) (hH : Bier.IsSignMatrix H) (L : ℝ)
    (hL : SquaredOperatorBound H L) : (Fintype.card C : ℝ) ≤ L := by
  let r : R := Classical.choice inferInstance
  have hh := hL (Pi.single r 1)
  have hsq (c : C) : H r c ^ 2 = 1 := by
    rcases hH r c with he | he <;> rw [he] <;> norm_num
  simpa [Pi.single_apply, hsq] using hh

theorem SignRealizes.rank_pos [Nonempty R] [Nonempty C]
    (H M : Matrix R C ℝ) (hM : Bier.SignRealizes H M) : 0 < M.rank := by
  by_contra hn
  have hz : M.rank = 0 := by omega
  obtain ⟨U, V, hUV⟩ := exists_rank_factorization M
  haveI : IsEmpty (Fin M.rank) := Fintype.card_eq_zero_iff.mp (by simpa using hz)
  have he : M = 0 := by
    ext r c
    have hh := congrFun (congrFun hUV r) c
    simpa [Matrix.mul_apply] using hh.symm
  let r : R := Classical.choice inferInstance
  let c : C := Classical.choice inferInstance
  have hp := hM r c
  simp [he] at hp

theorem forster_bound_fin {n : ℕ} (H M : Matrix (Fin n) C ℝ)
    (hH : Bier.IsSignMatrix H) (hM : Bier.SignRealizes H M)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : SquaredOperatorBound H L) :
    (n : ℝ) * Fintype.card C ≤ L * (M.rank : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn, mul_nonneg hL0 (sq_nonneg (M.rank : ℝ))]
  have hn' : 0 < n := by omega
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn'
  cases isEmpty_or_nonempty C with
  | inl he => simp [Fintype.card_ofIsEmpty, mul_nonneg hL0 (sq_nonneg (M.rank : ℝ))]
  | inr he =>
    have hk := SignRealizes.rank_pos H M hM
    by_cases hkn : M.rank < n
    · obtain ⟨U, V, hUV⟩ := exists_rank_factorization M
      exact forster_bound_small_factor H hH U V (by simpa [hUV] using hM) hk hkn L hL
    · have hc := hL.card_columns_le H hH L
      have hnk : (n : ℝ) ≤ (M.rank : ℝ) := by exact_mod_cast (show n ≤ M.rank by omega)
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      have hnk2 : (n : ℝ) ≤ (M.rank : ℝ) ^ 2 := by nlinarith
      calc
        (n : ℝ) * Fintype.card C ≤ n * L := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = L * n := by ring
        _ ≤ L * (M.rank : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hnk2 hL0

theorem SquaredOperatorBound.reindex_rows (H : Matrix R C ℝ) (L : ℝ)
    (hL : SquaredOperatorBound H L) {S : Type*} [Fintype S] (e : S ≃ R) :
    SquaredOperatorBound (H.submatrix e id) L := by
  intro x
  have hh := hL (fun r => x (e.symm r))
  have hn : (∑ r : R, x (e.symm r) ^ 2) = ∑ s : S, x s ^ 2 := by
    simpa using (e.sum_comp (fun r => x (e.symm r) ^ 2)).symm
  have hc (c : C) : (∑ r : R, H r c * x (e.symm r)) =
      ∑ s : S, (H.submatrix e id) s c * x s := by
    simpa using (e.sum_comp (fun r => H r c * x (e.symm r))).symm
  simpa only [hn, hc] using hh

/-- The full squared Forster bound for every strict sign realization. -/
theorem forster_bound (H M : Matrix R C ℝ)
    (hH : Bier.IsSignMatrix H) (hM : Bier.SignRealizes H M)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : SquaredOperatorBound H L) :
    (Fintype.card R : ℝ) * Fintype.card C ≤ L * (M.rank : ℝ) ^ 2 := by
  let e := (Fintype.equivFin R).symm
  have hh := forster_bound_fin (H.submatrix e id) (M.submatrix e id)
    (fun r c => hH (e r) c) (fun r c => hM (e r) c)
    L hL0 (hL.reindex_rows H L e)
  have hr : (M.submatrix e id).rank = M.rank :=
    Matrix.rank_submatrix M e (Equiv.refl C)
  simpa only [hr] using hh

/-- The sign rank is an actual attained matrix rank, so the same inequality
holds at the minimum over all realizations. -/
theorem signRank_bound (H : Matrix R C ℝ) (hH : Bier.IsSignMatrix H)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : SquaredOperatorBound H L) :
    (Fintype.card R : ℝ) * Fintype.card C ≤ L * (Bier.signRank H : ℝ) ^ 2 := by
  obtain ⟨M, hM, hr⟩ := Bier.exists_rank_eq_signRank hH
  simpa only [hr] using forster_bound H M hH hM L hL0 hL

end Bier.Forster
