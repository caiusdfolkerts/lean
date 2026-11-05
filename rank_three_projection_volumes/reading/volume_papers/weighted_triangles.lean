module

public import VolumePapers.MetricObstruction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push
public import Mathlib.Data.Finset.Max

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace VolumePapers.RankThree

/-- The hypotheses on a matrix are geometric and independent of any weight vector. -/
structure PositiveHollowMatrix (n : ℕ) where
  entries : Matrix (Fin n) (Fin n) ℝ
  hollow : ∀ i, entries i i = 0
  symmetric : ∀ i j, entries i j = entries j i
  positive : ∀ i j, i ≠ j → 0 < entries i j

namespace PositiveHollowMatrix

variable {n : ℕ} (P : PositiveHollowMatrix n)

/-- The inequalities of Corollary 2.3, with precisely the three distinct labels
specified in the paper. -/
def WeightedTriangles (x : Fin n → ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    P.entries i j * x k ≤ P.entries i k * x j + P.entries j k * x i

theorem nonnegative (i j : Fin n) : 0 ≤ P.entries i j := by
  by_cases hij : i = j
  · subst j; rw [P.hollow]
  · exact (P.positive i j hij).le

theorem weighted_all (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (ht : P.WeightedTriangles x) (i j k : Fin n) :
    P.entries i j * x k ≤ P.entries i k * x j + P.entries j k * x i := by
  by_cases hij : i = j
  · subst j
    rw [P.hollow, zero_mul]
    exact add_nonneg (mul_nonneg (P.nonnegative i k) (hx i))
      (mul_nonneg (P.nonnegative i k) (hx i))
  by_cases hik : i = k
  · subst k
    simp only [P.hollow, zero_mul, zero_add, P.symmetric j i]
    exact le_rfl
  by_cases hjk : j = k
  · subst k
    simp [P.hollow]
  exact ht i j k hij hik hjk

/-- Positive weights turn the weighted inequalities into the ordinary metric
inequalities. The rank bound is proved by literal diagonal matrix multiplication. -/
theorem positive_weights_impossible (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) : ¬ P.WeightedTriangles x := by
  intro ht
  let D : PositiveMetricMatrix n :=
    { entries := fun i j => P.entries i j / (x i*x j)
      hollow := by intro i; simp [P.hollow]
      symmetric := by intro i j; rw [P.symmetric i j, mul_comm (x i) (x j)]
      positive := by intro i j hij; exact div_pos (P.positive i j hij) (mul_pos (hx i) (hx j))
      triangle := by
        intro i j k
        have ht' := P.weighted_all x (fun a => (hx a).le) ht i j k
        have hprod : 0 < x i*x j*x k := mul_pos (mul_pos (hx i) (hx j)) (hx k)
        apply (mul_le_mul_iff_of_pos_right hprod).mp
        have hi := (hx i).ne'
        have hj := (hx j).ne'
        have hk := (hx k).ne'
        calc
          (P.entries i j / (x i*x j)) * (x i*x j*x k) = P.entries i j*x k := by
            field_simp [hi,hj,hk] <;> ring
          _ ≤ P.entries i k*x j + P.entries j k*x i := ht'
          _ = (P.entries i k/(x i*x k) + P.entries k j/(x k*x j))*(x i*x j*x k) := by
            rw [P.symmetric k j]
            field_simp [hi,hj,hk]
            <;> ring }
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => (x i)⁻¹)
  have heq : D.entries = M * P.entries * M := by
    ext i j
    simp [D, M, Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv, mul_inv_rev] <;>
      ring
  have hD : D.entries.rank ≤ P.entries.rank := by
    rw [heq]
    exact (Matrix.rank_mul_le_left (M * P.entries) M).trans
      (Matrix.rank_mul_le_right M P.entries)
  have hfour := D.rank_at_least_four hn
  omega

/-- A nonzero nonnegative solution has at most one zero coordinate. -/
theorem positive_away_from_zero (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hne : x ≠ 0) (ht : P.WeightedTriangles x)
    (z : Fin n) (hz : x z = 0) : ∀ i, i ≠ z → 0 < x i := by
  have hex : ∃ k, 0 < x k := by
    by_contra h
    push_neg at h
    apply hne
    funext k
    exact le_antisymm (h k) (hx k)
  obtain ⟨k,hk⟩ := hex
  intro i hiz
  by_contra hi
  have hix : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
  have hzk : z ≠ k := by intro h; subst k; rw [hz] at hk; exact (lt_irrefl 0 hk)
  have hik : i ≠ k := by intro h; subst k; rw [hix] at hk; exact (lt_irrefl 0 hk)
  have hineq := ht z i k hiz.symm hzk hik
  rw [hix,hz,mul_zero,mul_zero,add_zero] at hineq
  exact (not_le_of_gt (mul_pos (P.positive z i hiz.symm) hk)) hineq

private theorem exists_uniform_positive_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  let δ := Finset.univ.inf' Finset.univ_nonempty f
  refine ⟨δ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hf i)
  · intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)

/-- Filling a single zero coordinate with a sufficiently small positive number
preserves every weighted triangle inequality, with no positive-margin hypothesis. -/
theorem exists_positive_weights (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hne : x ≠ 0) (ht : P.WeightedTriangles x) :
    ∃ y : Fin n → ℝ, (∀ i, 0 < y i) ∧ P.WeightedTriangles y := by
  classical
  by_cases hzero : ∃ z, x z = 0
  · obtain ⟨z,hz⟩ := hzero
    have hxpos := P.positive_away_from_zero x hx hne ht z hz
    let f : Fin n × Fin n → ℝ := fun ij =>
      if ij.1 = ij.2 ∨ ij.1 = z ∨ ij.2 = z then 1
      else (P.entries ij.1 z*x ij.2 + P.entries ij.2 z*x ij.1)/P.entries ij.1 ij.2
    have hf : ∀ ij, 0 < f ij := by
      intro ⟨i,j⟩
      dsimp [f]
      split_ifs with h
      · norm_num
      · push_neg at h
        exact div_pos (add_pos (mul_pos (P.positive i z h.2.1) (hxpos j h.2.2))
          (mul_pos (P.positive j z h.2.2) (hxpos i h.2.1))) (P.positive i j h.1)
    haveI : Nonempty (Fin n) := ⟨z⟩
    obtain ⟨δ,hδ,hbound⟩ := exists_uniform_positive_bound f hf
    let y : Fin n → ℝ := fun i => if i = z then δ else x i
    have hypos : ∀ i, 0 < y i := by
      intro i
      by_cases hiz : i = z
      · simp [y,hiz,hδ]
      · simpa [y,hiz] using hxpos i hiz
    have hxy : ∀ i, x i ≤ y i := by
      intro i
      by_cases hiz : i = z
      · subst i; simpa [y,hz] using hδ.le
      · simp [y,hiz]
    refine ⟨y,hypos,?_⟩
    intro i j k hij hik hjk
    by_cases hkz : k = z
    · subst k
      have hb := hbound (i,j)
      have hnot : ¬ (i = j ∨ i = z ∨ j = z) := by simp [hij,hik,hjk]
      simp only [f,hnot,if_false] at hb
      simp only [y,hik,hjk,if_false,if_pos rfl]
      simpa only [mul_comm] using (le_div_iff₀ (P.positive i j hij)).mp hb
    · calc
        P.entries i j * y k = P.entries i j*x k := by simp [y,hkz]
        _ ≤ P.entries i k*x j + P.entries j k*x i := ht i j k hij hik hjk
        _ ≤ P.entries i k*y j + P.entries j k*y i :=
          add_le_add (mul_le_mul_of_nonneg_left (hxy j) (P.nonnegative i k))
            (mul_le_mul_of_nonneg_left (hxy i) (P.nonnegative j k))
  · refine ⟨x,?_,ht⟩
    intro i
    exact lt_of_le_of_ne (hx i) (by intro h; exact hzero ⟨i,h.symm⟩)

/-- Corollary 2.3, in full: no nonzero nonnegative weight vector can satisfy the
inequalities on five labels. Rank at most three is enough for the contradiction. -/
theorem weighted_triangles_obstruction (hn : 5 ≤ n) (hrank : P.entries.rank ≤ 3) :
    ¬ ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧ P.WeightedTriangles x := by
  rintro ⟨x,hx,hne,ht⟩
  obtain ⟨y,hy,hyt⟩ := P.exists_positive_weights x hx hne ht
  exact P.positive_weights_impossible hn hrank y hy hyt

end PositiveHollowMatrix
end VolumePapers.RankThree

namespace VolumePapers.RankThree

/-- Matrix-form interface to Corollary 2.3. The number of labels is arbitrary,
provided it is at least five. No geometric realization is assumed. -/
theorem no_nonnegative_weighted_triangles {n : ℕ} (hn : 5 ≤ n)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hollow : ∀ i, P i i = 0)
    (symmetric : ∀ i j, P i j = P j i)
    (positive : ∀ i j, i ≠ j → 0 < P i j)
    (rank : P.rank ≤ 3)
    (x : Fin n → ℝ) (nonnegative : ∀ i, 0 ≤ x i) (nonzero : x ≠ 0) :
    ¬ (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      P i j * x k ≤ P i k * x j + P j k * x i) := by
  let Q : PositiveHollowMatrix n := ⟨P, hollow, symmetric, positive⟩
  intro weighted
  exact Q.weighted_triangles_obstruction hn rank
    ⟨x, nonnegative, nonzero, weighted⟩

/-- Exactly the five-label, rank-three assertion of the paper's Corollary 2.3. -/
theorem corollary_two_three
    (P : Matrix (Fin 5) (Fin 5) ℝ)
    (hollow : ∀ i, P i i = 0)
    (symmetric : ∀ i j, P i j = P j i)
    (positive : ∀ i j, i ≠ j → 0 < P i j)
    (rank : P.rank = 3) :
    ¬ ∃ x : Fin 5 → ℝ, (∀ i, 0 ≤ x i) ∧ x ≠ 0 ∧
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        P i j * x k ≤ P i k * x j + P j k * x i := by
  rintro ⟨x, hx, hne, hweighted⟩
  exact no_nonnegative_weighted_triangles (by omega) P hollow symmetric positive
    rank.le x hx hne hweighted

end VolumePapers.RankThree
