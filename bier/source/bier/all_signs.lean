import bier.sign_rank
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Full sign rank of the matrix containing every normalized column pattern -/

noncomputable section

namespace Bier

open scoped BigOperators

variable (R : Type*) [Fintype R] [DecidableEq R]

/-- The distinguished row is all positive; the remaining rows realize every sign pattern. -/
def allColumnSigns : Matrix (Option R) (R → Fin 2) ℝ := fun r c =>
  match r with
  | none => 1
  | some i => if c i = 0 then 1 else -1

theorem allColumnSigns_sign : IsSignMatrix (allColumnSigns R) := by
  intro r c
  cases r <;> simp only [allColumnSigns]
  · exact Or.inl trivial
  · split_ifs <;> simp

private theorem allColumnSigns_relation_nonneg
    (M : Matrix (Option R) (R → Fin 2) ℝ) (hM : SignRealizes (allColumnSigns R) M)
    (a : Option R → ℝ) (ha : 0 ≤ a none)
    (hzero : ∑ r, a r • M.row r = 0) : ∀ r, a r = 0 := by
  classical
  let c : R → Fin 2 := fun r => if 0 ≤ a (some r) then 0 else 1
  have hnonneg : ∀ r, 0 ≤ a r * M r c := by
    intro r
    cases r with
    | none =>
      have hm := hM none c
      simp only [allColumnSigns, one_mul] at hm
      exact mul_nonneg ha hm.le
    | some r =>
      have hm := hM (some r) c
      by_cases h : 0 ≤ a (some r)
      · simp [allColumnSigns, c, h] at hm
        exact mul_nonneg h hm.le
      · simp [allColumnSigns, c, h] at hm
        exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge h) hm.le
  have hsum : ∑ r, a r * M r c = 0 := by
    simpa [Matrix.row, Finset.sum_apply] using congrFun hzero c
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hnonneg r)).mp hsum
  intro r
  exact (mul_eq_zero.mp (hall r (Finset.mem_univ _))).resolve_right (hM.entry_ne_zero r c)

theorem allColumnSigns_rows_independent
    (M : Matrix (Option R) (R → Fin 2) ℝ) (hM : SignRealizes (allColumnSigns R) M) :
    LinearIndependent ℝ M.row := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a hzero
  by_cases ha : 0 ≤ a none
  · exact allColumnSigns_relation_nonneg R M hM a ha hzero
  · have hz : ∑ r, (-a r) • M.row r = 0 := by
      simp only [neg_smul, Finset.sum_neg_distrib, hzero, neg_zero]
    have hh := allColumnSigns_relation_nonneg R M hM (fun r => -a r)
      (by linarith) hz
    intro r
    exact neg_eq_zero.mp (hh r)

theorem allColumnSigns_rank
    (M : Matrix (Option R) (R → Fin 2) ℝ) (hM : SignRealizes (allColumnSigns R) M) :
    M.rank = Fintype.card R + 1 := by
  simpa using (allColumnSigns_rows_independent R M hM).rank_matrix

theorem allColumnSigns_signRank : signRank (allColumnSigns R) = Fintype.card R + 1 := by
  obtain ⟨M, hM, hr⟩ := exists_rank_eq_signRank (allColumnSigns_sign R)
  exact hr.symm.trans (allColumnSigns_rank R M hM)

theorem allColumnSigns_positive : ∃ r c, allColumnSigns R r c = 1 :=
  ⟨none, fun _ => 0, rfl⟩

end Bier
