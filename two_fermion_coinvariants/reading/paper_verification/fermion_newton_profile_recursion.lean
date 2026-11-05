module

public import PaperVerification.FermionNewtonPrefixBlock

/-!
# First-coordinate blocks for arbitrary compatible multiplicities

These are identities for the literal rational Newton columns. They retain
the active interval at every coordinate and make no determinant assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

theorem activeInterval_succ (δ : Fin (n + 1) → ℕ) (i : Fin n) :
    activeInterval δ i.succ = (activeInterval (δ ∘ Fin.succ) i).map (Fin.succEmb n) := by
  ext k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp [activeInterval, Finset.mem_map, Fin.succEmb]
  · change k.succ ∈ activeInterval δ i.succ ↔
      (Fin.succEmb n) k ∈ (activeInterval (δ ∘ Fin.succ) i).map (Fin.succEmb n)
    rw [Finset.mem_map']
    simp only [mem_activeInterval, Fin.succ_le_succ_iff, Function.comp_apply]
    constructor
    · rintro ⟨hik, h⟩
      exact ⟨hik, fun j hij hjk ↦ h j.succ
        (Fin.succ_lt_succ_iff.mpr hij) (Fin.succ_le_succ_iff.mpr hjk)⟩
    · rintro ⟨hik, h⟩
      refine ⟨hik, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · intro hij
        exact False.elim (not_lt_of_ge (Fin.zero_le _) hij)
      · exact fun hij hjk ↦ h j (Fin.succ_lt_succ_iff.mp hij)
          (Fin.succ_le_succ_iff.mp hjk)

theorem profileNumerator_succ_of_ne_one
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x : Fin (n + 1) → L)
    (i : Fin n) (hσ : σ 0 ≠ 1) :
    profileNumerator δ σ x i.succ =
      profileNumerator (δ ∘ Fin.succ) (σ ∘ Fin.succ) (x ∘ Fin.succ) i := by
  rw [profileNumerator, earlierPositive_succ, if_neg hσ, nodal_map_embedding]
  rfl

theorem profileNumerator_succ_of_one
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x : Fin (n + 1) → L)
    (i : Fin n) (hσ : σ 0 = 1) :
    profileNumerator δ σ x i.succ =
      profileNumerator (δ ∘ Fin.succ) (σ ∘ Fin.succ) (x ∘ Fin.succ) i * (X - C (x 0)) := by
  rw [profileNumerator, earlierPositive_succ, if_pos hσ,
    nodal_insert _ x 0 (by simp [Finset.mem_map, Fin.succEmb]), nodal_map_embedding]
  change X ^ δ i.succ * ((X - C (x 0)) *
      Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i) (x ∘ Fin.succ)) =
    (X ^ δ i.succ * Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i) (x ∘ Fin.succ)) *
      (X - C (x 0))
  ring

@[simp] theorem profileNewtonMatrix_first_column
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (k : Fin (n + 1)) :
    profileNewtonMatrix δ σ x β k 0 = if k ∈ activeInterval δ 0 then x k ^ δ 0 else 0 := by
  simp [profileNewtonMatrix, profileNumerator, rationalColumn,
    earlierPositive_zero, earlierNegative_zero, Lagrange.nodal]

@[simp] theorem profileNewtonMatrix_zero_zero
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L) :
    profileNewtonMatrix δ σ x β 0 0 = x 0 ^ δ 0 := by
  rw [profileNewtonMatrix_first_column, if_pos (self_mem_activeInterval δ 0)]

theorem profileNewtonMatrix_first_row_nonnegative
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 ≠ -1) (i : Fin n) : profileNewtonMatrix δ σ x β 0 i.succ = 0 := by
  simp [profileNewtonMatrix, rationalColumn, activeInterval, earlierNegative, hσ]

theorem profileNewtonMatrix_suffix_flat
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = 0) (k i : Fin n) :
    profileNewtonMatrix δ σ x β k.succ i.succ =
      profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
        (x ∘ Fin.succ) (β ∘ Fin.succ) k i := by
  rw [profileNewtonMatrix, profileNumerator_succ_of_ne_one δ σ x i (by omega),
    earlierNegative_succ, if_neg (by omega), activeInterval_succ]
  exact rationalColumn_map_embedding (Fin.succEmb n) _ _ _ x β k

theorem profileNewtonMatrix_suffix_up
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = 1) (k i : Fin n) :
    profileNewtonMatrix δ σ x β k.succ i.succ = (x k.succ - x 0) *
      profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
        (x ∘ Fin.succ) (β ∘ Fin.succ) k i := by
  rw [profileNewtonMatrix, profileNumerator_succ_of_one δ σ x i hσ,
    earlierNegative_succ, if_neg (by omega), activeInterval_succ,
    rationalColumn_mul_polynomial, eval_sub, eval_X, eval_C]
  congr 1
  exact rationalColumn_map_embedding (Fin.succEmb n) _ _ _ x β k

theorem profileNewtonMatrix_suffix_down
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = -1) (k i : Fin n) :
    profileNewtonMatrix δ σ x β k.succ i.succ =
      profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
        (x ∘ Fin.succ) (β ∘ Fin.succ) k i / (x k.succ - x 0) := by
  rw [profileNewtonMatrix, profileNumerator_succ_of_ne_one δ σ x i (by omega),
    earlierNegative_succ, if_pos hσ, activeInterval_succ]
  exact rationalColumn_negative_suffix (Fin.succEmb n) _ _ _ x β 0
    (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj) k

theorem profileNewtonMatrix_first_row_down
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = -1) (i : Fin n) :
    profileNewtonMatrix δ σ x β 0 i.succ =
      x 0 ^ δ i.succ *
        ((Lagrange.nodal (earlierPositive (σ ∘ Fin.succ) i) (x ∘ Fin.succ)).eval (x 0) /
          ((Lagrange.nodal (earlierNegative (σ ∘ Fin.succ) i) (x ∘ Fin.succ)).eval (x 0) * β 0) *
            ∑ k ∈ activeInterval (δ ∘ Fin.succ) i, β k.succ / (x 0 - x k.succ)) := by
  rw [profileNewtonMatrix, profileNumerator_succ_of_ne_one δ σ x i (by omega),
    earlierNegative_succ, if_pos hσ, activeInterval_succ,
    rationalColumn_negative_new_row (Fin.succEmb n) _ _ _ x β 0
      (by rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj)]
  simp only [profileNumerator, eval_mul, eval_pow, eval_X, Fin.coe_succEmb, Function.comp_apply]
  ring

theorem profileNewtonMatrix_eq_adjoin
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (scale : Fin n → L)
    (hscale : ∀ k i,
      profileNewtonMatrix δ σ x β k.succ i.succ = scale k *
        profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
          (x ∘ Fin.succ) (β ∘ Fin.succ) k i) :
    profileNewtonMatrix δ σ x β =
      adjoinPowerColumn (x 0 ^ δ 0)
        (fun k ↦ profileNewtonMatrix δ σ x β k.succ 0)
        (fun i ↦ profileNewtonMatrix δ σ x β 0 i.succ) scale
        (profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
          (x ∘ Fin.succ) (β ∘ Fin.succ)) := by
  ext k i
  refine Fin.cases ?_ (fun k ↦ ?_) k <;> refine Fin.cases ?_ (fun i ↦ ?_) i
  · exact profileNewtonMatrix_zero_zero δ σ x β
  · rfl
  · rfl
  · exact hscale k i

theorem profileNewtonMatrix_nonnegative_det_ne_zero
    (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = 0 ∨ σ 0 = 1) (hx : Function.Injective x) (hx0 : x 0 ≠ 0)
    (hS : (profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ)
      (x ∘ Fin.succ) (β ∘ Fin.succ)).det ≠ 0) :
    (profileNewtonMatrix δ σ x β).det ≠ 0 := by
  let S := profileNewtonMatrix (δ ∘ Fin.succ) (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)
  let η := fun k : Fin n ↦ profileNewtonMatrix δ σ x β k.succ 0
  rcases hσ with hσ | hσ
  · have hM : profileNewtonMatrix δ σ x β = adjoinPowerColumn (x 0 ^ δ 0) η 0 1 S := by
      rw [profileNewtonMatrix_eq_adjoin δ σ x β 1
        (fun k i ↦ by simpa only [Pi.one_apply, one_mul] using
          profileNewtonMatrix_suffix_flat δ σ x β hσ k i)]
      congr 1
      funext i
      exact profileNewtonMatrix_first_row_nonnegative δ σ x β (by omega) i
    rw [hM, adjoinPowerColumn_zero_row_det]
    simpa only [Pi.one_apply, Finset.prod_const_one, mul_one] using mul_ne_zero (pow_ne_zero _ hx0) hS
  · have hM : profileNewtonMatrix δ σ x β =
        adjoinPowerColumn (x 0 ^ δ 0) η 0 (fun k ↦ x k.succ - x 0) S := by
      rw [profileNewtonMatrix_eq_adjoin δ σ x β (fun k ↦ x k.succ - x 0)
        (profileNewtonMatrix_suffix_up δ σ x β hσ)]
      congr 1
      funext i
      exact profileNewtonMatrix_first_row_nonnegative δ σ x β (by omega) i
    rw [hM, adjoinPowerColumn_zero_row_det]
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx0) _) hS
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun he ↦ Fin.succ_ne_zero k (hx he))

theorem activeInterval_first_of_prefix
    {m : ℕ} (hm : m < n) (δ : Fin n → ℕ) (d : ℕ)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) (k : Fin n) :
    k.succ ∈ activeInterval (Fin.cases d δ) 0 ↔ k.val < m := by
  constructor
  · intro hk
    rcases (mem_activeInterval _ _ _).mp hk with ⟨_, h⟩
    by_contra hn
    have hh := h (Fin.succ ⟨m, hm⟩) (Fin.succ_pos _) (Fin.succ_le_succ_iff.mpr (Nat.le_of_not_gt hn))
    exact (not_le_of_gt hjump) hh
  · intro hk
    refine (mem_activeInterval _ _ _).mpr ⟨Fin.zero_le _, ?_⟩
    intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · intro h
      exact False.elim (lt_irrefl _ h)
    · intro hj hjk
      change δ j ≤ d
      rw [hδ j (lt_of_le_of_lt (Fin.succ_le_succ_iff.mp hjk) hk)]

end PaperVerification.Fermion.Newton
