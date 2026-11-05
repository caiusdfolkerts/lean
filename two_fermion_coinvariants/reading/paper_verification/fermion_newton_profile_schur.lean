module

public import PaperVerification.FermionNewtonProfileRecursion

/-!
# The supported Schur numerator at a multiplicity jump

The expansion of the lower-left vector stays inside the initial constant
block. Every positive set there is empty, so its entire Schur contribution
has degree below the full nodal denominator. The remaining leading
coefficient is exactly the nonempty prefix sum of the weights.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

theorem clearedSchur_ne_zero_of_supported_no_positive
    (y β : Fin n → L) (β₀ : L) (positive poles active : Fin n → Finset (Fin n))
    (A : Fin n → L) (U : Finset (Fin n))
    (hdisj : ∀ i, Disjoint (active i) (poles i))
    (hpositive : ∀ i ∈ U, positive i = ∅)
    (hsupport : ∀ i, i ∉ U → A i = 0)
    (hβ : β₀ + ∑ k ∈ U, β k ≠ 0) :
    C β₀ * Lagrange.nodal Finset.univ y -
        ∑ i, C (A i) * clearedResidueRow y β (positive i) (poles i) (active i) +
        X * clearedResidueRow y β ∅ ∅ U ≠ 0 := by
  have hzero (i : Fin n) (hi : 0 < (positive i).card) : A i = 0 := by
    apply hsupport i
    intro hiU
    rw [hpositive i hiU, Finset.card_empty] at hi
    omega
  have hhigh (i : Fin n) : (poles i).card + 1 < (positive i).card → A i = 0 :=
    fun hi ↦ hzero i (by omega)
  intro hz
  have hc := congrArg (fun p : L[X] ↦ p.coeff (Fintype.card (Fin n))) hz
  rw [clearedSchur_coeff_card y β β₀ positive poles active A U hdisj hhigh,
    coeff_zero] at hc
  have hsum : (∑ i ∈ Finset.univ.filter
      (fun i ↦ (positive i).card = (poles i).card + 1),
      A i * ∑ k ∈ active i, β k) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i (by have hh := (Finset.mem_filter.mp hi).2; omega), zero_mul]
  rw [hsum, sub_zero] at hc
  exact hβ hc

theorem adjoinPowerColumn_weighted_negative_det
    (z : L) (d : ℕ) (y η r A B : Fin n → L)
    (hzy : ∀ k, y k ≠ z) (S : Matrix (Fin n) (Fin n) L)
    (hA : S *ᵥ A = fun k ↦ y k * η k) (hB : S *ᵥ B = η) :
    (adjoinPowerColumn (z ^ d) η (fun i ↦ z ^ d * r i)
      (fun k ↦ (y k - z)⁻¹) S).det =
      z ^ d * (1 - r ⬝ᵥ A + z * (r ⬝ᵥ B)) *
        (∏ k, (y k - z)⁻¹) * S.det := by
  have hsolve (k : Fin n) : (y k - z)⁻¹ * (S *ᵥ (A - z • B)) k = η k := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hA, hB]
    change (y k - z)⁻¹ * (y k * η k - z * η k) = η k
    rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (hzy k)), one_mul]
  rw [adjoinPowerColumn_det (z ^ d) η _ _ (A - z • B) S hsolve]
  congr 2
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib]
  have hsum : (∑ i, r i * (z * B i)) = z * ∑ i, r i * B i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum,hsum]
  ring

theorem mem_activeInterval_zero_of_prefix
    {m : ℕ} (hm : m < n + 1) (hmpos : 0 < m)
    (δ : Fin (n + 1) → ℕ) (d : ℕ)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) (k : Fin (n + 1)) :
    k ∈ activeInterval δ 0 ↔ k.val < m := by
  constructor
  · intro hk
    rcases (mem_activeInterval _ _ _).mp hk with ⟨_, hbetween⟩
    by_contra hn
    have hh := hbetween ⟨m, hm⟩ hmpos (Nat.le_of_not_gt hn)
    rw [hδ 0 hmpos] at hh
    exact (not_le_of_gt hjump) hh
  · intro hk
    refine (mem_activeInterval _ _ _).mpr ⟨Fin.zero_le _, ?_⟩
    intro j hj hjk
    rw [hδ j (lt_of_le_of_lt hjk hk), hδ 0 hmpos]

theorem profile_first_column_of_prefix
    {m : ℕ} (hm : m < n + 1) (hmpos : 0 < m)
    (δ : Fin (n + 1) → ℕ) (d : ℕ) (σ : Fin (n + 1) → ℤ) (y β : Fin (n + 1) → L)
    (hδ : ∀ k, k.val < m → δ k = d) (hjump : d < δ ⟨m, hm⟩) (k : Fin (n + 1)) :
    profileNewtonMatrix δ σ y β k 0 = if k.val < m then y k ^ d else 0 := by
  rw [profileNewtonMatrix_first_column, hδ 0 hmpos]
  simp only [mem_activeInterval_zero_of_prefix hm hmpos δ d hδ hjump]

end PaperVerification.Fermion.Newton
