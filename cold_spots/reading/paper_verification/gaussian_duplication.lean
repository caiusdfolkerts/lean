module
public import PaperVerification.GaussianProduct
public import Lean.Elab.Tactic.Omega
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- Half-sum/half-difference coordinates, with an explicit parity tag. -/
def pairParityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun
    | .inl (u, v) => (u + v, u - v)
    | .inr (u, v) => (u + v + 1, u - v)
  invFun p := if Even (p.1 + p.2) then
    .inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2) else
    .inr ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
  left_inv := by
    intro s
    cases s with
    | inl p =>
      rcases p with ⟨u, v⟩
      have he : Even (u + v + (u - v)) := by
        exact ⟨u, by omega⟩
      simp only [he, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq]
      omega
    | inr p =>
      rcases p with ⟨u, v⟩
      have he : ¬Even (u + v + 1 + (u - v)) := by
        rw [Int.even_iff]
        omega
      simp only [he, ↓reduceIte, Sum.inr.injEq, Prod.mk.injEq]
      omega
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega
    · rw [Int.even_iff] at he
      apply Prod.ext <;> dsimp <;> omega

lemma hasSum_gaussian_pair {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t s : ℝ) :
    HasSum (fun p : ℤ × ℤ ↦ Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-β * ((p.2 : ℝ) - s) ^ 2)) (gaussian α t * gaussian β s) :=
  (hasSum_gaussian hα t).mul (hasSum_gaussian hβ s)
    (summable_mul_of_summable_norm (summable_gaussian hα t).norm
      (summable_gaussian hβ s).norm)

lemma hasSum_alternatingGaussian_pair {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t s : ℝ) :
    HasSum (fun p : ℤ × ℤ ↦
      (paritySign p.1 * Real.exp (-α * ((p.1 : ℝ) - t) ^ 2)) *
      (paritySign p.2 * Real.exp (-β * ((p.2 : ℝ) - s) ^ 2)))
      (alternatingGaussian α t * alternatingGaussian β s) :=
  (hasSum_alternatingGaussian hα t).mul
    (hasSum_alternatingGaussian hβ s)
    (summable_mul_of_summable_norm (summable_alternatingGaussian hα t).norm
      (summable_alternatingGaussian hβ s).norm)

lemma gaussian_pair_even (α t : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - t) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-(2 * α) * (p.2 : ℝ) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma gaussian_pair_odd (α t : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - t) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t - 1 / 2)) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (-(1 / 2))) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The first duplication formula in Equation (1), as an identity of convergent series. -/
theorem gaussian_duplication {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 = gaussian (2 * α) 0 * gaussian (2 * α) t +
      gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) * Real.exp (-α * ((p.2 : ℝ) - t) ^ 2)
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) t * gaussian (2 * α) 0) := by
    simpa only [f, gaussian_pair_even, sub_zero] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα) t 0
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2))) := by
    simpa only [f, gaussian_pair_odd] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα)
        (t - 1 / 2) (-(1 / 2))
  have hs : HasSum f (gaussian (2 * α) t * gaussian (2 * α) 0 +
      gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2))) :=
    (pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  have hu := (hasSum_gaussian_pair hα hα t t).unique hs
  rw [gaussian_even] at hu
  simpa only [pow_two, mul_comm] using hu

lemma paritySign_pair_even (p : ℤ × ℤ) :
    paritySign (pairParityEquiv (.inl p)).1 *
      paritySign (pairParityEquiv (.inl p)).2 = 1 := by
  rw [← paritySign_add]
  have he : Even ((pairParityEquiv (.inl p)).1 + (pairParityEquiv (.inl p)).2) := by
    refine ⟨p.1, ?_⟩
    dsimp [pairParityEquiv]
    omega
  simp [paritySign, he]

lemma paritySign_pair_odd (p : ℤ × ℤ) :
    paritySign (pairParityEquiv (.inr p)).1 *
      paritySign (pairParityEquiv (.inr p)).2 = -1 := by
  rw [← paritySign_add]
  have he : ¬Even ((pairParityEquiv (.inr p)).1 + (pairParityEquiv (.inr p)).2) := by
    rw [Int.even_iff]
    dsimp [pairParityEquiv]
    omega
  simp [paritySign, he]

lemma alternating_pair_even (α t : ℝ) (p : ℤ × ℤ) :
    (paritySign (pairParityEquiv (.inl p)).1 *
      Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2)) *
    (paritySign (pairParityEquiv (.inl p)).2 *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - t) ^ 2)) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - t) ^ 2) *
      Real.exp (-(2 * α) * (p.2 : ℝ) ^ 2) := by
  rw [mul_mul_mul_comm, paritySign_pair_even, one_mul, gaussian_pair_even]

lemma alternating_pair_odd (α t : ℝ) (p : ℤ × ℤ) :
    (paritySign (pairParityEquiv (.inr p)).1 *
      Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2)) *
    (paritySign (pairParityEquiv (.inr p)).2 *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - t) ^ 2)) =
    -(Real.exp (-(2 * α) * ((p.1 : ℝ) - (t - 1 / 2)) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (-(1 / 2))) ^ 2)) := by
  rw [mul_mul_mul_comm, paritySign_pair_odd, neg_one_mul, gaussian_pair_odd]

/-- The alternating duplication formula in Equation (1). -/
theorem alternatingGaussian_duplication {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t ^ 2 = gaussian (2 * α) 0 * gaussian (2 * α) t -
      gaussian (2 * α) (1 / 2) * gaussian (2 * α) (t - 1 / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    (paritySign p.1 * Real.exp (-α * ((p.1 : ℝ) - t) ^ 2)) *
    (paritySign p.2 * Real.exp (-α * ((p.2 : ℝ) - t) ^ 2))
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) t * gaussian (2 * α) 0) := by
    simpa only [f, alternating_pair_even, sub_zero] using
      hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα) t 0
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (-(gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2)))) := by
    simpa only [f, alternating_pair_odd] using
      (hasSum_gaussian_pair (mul_pos (by norm_num) hα) (mul_pos (by norm_num) hα)
        (t - 1 / 2) (-(1 / 2))).neg
  have hs : HasSum f (gaussian (2 * α) t * gaussian (2 * α) 0 +
      -(gaussian (2 * α) (t - 1 / 2) * gaussian (2 * α) (-(1 / 2)))) :=
    (pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  have hu := (hasSum_alternatingGaussian_pair hα hα t t).unique hs
  rw [gaussian_even] at hu
  simpa only [pow_two, sub_eq_add_neg, mul_comm] using hu

end PaperVerification.ColdSpots
