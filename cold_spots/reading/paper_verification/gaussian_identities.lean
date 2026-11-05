module
public import PaperVerification.GaussianDuplication
public import Mathlib.Tactic.FieldSimp
@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- The two congruence classes of the integers, without counting any point twice. -/
def integerParityEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun
    | .inl u => 2 * u
    | .inr u => 2 * u + 1
  invFun z := if Even z then .inl (z / 2) else .inr (z / 2)
  left_inv := by
    intro z
    cases z with
    | inl u =>
      have he : Even (2 * u) := ⟨u, by omega⟩
      simp only [he, ↓reduceIte, Sum.inl.injEq]
      omega
    | inr u =>
      have he : ¬Even (2 * u + 1) := by rw [Int.even_iff]; omega
      simp only [he, ↓reduceIte, Sum.inr.injEq]
      omega
  right_inv := by
    intro z
    dsimp only
    split_ifs with he
    · rw [Int.even_iff] at he
      dsimp
      omega
    · rw [Int.even_iff] at he
      dsimp
      omega

lemma gaussian_integer_even_term (α t : ℝ) (u : ℤ) :
    Real.exp (-α * ((integerParityEquiv (.inl u) : ℝ) - t) ^ 2) =
      Real.exp (-(4 * α) * ((u : ℝ) - t / 2) ^ 2) := by
  simp only [integerParityEquiv, Equiv.coe_fn_mk, Int.cast_mul, Int.cast_ofNat]
  congr 1
  ring

lemma gaussian_integer_odd_term (α t : ℝ) (u : ℤ) :
    Real.exp (-α * ((integerParityEquiv (.inr u) : ℝ) - t) ^ 2) =
      Real.exp (-(4 * α) * ((u : ℝ) - (t - 1) / 2) ^ 2) := by
  simp only [integerParityEquiv, Equiv.coe_fn_mk, Int.cast_mul, Int.cast_ofNat,
    Int.cast_add, Int.cast_one]
  congr 1
  ring

theorem gaussian_split {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t = gaussian (4 * α) (t / 2) + gaussian (4 * α) ((t - 1) / 2) := by
  have h4 : 0 < 4 * α := mul_pos (by norm_num) hα
  have he : HasSum (fun u : ℤ ↦
      Real.exp (-α * ((integerParityEquiv (.inl u) : ℝ) - t) ^ 2))
      (gaussian (4 * α) (t / 2)) := by
    simpa only [gaussian_integer_even_term] using
      hasSum_gaussian h4 (t / 2)
  have ho : HasSum (fun u : ℤ ↦
      Real.exp (-α * ((integerParityEquiv (.inr u) : ℝ) - t) ^ 2))
      (gaussian (4 * α) ((t - 1) / 2)) := by
    simpa only [gaussian_integer_odd_term] using
      hasSum_gaussian h4 ((t - 1) / 2)
  exact ((integerParityEquiv.hasSum_iff
    (f := fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2))).mp (he.sum ho)).tsum_eq

theorem alternatingGaussian_split {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t =
      gaussian (4 * α) (t / 2) - gaussian (4 * α) ((t - 1) / 2) := by
  have h4 : 0 < 4 * α := mul_pos (by norm_num) hα
  have hsignEven (u : ℤ) : paritySign (integerParityEquiv (.inl u)) = 1 := by
    have h : Even (2 * u) := ⟨u, by ring⟩
    change (if Even (2 * u) then (1 : ℝ) else -1) = 1
    simp only [h, ite_true]
  have hsignOdd (u : ℤ) : paritySign (integerParityEquiv (.inr u)) = -1 := by
    have h : ¬Even (2 * u + 1) := by rw [Int.even_iff]; omega
    change (if Even (2 * u + 1) then (1 : ℝ) else -1) = -1
    simp only [h, ite_false]
  let f : ℤ → ℝ := fun z ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)
  have he : HasSum (fun u : ℤ ↦ f (integerParityEquiv (.inl u)))
      (gaussian (4 * α) (t / 2)) := by
    simpa only [f, hsignEven, one_mul, gaussian_integer_even_term] using
      hasSum_gaussian h4 (t / 2)
  have ho : HasSum (fun u : ℤ ↦ f (integerParityEquiv (.inr u)))
      (-gaussian (4 * α) ((t - 1) / 2)) := by
    simpa only [f, hsignOdd, neg_one_mul, gaussian_integer_odd_term] using
      (hasSum_gaussian h4 ((t - 1) / 2)).neg
  have hs := (integerParityEquiv.hasSum_iff (f := f)).mp (he.sum ho)
  simpa only [sub_eq_add_neg] using (hasSum_alternatingGaussian hα t).unique hs

theorem gaussian_half_eq_twice_quarter {α : ℝ} (hα : 0 < α) :
    gaussian α (1 / 2) = 2 * gaussian (4 * α) (1 / 4) := by
  rw [gaussian_split hα]
  norm_num
  rw [gaussian_even]
  ring

lemma gaussian_pair_general_even (α t s : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inl p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inl p)).2 : ℝ) - s) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t + s) / 2) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (t - s) / 2) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma gaussian_pair_general_odd (α t s : ℝ) (p : ℤ × ℤ) :
    Real.exp (-α * (((pairParityEquiv (.inr p)).1 : ℝ) - t) ^ 2) *
      Real.exp (-α * (((pairParityEquiv (.inr p)).2 : ℝ) - s) ^ 2) =
    Real.exp (-(2 * α) * ((p.1 : ℝ) - (t + s - 1) / 2) ^ 2) *
      Real.exp (-(2 * α) * ((p.2 : ℝ) - (t - s - 1) / 2) ^ 2) := by
  simp only [pairParityEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Addition formula obtained from a bijection of the two-dimensional integer lattice. -/
theorem gaussian_addition {α : ℝ} (hα : 0 < α) (t s : ℝ) :
    gaussian α t * gaussian α s =
      gaussian (2 * α) ((t + s) / 2) * gaussian (2 * α) ((t - s) / 2) +
      gaussian (2 * α) ((t + s - 1) / 2) * gaussian (2 * α) ((t - s - 1) / 2) := by
  let f : ℤ × ℤ → ℝ := fun p ↦
    Real.exp (-α * ((p.1 : ℝ) - t) ^ 2) * Real.exp (-α * ((p.2 : ℝ) - s) ^ 2)
  have h2 : 0 < 2 * α := mul_pos (by norm_num) hα
  have he : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inl p)))
      (gaussian (2 * α) ((t + s) / 2) * gaussian (2 * α) ((t - s) / 2)) := by
    simpa only [f, gaussian_pair_general_even] using
      hasSum_gaussian_pair h2 h2 ((t + s) / 2) ((t - s) / 2)
  have ho : HasSum (fun p : ℤ × ℤ ↦ f (pairParityEquiv (.inr p)))
      (gaussian (2 * α) ((t + s - 1) / 2) *
        gaussian (2 * α) ((t - s - 1) / 2)) := by
    simpa only [f, gaussian_pair_general_odd] using
      hasSum_gaussian_pair h2 h2 ((t + s - 1) / 2) ((t - s - 1) / 2)
  exact (hasSum_gaussian_pair hα hα t s).unique
    ((pairParityEquiv.hasSum_iff (f := f)).mp (he.sum ho))

/-- Equation (3) of the cold-spots manuscript. -/
theorem gaussian_shift_product {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t * gaussian α (t - 1 / 2) =
      gaussian (2 * α) (1 / 4) * gaussian (α / 2) (2 * t - 1 / 2) := by
  rw [gaussian_addition hα]
  have hs := gaussian_split (half_pos hα) (2 * t - 1 / 2)
  have h₁ : (t + (t - 1 / 2)) / 2 = t - 1 / 4 := by ring
  have h₂ : (t - (t - 1 / 2)) / 2 = (1 / 4 : ℝ) := by ring
  have h₃ : (t + (t - 1 / 2) - 1) / 2 = t - 3 / 4 := by ring
  have h₄ : (t - (t - 1 / 2) - 1) / 2 = -(1 / 4 : ℝ) := by ring
  rw [h₁, h₂, h₃, h₄, gaussian_even]
  rw [show 4 * (α / 2) = 2 * α by ring,
    show (2 * t - 1 / 2) / 2 = t - 1 / 4 by ring,
    show (2 * t - 1 / 2 - 1) / 2 = t - 3 / 4 by ring] at hs
  rw [hs]
  ring

theorem gaussian_diagonal_sum {α : ℝ} (hα : 0 < α) (t : ℝ) :
    gaussian α t ^ 2 + gaussian α (t - 1 / 2) ^ 2 =
      gaussian (α / 2) 0 * gaussian (α / 2) (2 * t) := by
  rw [gaussian_duplication hα, gaussian_duplication hα]
  have hp : gaussian (2 * α) (t - 1 / 2 - 1 / 2) = gaussian (2 * α) t := by
    have h := gaussian_one_period (2 * α) (t - 1)
    rw [show t - 1 + 1 = t by ring] at h
    rw [show t - 1 / 2 - 1 / 2 = t - 1 by ring]
    exact h.symm
  rw [hp]
  have hs0 := gaussian_split (half_pos hα) 0
  have hst := gaussian_split (half_pos hα) (2 * t)
  norm_num at hs0
  rw [show 4 * (α / 2) = 2 * α by ring, gaussian_even] at hs0
  rw [show 4 * (α / 2) = 2 * α by ring,
    show 2 * t / 2 = t by ring,
    show (2 * t - 1) / 2 = t - 1 / 2 by ring] at hst
  rw [hs0, hst]
  ring

theorem gaussian_constant_quadratics {α : ℝ} (hα : 0 < α) :
    gaussian α 0 ^ 2 = gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2 ∧
    alternatingGaussian α 0 ^ 2 =
      gaussian (2 * α) 0 ^ 2 - gaussian (2 * α) (1 / 2) ^ 2 ∧
    gaussian α (1 / 2) ^ 2 = 2 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2) := by
  have ha := gaussian_duplication hα 0
  have hb := alternatingGaussian_duplication hα 0
  have hc := gaussian_duplication hα (1 / 2)
  norm_num at ha hb hc
  rw [gaussian_even] at ha hb
  constructor
  · nlinarith [ha]
  constructor
  · nlinarith [hb]
  · nlinarith [hc]

/-- Jacobi's quartic identity in the Gaussian normalization of the paper. -/
theorem gaussian_constant_quartic {α : ℝ} (hα : 0 < α) :
    gaussian α 0 ^ 4 = alternatingGaussian α 0 ^ 4 + gaussian α (1 / 2) ^ 4 := by
  obtain ⟨ha, hb, hc⟩ := gaussian_constant_quadratics hα
  calc
    gaussian α 0 ^ 4 = (gaussian α 0 ^ 2) ^ 2 := by ring
    _ = (gaussian (2 * α) 0 ^ 2 + gaussian (2 * α) (1 / 2) ^ 2) ^ 2 := by rw [ha]
    _ = (gaussian (2 * α) 0 ^ 2 - gaussian (2 * α) (1 / 2) ^ 2) ^ 2 +
        (2 * gaussian (2 * α) 0 * gaussian (2 * α) (1 / 2)) ^ 2 := by ring
    _ = alternatingGaussian α 0 ^ 4 + gaussian α (1 / 2) ^ 4 := by rw [← hb, ← hc]; ring

end PaperVerification.ColdSpots
