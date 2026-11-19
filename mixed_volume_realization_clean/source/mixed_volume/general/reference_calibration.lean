module

public import mixed_volume.general.automaton_words

/-! Simultaneous sign calibration for every reference segment in the general
alphabet construction.  The horizontal sign of each letter is linked to the
first letter by a literal mixed determinant, and the vertical signs are linked
to the identity reference. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.GeneralCalibration

open VolumePolynomials VolumePolynomials.Holonomy AutomatonWords
open scoped Pointwise

variable {s : ℕ}

def letterDirection (a : Fin s) : Space 3 := ![-((a.val : ℝ) + 1), -base s, 1]
def identityDirection : Space 3 := ![0, -1, 1]

theorem unit_square (x : ℝ) (hx : |x| = 1) : x * x = 1 := by
  nlinarith [sq_abs x]

theorem aligned_sign (u x b : ℝ) (hu : |u| = 1) (hx : |x| = b)
    (hb : 1 ≤ b) (h : |x - u| = b - 1) : u * x = b := by
  rcases eq_or_eq_neg_of_abs_eq hu with rfl | rfl
  · rcases eq_or_eq_neg_of_abs_eq hx with heq | heq
    · rw [heq]; ring
    · rw [heq] at h ⊢
      rw [abs_of_nonpos (by linarith : -b - 1 ≤ 0)] at h
      linarith
  · rcases eq_or_eq_neg_of_abs_eq hx with heq | heq
    · rw [heq] at h ⊢
      rw [abs_of_nonneg (by linarith : 0 ≤ b - -1)] at h
      linarith
    · rw [heq]; ring

theorem normalized_pair (x y z t : ℝ) (hz : |z| = 1) (ht : |t| = 1) :
    |z * x - t * y| = |x * t - z * y| := by
  rcases eq_or_eq_neg_of_abs_eq hz with rfl | rfl <;>
    rcases eq_or_eq_neg_of_abs_eq ht with rfl | rfl <;>
    apply (sq_eq_sq_iff_abs_eq_abs _ _).mp <;> ring

/-- One common volume-preserving coordinate reflection calibrates all letter
segments and the identity segment.  The hypotheses are precisely the absolute
coordinate and pair determinants visible in the complete cubic array. -/
theorem calibrate_vectors (hs : 0 < s) (v : Fin s → Space 3) (w : Space 3)
    (hx : ∀ a, |v a 0| = (a.val : ℝ) + 1)
    (hy : ∀ a, |v a 1| = base s)
    (hz : ∀ a, |v a 2| = 1)
    (hwx : w 0 = 0) (hwy : |w 1| = 1) (hwz : |w 2| = 1)
    (hvertical : ∀ a, |v a 1 * w 2 - v a 2 * w 1| = base s - 1)
    (hhorizontal : ∀ a, |v a 0 * v ⟨0, hs⟩ 2 - v a 2 * v ⟨0, hs⟩ 0| = (a.val : ℝ)) :
    ∃ g : Space 3 ≃L[ℝ] Space 3,
      |LinearMap.det g.toLinearMap| = 1 ∧
      (∀ k : Fin 3, ∃ t : ℝ, g (axis k) = t • axis k) ∧
      (∀ k : Fin 3, mapBody g.toContinuousLinearMap (centeredBody (axis k)) = centeredBody (axis k)) ∧
      (∀ a, mapBody g.toContinuousLinearMap (centeredBody (v a)) = centeredBody (letterDirection a)) ∧
      mapBody g.toContinuousLinearMap (centeredBody w) = centeredBody identityDirection := by
  let a₀ : Fin s := ⟨0, hs⟩
  let σ : Space 3 := ![-v a₀ 2 * v a₀ 0, -w 2 * w 1, 1]
  have hx₀ : |v a₀ 0| = 1 := by simpa only [a₀, Nat.cast_zero, zero_add] using hx a₀
  have hσ : ∀ k, |σ k| = 1 := by
    intro k
    fin_cases k <;> simp [σ, abs_mul, hz, hx₀, hwy, hwz]
  let g := coordinateReflection σ hσ
  have hvx (a : Fin s) : (v a₀ 2 * v a₀ 0) * (v a 2 * v a 0) = (a.val : ℝ) + 1 := by
    apply aligned_sign
    · rw [abs_mul, hz, hx₀, one_mul]
    · rw [abs_mul, hz, hx, one_mul]
    · have ha := Nat.cast_nonneg (α := ℝ) a.val
      linarith
    · rw [normalized_pair _ _ _ _ (hz a) (hz a₀), hhorizontal]
      ring
  have hvy (a : Fin s) : (w 2 * w 1) * (v a 2 * v a 1) = base s := by
    apply aligned_sign
    · rw [abs_mul, hwz, hwy, one_mul]
    · rw [abs_mul, hz, hy, one_mul]
    · dsimp [base]
      have hs0 := Nat.cast_nonneg (α := ℝ) s
      linarith
    · rw [normalized_pair _ _ _ _ (hz a) hwz, hvertical]
  have hv (a : Fin s) : (v a 2) • g (v a) = letterDirection a := by
    ext k
    fin_cases k
    · have h := hvx a
      change v a 2 * ((-v a₀ 2 * v a₀ 0) * v a 0) = -((a.val : ℝ) + 1)
      nlinarith [h]
    · have h := hvy a
      change v a 2 * ((-w 2 * w 1) * v a 1) = -base s
      nlinarith [h]
    · change v a 2 * (1 * v a 2) = 1
      rw [one_mul]
      exact unit_square _ (hz a)
  have hw : (w 2) • g w = identityDirection := by
    ext k
    fin_cases k
    · change w 2 * ((-v a₀ 2 * v a₀ 0) * w 0) = 0
      rw [hwx, mul_zero, mul_zero]
    · change w 2 * ((-w 2 * w 1) * w 1) = -1
      nlinarith [unit_square (w 2) hwz, unit_square (w 1) hwy]
    · change w 2 * (1 * w 2) = 1
      rw [one_mul]
      exact unit_square _ hwz
  refine ⟨g, coordinateReflection_abs_det σ hσ, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨σ k, coordinateReflection_basis σ hσ k⟩
  · intro k
    rw [map_centeredBody]
    change centeredBody (g (axis k)) = centeredBody (axis k)
    rw [show g (axis k) = σ k • axis k from coordinateReflection_basis σ hσ k]
    exact centeredBody_smul_sign (σ k) (hσ k) (axis k)
  · intro a
    rw [map_centeredBody]
    change centeredBody (g (v a)) = centeredBody (letterDirection a)
    exact (centeredBody_smul_sign (v a 2) (hz a) (g (v a))).symm.trans
      (congrArg centeredBody (hv a))
  · rw [map_centeredBody]
    change centeredBody (g w) = centeredBody identityDirection
    exact (centeredBody_smul_sign (w 2) hwz (g w)).symm.trans (congrArg centeredBody hw)

end MixedVolume.GeneralCalibration

end
