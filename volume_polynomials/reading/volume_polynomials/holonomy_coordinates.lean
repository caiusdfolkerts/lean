module

public import VolumePolynomials.Holonomy
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

abbrev Plane := ℝ × ℝ

/-- Coordinate form of projection from the xy-plane to the xz-plane along v. -/
def transport01 : Plane ≃L[ℝ] Plane where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk continuous_snd.neg
  continuous_invFun := continuous_fst.prodMk continuous_snd.neg

/-- Coordinate form of projection from the xz-plane to the yz-plane along w. -/
def transport12 : Plane ≃L[ℝ] Plane where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' c p := by ext <;> simp
  continuous_toFun := continuous_fst.neg.prodMk continuous_snd
  continuous_invFun := continuous_fst.neg.prodMk continuous_snd

/-- Coordinate form of projection from the yz-plane to the xy-plane along z. -/
def transport20 : Plane ≃L[ℝ] Plane where
  toFun p := (-p.2, p.1 - (2 / 3 : ℝ) * p.2)
  invFun p := (p.2 - (2 / 3 : ℝ) * p.1, -p.1)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, RingHom.id_apply] <;> ring
  continuous_toFun := continuous_snd.neg.prodMk
    (continuous_fst.sub (continuous_const.mul continuous_snd))
  continuous_invFun := (continuous_snd.sub (continuous_const.mul continuous_fst)).prodMk
    continuous_fst.neg

@[simp] theorem transport01_apply (p : Plane) : transport01 p = (p.1, -p.2) := rfl
@[simp] theorem transport12_apply (p : Plane) : transport12 p = (-p.1, p.2) := rfl
@[simp] theorem transport20_apply (p : Plane) :
    transport20 p = (-p.2, p.1 - (2 / 3 : ℝ) * p.2) := rfl

@[simp] theorem transport_cycle (p : Plane) :
    transport20 (transport12 (transport01 p)) = returnMap p := by
  first
  | ext <;> simp [returnMap] <;> ring

/-- The unique center that absorbs an affine translation in the return equation.
The determinant is positive for every real parameter, not just the contracting
range used in Theorem 1.2. -/
def translationCenter (lam : ℝ) (q : Plane) : Plane :=
  (((1 - (2 / 3 : ℝ) * lam) * q.1 + lam * q.2) /
      (1 - (2 / 3 : ℝ) * lam + lam ^ 2),
    (-lam * q.1 + q.2) / (1 - (2 / 3 : ℝ) * lam + lam ^ 2))

theorem translationCenter_equation (lam : ℝ) (q : Plane) :
    translationCenter lam q - lam • returnMap (translationCenter lam q) = q := by
  first
  | have hd := ne_of_gt (fixed_translation_determinant_pos lam)
    have hd₃ : (3 - lam * 2 + lam ^ 2 * 3 : ℝ) ≠ 0 := by
      have hpos := fixed_translation_determinant_pos lam
      nlinarith
    ext <;> dsimp [translationCenter, returnMap] <;> field_simp [hd, hd₃] <;>
      ring_nf <;> field_simp [hd₃] <;> ring

theorem translationCenter_fixed (lam : ℝ) (q : Plane) :
    translationCenter lam q = q + lam • returnMap (translationCenter lam q) := by
  first
  | exact sub_eq_iff_eq_add.mp (translationCenter_equation lam q)

theorem translationCenter_unique (lam : ℝ) (q c : Plane)
    (hc : c - lam • returnMap c = q) : c = translationCenter lam q := by
  first
  | have hc₁ := congrArg Prod.fst hc
    have hc₂ := congrArg Prod.snd hc
    have ht := translationCenter_equation lam q
    have ht₁ := congrArg Prod.fst ht
    have ht₂ := congrArg Prod.snd ht
    dsimp [returnMap] at hc₁ hc₂ ht₁ ht₂
    have hd := ne_of_gt (fixed_translation_determinant_pos lam)
    have hx : lam * (c.1 - (translationCenter lam q).1) =
        lam ^ 2 * (c.2 - (translationCenter lam q).2) := by
      calc
        _ = lam * (lam * (c.2 - (translationCenter lam q).2)) := by
          congr 1
          linarith
        _ = _ := by ring
    have hy : (1 - (2 / 3 : ℝ) * lam + lam ^ 2) *
        (c.2 - (translationCenter lam q).2) = 0 := by
      nlinarith
    have hy' := (mul_eq_zero.mp hy).resolve_left hd
    have hcy := sub_eq_zero.mp hy'
    apply Prod.ext
    · rw [hcy] at hc₁
      linarith
    · exact hcy

/-- The final determinant distinguishes the four remaining sign patterns. -/
theorem final_calibration_signs {s t : ℝ} (hs : |s| = 1)
    (ht : |t| = (2 / 3 : ℝ)) (hd : |t - s - 1| = (4 / 3 : ℝ)) :
    s = 1 ∧ t = (2 / 3 : ℝ) := by
  first
  | rcases eq_or_eq_neg_of_abs_eq hs with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq ht with rfl | rfl <;>
      norm_num at hd
    all_goals norm_num

/-- Complete scalar sign calibration for Lemma 7.1 at τ = 2/3.

The conclusion supplies two coordinate reflections (the middle coordinate is
fixed) and three independent segment orientations.  The hypotheses are exactly
the absolute coordinates and absolute triple determinant read from the volume
tests.  The finite sign split exhausts all real solutions of those hypotheses.
-/
theorem calibration_signs
    (vy vz wx wy zx zy zz : ℝ)
    (hvy : |vy| = 1) (hvz : |vz| = 1)
    (hwx : |wx| = 1) (hwy : |wy| = 1)
    (hzx : |zx| = 1) (hzy : |zy| = (2 / 3 : ℝ)) (hzz : |zz| = 1)
    (hdet : |-wx * vy * zz + wx * vz * zy - zx * vz * wy| = (4 / 3 : ℝ)) :
    ∃ σ₁ σ₃ rv rw rz : ℝ,
      |σ₁| = 1 ∧ |σ₃| = 1 ∧ |rv| = 1 ∧ |rw| = 1 ∧ |rz| = 1 ∧
      rv * vy = 1 ∧ rv * σ₃ * vz = 1 ∧
      rw * σ₁ * wx = 1 ∧ rw * wy = 1 ∧
      rz * σ₁ * zx = 1 ∧ rz * zy = (2 / 3 : ℝ) ∧ rz * σ₃ * zz = 1 := by
  first
  | refine ⟨wx * wy, vy * vz, vy, wy, vy * vz * zz, ?_⟩
    rcases eq_or_eq_neg_of_abs_eq hvy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hvz with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hwx with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hwy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzx with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzy with rfl | rfl <;>
      rcases eq_or_eq_neg_of_abs_eq hzz with rfl | rfl <;>
      norm_num at hdet
    all_goals norm_num


end VolumePolynomials.Holonomy
