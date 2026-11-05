module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast

@[expose] public section
noncomputable section

/-!
Algebraic lemmas for Section 7 of Volume polynomials and the Heine–Shephard problem.
This file does not assert the geometric realization theorem or the natural-boundary theorem.
-/

namespace VolumePolynomials.Holonomy

/-- The return map in equation (7.1), expressed in planar coordinates. -/
def returnMap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -p.1 + (2 / 3 : ℝ) * p.2)

/-- The positive quadratic form preserved by the return map, equation (7.9). -/
def preservedForm (p : ℝ × ℝ) : ℝ := p.1 ^ 2 - (2 / 3 : ℝ) * p.1 * p.2 + p.2 ^ 2

theorem preservedForm_eq_squares (p : ℝ × ℝ) :
    preservedForm p = (p.1 - p.2 / 3)^2 + (8 / 9 : ℝ) * p.2^2 := by
  dsimp [preservedForm]
  ring

theorem preservedForm_nonneg (p : ℝ × ℝ) : 0 ≤ preservedForm p := by
  rw [preservedForm_eq_squares]
  positivity

theorem preservedForm_eq_zero_iff (p : ℝ × ℝ) : preservedForm p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [preservedForm_eq_squares] at h
    have hy : p.2 = 0 := by nlinarith [sq_nonneg (p.1 - p.2 / 3), sq_nonneg p.2]
    have hx : p.1 = 0 := by simpa [hy] using h
    exact Prod.ext hx hy
  · rintro rfl
    norm_num [preservedForm]

theorem preservedForm_pos {p : ℝ × ℝ} (hp : p ≠ 0) : 0 < preservedForm p := by
  exact lt_of_le_of_ne (preservedForm_nonneg p)
    (fun h => hp ((preservedForm_eq_zero_iff p).mp h.symm))

theorem returnMap_preserves (p : ℝ × ℝ) :
    preservedForm (returnMap p) = preservedForm p := by
  dsimp [returnMap, preservedForm]
  ring

/-- `I - lam M` has positive determinant for every real parameter lam. -/
theorem fixed_translation_determinant_pos (lam : ℝ) :
    0 < 1 - (2 / 3 : ℝ) * lam + lam ^ 2 := by
  nlinarith [sq_nonneg (lam - 1/3)]

/-- Integral recurrence obtained from `3 M`; `b(n+1)` has no factors of three. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * b (n + 1) - 9 * b n

@[simp] theorem b_zero : b 0 = 0 := rfl
@[simp] theorem b_one : b 1 = 1 := rfl
@[simp] theorem b_recurrence (n : ℕ) : b (n + 2) = 2 * b (n + 1) - 9 * b n := rfl

theorem b_mod_three (n : ℕ) : (b (n + 1) : ZMod 3) = (2 : ZMod 3)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 1 = n + 2 by omega, b_recurrence]
      push_cast
      rw [show (9 : ZMod 3) = 0 by decide, zero_mul, sub_zero, ih, pow_succ]
      ring

theorem b_succ_ne_zero (n : ℕ) : b (n + 1) ≠ 0 := by
  intro h
  have hm := b_mod_three n
  rw [h] at hm
  simp only [Int.cast_zero] at hm
  have hunit : IsUnit (2 : ZMod 3) := ⟨⟨2, 2, by decide, by decide⟩, rfl⟩
  exact (hunit.pow n).ne_zero hm.symm

/-- The return map bundled as a continuous linear map. -/
def returnContinuous : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) where
  toFun := returnMap
  map_add' := by
    intro p q
    ext <;> simp only [returnMap, Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' := by
    intro c p
    ext <;> simp only [returnMap, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      RingHom.id_apply] <;> ring
  cont := continuous_snd.prodMk
    (continuous_fst.neg.add (continuous_const.mul continuous_snd))

@[simp] theorem returnContinuous_apply (p : ℝ × ℝ) : returnContinuous p = returnMap p := rfl

/-- Orbit of the generating vector e₁ under the actual matrix M. -/
def orbit : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => returnMap (orbit n)

@[simp] theorem orbit_zero : orbit 0 = (1, 0) := rfl
@[simp] theorem orbit_succ (n : ℕ) : orbit (n + 1) = returnMap (orbit n) := rfl

theorem orbit_form (n : ℕ) : preservedForm (orbit n) = 1 := by
  induction n with
  | zero => norm_num [orbit, preservedForm]
  | succ n ih => rw [orbit_succ, returnMap_preserves, ih]

theorem orbit_norm_le (n : ℕ) : ‖orbit n‖ ≤ 2 := by
  have hq := orbit_form n
  have hx : (8/9 : ℝ) * (orbit n).1^2 ≤ preservedForm (orbit n) := by
    dsimp [preservedForm]
    nlinarith [sq_nonneg ((orbit n).2 - (orbit n).1/3)]
  have hy : (8/9 : ℝ) * (orbit n).2^2 ≤ preservedForm (orbit n) := by
    dsimp [preservedForm]
    nlinarith [sq_nonneg ((orbit n).1 - (orbit n).2/3)]
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

theorem orbit_eq_rational (n : ℕ) :
    orbit (n + 1) =
      (-3 * (b n : ℝ) / (3 : ℝ)^n, -(b (n + 1) : ℝ) / (3 : ℝ)^n) := by
  induction n with
  | zero => norm_num [orbit, returnMap, b]
  | succ n ih =>
      rw [orbit_succ, ih]
      ext <;> simp only [returnMap, Prod.fst, Prod.snd]
      · rw [pow_succ]
        field_simp
      · rw [show n + 1 + 1 = n + 2 by omega, b_recurrence, pow_succ]
        push_cast
        field_simp
        ring

theorem orbit_succ_snd_ne_zero (n : ℕ) : (orbit (n + 1)).2 ≠ 0 := by
  rw [orbit_eq_rational]
  dsimp
  exact div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast b_succ_ne_zero n))
    (pow_ne_zero n (by norm_num))

/-- The standard oriented determinant on the plane. -/
def det (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem det_returnMap (p q : ℝ × ℝ) :
    det (returnMap p) (returnMap q) = det p q := by
  dsimp [returnMap, det]
  ring

theorem det_orbit_add (i n : ℕ) : det (orbit i) (orbit (i + n)) = (orbit n).2 := by
  induction i with
  | zero => simp [det, orbit_zero]
  | succ i ih =>
      rw [show i + 1 + n = (i + n) + 1 by omega, orbit_succ, orbit_succ,
        det_returnMap, ih]

theorem det_orbit_ne_zero {i j : ℕ} (hij : i ≠ j) : det (orbit i) (orbit j) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    simpa [Nat.add_assoc] using
      (show det (orbit i) (orbit (i + (n + 1))) ≠ 0 by
        rw [det_orbit_add]
        exact orbit_succ_snd_ne_zero n)
  · have hswap : det (orbit j) (orbit i) ≠ 0 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      simpa [Nat.add_assoc] using
        (show det (orbit j) (orbit (j + (n + 1))) ≠ 0 by
          rw [det_orbit_add]
          exact orbit_succ_snd_ne_zero n)
    intro h
    apply hswap
    dsimp [det] at *
    linarith

#print axioms returnMap_preserves
#print axioms b_succ_ne_zero
#print axioms det_orbit_ne_zero

end VolumePolynomials.Holonomy
