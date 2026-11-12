module

public import ToricPower.GridSaturation

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

def IsSignPattern (e : Fin s → ℤ) : Prop := ∀ i, e i = 0 ∨ e i = -1

def patternCoefficient (e : Fin s → ℤ) (x : Fin s → ℝ) : Fin s → ℤ :=
  fun i => if e i = 0 then ⌊x i⌋ else ⌈x i⌉ - 1

def thomsenClasses (A : Matrix (Fin s) (Fin n) ℤ) (e : Fin s → ℤ) :
    Set (DivisorClass A) :=
  Set.range (fun x : Fin n → ℝ => divisorClass A (patternCoefficient e (realRayMap A x)))

def universalDenominator (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  rayPeriod A * dimensionDenominator n

lemma universalDenominator_pos (A : Matrix (Fin s) (Fin n) ℤ) :
    0 < universalDenominator A :=
  Nat.mul_pos (rayPeriod_pos A) (dimensionDenominator_pos n)

lemma patternCoefficient_eq_iff (e a : Fin s → ℤ) (x : Fin s → ℝ) :
    patternCoefficient e x = a ↔
      ∀ i, if e i = 0 then (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1
        else (a i : ℝ) < x i ∧ x i ≤ (a i : ℝ) + 1 := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  by_cases he : e i = 0
  · simp [patternCoefficient, he, Int.floor_eq_iff]
  · simp only [patternCoefficient, he, if_false]
    have hh : ⌈x i⌉ - 1 = a i ↔ ⌈x i⌉ = a i + 1 := by omega
    rw [hh, Int.ceil_eq_iff]
    push_cast
    simp

lemma patternCoefficient_sub_int (e d : Fin s → ℤ) (x : Fin s → ℝ) :
    patternCoefficient e (x - fun i => (d i : ℝ)) = patternCoefficient e x - d := by
  ext i
  by_cases he : e i = 0
  · simp [patternCoefficient, he, Int.floor_sub_intCast]
  · simp [patternCoefficient, he, Int.ceil_sub_intCast]
    ring

lemma realRayMap_sub (A : Matrix (Fin s) (Fin n) ℤ) (x y : Fin n → ℝ) :
    realRayMap A (x - y) = realRayMap A x - realRayMap A y :=
  Matrix.mulVec_sub _ _ _

lemma realRayMap_smul (A : Matrix (Fin s) (Fin n) ℤ) (t : ℝ) (x : Fin n → ℝ) :
    realRayMap A (t • x) = t • realRayMap A x := Matrix.mulVec_smul _ _ _

lemma divisorClass_sub_rayMap (A : Matrix (Fin s) (Fin n) ℤ)
    (a : Fin s → ℤ) (u : Fin n → ℤ) :
    divisorClass A (a - rayMap A u) = divisorClass A a := by
  change Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.mk_sub]
  change divisorClass A a - divisorClass A (rayMap A u) = divisorClass A a
  rw [divisorClass_rayMap A u, sub_zero]

/-- The two boundary conventions are exactly the two offset floors on an
integral power-map grid, including every negative boundary value. -/
theorem patternCoefficient_on_grid (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) (ell : ℕ) (hell : 0 < ell)
    (z : Fin n → ℤ) :
    patternCoefficient e (realRayMap A ((ell : ℝ)⁻¹ • (fun j => (z j : ℝ)))) =
      powerCoefficient A e (ell : ℤ) z := by
  apply (patternCoefficient_eq_iff _ _ _).mpr
  intro i
  have hp : (0 : ℝ) < ell := by exact_mod_cast hell
  have hpZ : (0 : ℤ) < ell := by exact_mod_cast hell
  have hb := (powerCoefficient_eq_iff A e (powerCoefficient A e ell z) ell hpZ z).mp rfl i
  have hr : (ell : ℝ) * (powerCoefficient A e ell z i : ℝ) ≤
      (e i : ℝ) + (rayMap A z i : ℝ) ∧
      (e i : ℝ) + (rayMap A z i : ℝ) ≤
        (ell : ℝ) * ((powerCoefficient A e ell z i : ℝ) + 1) - 1 := by
    exact_mod_cast hb
  rw [realRayMap_smul]
  simp only [Pi.smul_apply, smul_eq_mul, realRayMap_integer]
  rcases he i with hi | hi
  · rw [if_pos hi]
    rw [hi] at hr
    norm_num at hr
    constructor
    · have h := (le_div_iff₀ hp).mpr (show
          (powerCoefficient A e ell z i : ℝ) * ell ≤ (rayMap A z i : ℝ) by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using h
    · have h := (div_lt_iff₀ hp).mpr (show (rayMap A z i : ℝ) <
          ((powerCoefficient A e ell z i : ℝ) + 1) * ell by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using h
  · have hi0 : e i ≠ 0 := by omega
    rw [if_neg hi0]
    rw [hi] at hr
    norm_num at hr
    constructor
    · have h := (lt_div_iff₀ hp).mpr (show
          (powerCoefficient A e ell z i : ℝ) * ell < (rayMap A z i : ℝ) by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using h
    · have h := (div_le_iff₀ hp).mpr (show (rayMap A z i : ℝ) ≤
          ((powerCoefficient A e ell z i : ℝ) + 1) * ell by nlinarith)
      simpa [div_eq_mul_inv, mul_comm] using h

def roundingStrictRows (e : Fin s → ℤ) : Set (RawRow n s) :=
  {j | match j.2 with
    | Sum.inl _ => False
    | Sum.inr i => if e i = 0 then j.1 = true else j.1 = false}

lemma pattern_cell_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (e a : Fin s → ℤ) (x : Fin n → ℝ)
    (hbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1) :
    patternCoefficient e (realRayMap A x) = a ↔
      x ∈ slopePolytope A a ∧
      ∀ j ∈ roundingStrictRows e,
        matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)) j x <
          (rawSlope a j : ℝ) := by
  rw [patternCoefficient_eq_iff]
  constructor
  · intro h
    constructor
    · rw [mem_slopePolytope_iff]
      refine ⟨hbox, ?_⟩
      intro i
      by_cases he : e i = 0
      · have hi := h i
        simp only [he, if_true] at hi
        exact ⟨hi.1, hi.2.le⟩
      · have hi := h i
        simp only [he, if_false] at hi
        exact ⟨hi.1.le, hi.2⟩
    · rintro ⟨sgn, row⟩ hj
      cases row with
      | inl j => exact False.elim (by simpa [roundingStrictRows] using hj)
      | inr i =>
        by_cases he : e i = 0
        · have hs : sgn = true := by simpa [roundingStrictRows, he] using hj
          subst sgn
          have hi := h i
          simp only [he, if_true] at hi
          simpa only [matrixRows_raw_positive_ray, rawSlope,
            Int.cast_add, Int.cast_one] using hi.2
        · have hs : sgn = false := by simpa [roundingStrictRows, he] using hj
          subst sgn
          have hi := h i
          simp only [he, if_false] at hi
          simp only [matrixRows_raw_negative_ray, rawSlope, Int.cast_neg]
          linarith
  · rintro ⟨hx, hs⟩ i
    have hb := ((mem_slopePolytope_iff A a x).mp hx).2 i
    by_cases he : e i = 0
    · rw [if_pos he]
      have ht := hs (true, Sum.inr i) (by simp [roundingStrictRows, he])
      simp only [matrixRows_raw_positive_ray, rawSlope, Int.cast_add, Int.cast_one] at ht
      exact ⟨hb.1, ht⟩
    · rw [if_neg he]
      have ht := hs (false, Sum.inr i) (by simp [roundingStrictRows, he])
      simp only [matrixRows_raw_negative_ray, rawSlope, Int.cast_neg] at ht
      exact ⟨by linarith, hb.2⟩

/-- Every nonempty rounded arrangement cell in the coordinate cube contains
a point on the exact R-grid of Lemma 6.1. -/
theorem rounding_cell_grid (A : Matrix (Fin s) (Fin n) ℤ)
    (e a : Fin s → ℤ) (he : IsSignPattern e) (x : Fin n → ℝ)
    (hbox : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hx : patternCoefficient e (realRayMap A x) = a) :
    ∃ z : Fin n → ℤ, powerCoefficient A e (universalDenominator A : ℤ) z = a := by
  have hcell := (pattern_cell_iff A e a x hbox).mp hx
  have hxv : x ∈ convexHull ℝ (slopeVertices A a : Set (Fin n → ℝ)) := by
    rw [← slopePolytope_eq_convexHull]
    exact hcell.1
  obtain ⟨y, hyv, hyint, hystrict⟩ := exists_grid_point_preserving_strict_faces
    (slopeVertices A a) x hxv (rayPeriod A) (slope_vertex_denominator A a)
    (matrixRows ((rawConstraintMatrix A).map (Int.castRingHom ℝ)))
    (fun j => (rawSlope a j : ℝ)) (roundingStrictRows e)
    (by
      intro v hv
      have hQ : v ∈ slopePolytope A a := by
        rw [slopePolytope_eq_convexHull]
        exact subset_convexHull ℝ _ hv
      exact hQ)
    hcell.2
  have hyQ : y ∈ slopePolytope A a := by
    rw [slopePolytope_eq_convexHull]
    exact hyv
  have hybox := ((mem_slopePolytope_iff A a y).mp hyQ).1
  have hyr := (pattern_cell_iff A e a y hybox).mpr ⟨hyQ, hystrict⟩
  obtain ⟨z, hz⟩ := hyint
  have hzfun : (fun j => (z j : ℝ)) = (universalDenominator A : ℝ) • y :=
    funext hz
  have hR : (universalDenominator A : ℝ) ≠ 0 := by
    exact_mod_cast (universalDenominator_pos A).ne'
  have hy : y = (universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ)) := by
    rw [hzfun, smul_smul, inv_mul_cancel₀ hR, one_smul]
  rw [hy, patternCoefficient_on_grid A e he _ (universalDenominator_pos A)] at hyr
  exact ⟨z, hyr⟩

end ToricPower
