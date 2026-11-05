module
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
@[expose] public section
/-!
# Exact numerical bounds for the corrected boxes

These are the integer ceiling and degree calculations in Sections 5--7.
Every geometric premise is kept explicit. No contraction, positivity, or
box-containment conclusion is built into these purely numerical statements.
-/

namespace PaperVerification.ToricGeometry

/-- An integer ceiling correction with positive integral slope is bounded by
the nonnegative part of the deficit. -/
theorem ceil_div_le_positivePart (δ a : ℤ) (ha : 1 ≤ a) :
    Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ max δ 0 := by
  apply Int.ceil_le.mpr
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hmax0 : (0 : ℝ) ≤ (max δ 0 : ℤ) := by exact_mod_cast le_max_right δ 0
  have hmaxδ : (δ : ℝ) ≤ (max δ 0 : ℤ) := by exact_mod_cast le_max_left δ 0
  apply (div_le_iff₀ (show (0 : ℝ) < a by linarith)).mpr
  nlinarith [mul_nonneg hmax0 (sub_nonneg.mpr haR)]

/-- The ceiling supplies enough correction to repair the actual deficit. -/
theorem deficit_le_mul_ceil_div (δ a : ℤ) (ha : 1 ≤ a) :
    δ ≤ a * Int.ceil ((δ : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show (0 : ℤ) < a by omega)
  have h := (div_le_iff₀ haR).mp (Int.le_ceil ((δ : ℝ) / (a : ℝ)))
  have h' : (δ : ℝ) ≤ (a : ℝ) * (Int.ceil ((δ : ℝ) / (a : ℝ)) : ℝ) := by
    nlinarith
  exact_mod_cast h'

/-- For a strictly positive deficit the correction is a positive integer,
at most the deficit itself. -/
theorem positive_ceil_correction (δ a : ℤ) (hδ : 0 < δ) (ha : 1 ≤ a) :
    1 ≤ Int.ceil ((δ : ℝ) / (a : ℝ)) ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ δ ∧
      δ ≤ a * Int.ceil ((δ : ℝ) / (a : ℝ)) := by
  have hrepair := deficit_le_mul_ceil_div δ a ha
  have hupper := ceil_div_le_positivePart δ a ha
  rw [max_eq_left hδ.le] at hupper
  have hpos : 0 < Int.ceil ((δ : ℝ) / (a : ℝ)) := by
    by_contra h
    have hnonpos : Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 0 := le_of_not_gt h
    have hprod : a * Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by omega) hnonpos
    omega
  exact ⟨by omega, hupper, hrepair⟩

/-- The exact common-blowup displacement chosen for the parity boxes. -/
noncomputable def parityCorrection (r q d a : ℤ) : ℤ :=
  max (2 * (q - 1)) (max (Int.ceil (((2 * r - d : ℤ) : ℝ) / (a : ℝ))) 0)

/-- All bounds in Section 6.2, including the fiber-degree repair, for the
exact integer correction used by the paper. -/
theorem parityCorrection_bounds (n r q b d a : ℤ)
    (hqdim : 1 ≤ q) (hb : 0 ≤ b) (ha : 1 ≤ a)
    (hdim : n = r + q + b) (hlarge : n < 2 * r) (hd : n ≤ d) :
    0 ≤ parityCorrection r q d a ∧
      2 * (q - 1) ≤ parityCorrection r q d a ∧
      parityCorrection r q d a ≤ n - 2 * b - 2 ∧
      parityCorrection r q d a ≤ r + q - 2 ∧
      2 * r ≤ d + a * parityCorrection r q d a := by
  let c := Int.ceil (((2 * r - d : ℤ) : ℝ) / (a : ℝ))
  have hc : c ≤ 2 * r - n := by
    apply (ceil_div_le_positivePart (2 * r - d) a ha).trans
    exact max_le (by omega) (by omega)
  have hbase : 2 * (q - 1) ≤ parityCorrection r q d a :=
    le_max_left _ _
  have hct : c ≤ parityCorrection r q d a :=
    (le_max_left _ _).trans (le_max_right _ _)
  have ht0 : 0 ≤ parityCorrection r q d a :=
    (le_max_right _ _).trans (le_max_right _ _)
  have htupper : parityCorrection r q d a ≤ n - 2 * b - 2 := by
    unfold parityCorrection
    apply max_le
    · omega
    · apply max_le
      · dsimp [c] at hc
        omega
      · omega
  have hrepair := deficit_le_mul_ceil_div (2 * r - d) a ha
  have hproduct : a * c ≤ a * parityCorrection r q d a :=
    mul_le_mul_of_nonneg_left hct (by omega)
  exact ⟨ht0, hbase, htupper, by omega, by dsimp [c] at hproduct; omega⟩

/-- The exact displacement of the inner unit boxes in Section 7.3. -/
noncomputable def adjointCorrection (r q d coefficientSum a : ℤ) : ℤ :=
  max (2 * (q - 1))
    (q - 1 + Int.ceil (((2 * r + 1 - d - coefficientSum : ℤ) : ℝ) / (a : ℝ)))

/-- Bounds for an actually selected adjoint obstruction. The coefficient sum
is at least the number of negative rays because each coefficient is positive. -/
theorem adjointCorrection_bounds (n r q b d coefficientSum a : ℤ)
    (hq : 1 ≤ q) (hb : 0 ≤ b) (ha : 1 ≤ a)
    (hdim : n = r + q + b) (hd : n + 1 ≤ d)
    (hcoeff : q ≤ coefficientSum) (hselected : 0 < 2 * r + 1 - d - coefficientSum) :
    n < 2 * r ∧
      2 * (q - 1) ≤ adjointCorrection r q d coefficientSum a ∧
      adjointCorrection r q d coefficientSum a ≤ n - 2 * b - 2 ∧
      2 * r + 1 ≤ d + coefficientSum +
        a * (adjointCorrection r q d coefficientSum a + 1 - q) := by
  let δ := 2 * r + 1 - d - coefficientSum
  let c := Int.ceil ((δ : ℝ) / (a : ℝ))
  have hδ : 0 < δ := hselected
  have hc : c ≤ δ := (positive_ceil_correction δ a hδ ha).2.1
  have hrepair : δ ≤ a * c := deficit_le_mul_ceil_div δ a ha
  have hlarge : n < 2 * r := by omega
  have hbase : 2 * (q - 1) ≤ adjointCorrection r q d coefficientSum a :=
    le_max_left _ _
  have hct : q - 1 + c ≤ adjointCorrection r q d coefficientSum a :=
    le_max_right _ _
  have htupper : adjointCorrection r q d coefficientSum a ≤ n - 2 * b - 2 := by
    unfold adjointCorrection
    apply max_le
    · omega
    · change q - 1 + c ≤ _
      dsimp [δ] at hc
      omega
  have hproduct : a * c ≤
      a * (adjointCorrection r q d coefficientSum a + 1 - q) :=
    mul_le_mul_of_nonneg_left (by omega) (by omega)
  exact ⟨hlarge, hbase, htupper, by dsimp [δ] at hrepair; omega⟩

/-- Equation (8): an activated correction is positive and obeys the precise
normal-coordinate budget. -/
theorem activatedCorrection_bounds (n r q A k δ a : ℤ)
    (hA : A ≤ r) (hk : 0 ≤ k) (hδ : 0 < δ) (ha : 1 ≤ a)
    (hbudget : δ ≤ 2 * A - 2 * k - n) :
    1 ≤ Int.ceil ((δ : ℝ) / (a : ℝ)) ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 2 * A - 2 * k - n ∧
      Int.ceil ((δ : ℝ) / (a : ℝ)) ≤ 2 * r - n := by
  obtain ⟨hpos, hup, _⟩ := positive_ceil_correction δ a hδ ha
  exact ⟨hpos, by omega, by omega⟩

/-- Proposition 5.2's one-positive-exceptional-divisor estimate. -/
theorem outside_box_one_positive_bound (n r q b s k τ : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2)
    (hk : k ≤ q - 1) (hτ : τ ≤ 2 * r - n) :
    0 ≤ n - 2 * (s - 1) - 2 * k - τ := by omega

/-- The complementary two-positive-divisor estimates force a positive
degree; no sign is lost by choosing one of the two estimates. -/
theorem outside_box_two_positive_bound (n b : ℝ) (degree : ℝ)
    (hfirst : 2 * b + 4 - n ≤ degree)
    (hsecond : n - 2 * b - 2 ≤ degree) : 1 ≤ degree := by linarith

/-- A parity center remains nef in the one-positive-divisor case. -/
theorem parity_center_one_positive_bound (n r q b s t : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2) (ht : t ≤ r + q - 2) :
    0 ≤ n - s - t := by omega

/-- The parity center has positive degree in the two-positive-divisor case. -/
theorem parity_center_two_positive_bound (n ri qi bi rj qj bj q' ti tj : ℤ)
    (hdi : n = ri + qi + bi) (hdj : n = rj + qj + bj)
    (hnegative : n - 1 - bi - bj ≤ q')
    (hti : ti ≤ ri + qi - 2) (htj : tj ≤ rj + qj - 2) :
    1 ≤ n - 2 + q' - ti - tj := by omega

/-- Twice the Section 7.4 one-positive-divisor lower bound, avoiding any
rounding of the half-canonical coefficient. -/
theorem adjoint_center_one_positive_bound (n b t : ℤ)
    (ht : t ≤ n - 2 * b - 2) :
    b ≤ 2 * (n + 1) - 3 * (b + 2) - 2 * t := by omega

/-- Twice the corresponding two-positive-divisor bound. -/
theorem adjoint_center_two_positive_bound (n bi bj q' ti tj : ℤ)
    (hnegative : n - 1 - bi - bj ≤ q')
    (hti : ti ≤ n - 2 * bi - 2) (htj : tj ≤ n - 2 * bj - 2) :
    n + bi + bj + 1 ≤ 2 * (n - 2) + 3 * q' - 2 * ti - 2 * tj := by omega

/-- The first center's one-positive-divisor degree estimate in Section 7.4. -/
theorem first_adjoint_center_one_positive_bound (n r q b s : ℤ)
    (hdim : n = r + q + b) (hs : s ≤ b + 2) :
    2 * r + b + 2 ≤ 2 * (n + 1) - s - 2 * (q - 1) := by omega

/-- Large disjoint contraction parameters force the strict codimension sum
used by both center estimates. -/
theorem large_loci_codimension_sum_lt (n ri qi bi rj qj bj : ℤ)
    (hdi : n = ri + qi + bi) (hdj : n = rj + qj + bj)
    (hbi : 0 ≤ bi) (hbj : 0 ≤ bj) (hri : n < 2 * ri) (hrj : n < 2 * rj) :
    qi + qj < n := by omega

end PaperVerification.ToricGeometry

