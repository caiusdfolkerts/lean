module
public import VolumePolynomials.PolynomialCoordinates
public import VolumePolynomials.SegmentVolume
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The literal ternary-cubic coefficient slice

The polynomial is exactly (3.1), with ordinary monomial coefficients. Its
zero pure terms and positive repeated terms force every realizing body to
have affine dimension two. The argument uses actual volume evaluations and
the general segment extrusion theorem; it does not assume degree/dimension
correspondence or a mixed-volume positivity axiom.
-/

open Set Module MvPolynomial
open scoped BigOperators Pointwise

namespace VolumePolynomials.CubicSlice

def polynomial (α s z : ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (3 * α) * X 0 ^ 2 * X 1 + C (3 * α) * X 0 ^ 2 * X 2 +
  C 3 * X 0 * X 1 ^ 2 + C 3 * X 1 ^ 2 * X 2 +
  C (3 * s) * X 0 * X 2 ^ 2 + C 3 * X 1 * X 2 ^ 2 +
  C (6 * z) * X 0 * X 1 * X 2

theorem polynomial_homogeneous (α s z : ℝ) : (polynomial α s z).IsHomogeneous 3 := by
  first
  | have h21 (a : ℝ) (i j : Fin 3) :
        (C a * X i ^ 2 * X j : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add, one_mul] using
        ((isHomogeneous_C (σ := Fin 3) a).mul
          ((isHomogeneous_X ℝ i).pow 2)).mul (isHomogeneous_X ℝ j)
    have h12 (a : ℝ) (i j : Fin 3) :
        (C a * X i * X j ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add, one_mul] using
        ((isHomogeneous_C (σ := Fin 3) a).mul
          (isHomogeneous_X ℝ i)).mul ((isHomogeneous_X ℝ j).pow 2)
    have h111 : (C (6 * z) * X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 3 := by
      simpa only [zero_add] using
        (((isHomogeneous_C (σ := Fin 3) (6 * z)).mul
          (isHomogeneous_X ℝ (0 : Fin 3))).mul (isHomogeneous_X ℝ (1 : Fin 3))).mul
          (isHomogeneous_X ℝ (2 : Fin 3))
    exact (((((h21 (3 * α) 0 1).add (h21 (3 * α) 0 2)).add (h12 3 0 1)).add
      (h21 3 1 2)).add (h12 (3 * s) 0 2)).add (h12 3 1 2) |>.add h111

def coefficients (α s z : ℝ) : Coefficients 3 3 :=
  coefficientsOfPolynomial (polynomial α s z)

def value (α s z : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  3 * α * t 0 ^ 2 * t 1 + 3 * α * t 0 ^ 2 * t 2 +
  3 * t 0 * t 1 ^ 2 + 3 * t 1 ^ 2 * t 2 +
  3 * s * t 0 * t 2 ^ 2 + 3 * t 1 * t 2 ^ 2 +
  6 * z * t 0 * t 1 * t 2

theorem evaluate_coefficients (α s z : ℝ) (t : Fin 3 → ℝ) :
    evaluate (coefficients α s z) t = value α s z t := by
  first
  | rw [coefficients, evaluate_eq_polynomial_eval,
      coefficientPolynomial_coefficientsOfPolynomial _ (polynomial_homogeneous α s z)]
    simp only [polynomial, value, map_add, map_mul, map_pow, eval_C, eval_X]

theorem realizes_iff (α s z : ℝ) (K : Fin 3 → Body 3) :
    Realizes K (coefficients α s z) ↔
      ∀ t : Fin 3 → ℝ, (∀ i, 0 ≤ t i) → volumeFunction K t = value α s z t := by
  first
  | simp only [Realizes, evaluate_coefficients, eq_comm]

theorem pure_volumes_zero {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (coefficients α s z)) (i : Fin 3) : bodyVolume (K i) = 0 := by
  first
  | have h := (realizes_iff α s z K).mp hK (Pi.single i 1) (by
      intro j
      by_cases hji : j = i <;> simp [Pi.single_apply, hji])
    rw [volumeFunction, weightedSum_single, one_smul] at h
    fin_cases i <;> simpa [value, Pi.single_apply] using h

theorem pair_volumes {α s z : ℝ} {K : Fin 3 → Body 3}
    (hK : Realizes K (coefficients α s z)) :
    bodyVolume (K 0 + K 1) = 3 * α + 3 ∧
    bodyVolume (K 0 + K 2) = 3 * α + 3 * s ∧
    bodyVolume (K 1 + K 2) = 6 := by
  first
  | have hvol := (realizes_iff α s z K).mp hK
    have h01 := hvol ![1, 1, 0] (by intro i; fin_cases i <;> norm_num)
    have h02 := hvol ![1, 0, 1] (by intro i; fin_cases i <;> norm_num)
    have h12 := hvol ![0, 1, 1] (by intro i; fin_cases i <;> norm_num)
    norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h01 h02 h12
    exact ⟨h01, h02, h12⟩

def nextBody : Fin 3 → Fin 3 := ![1, 2, 0]

theorem second_difference_positive {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z)) (i : Fin 3) :
    0 < bodyVolume (K (nextBody i) + (2 : ℝ) • K i) -
      2 * bodyVolume (K (nextBody i) + K i) + bodyVolume (K (nextBody i)) := by
  first
  | have hvol := (realizes_iff α s z K).mp hK
    obtain ⟨h01, h02, h12⟩ := pair_volumes hK
    have hzero := pure_volumes_zero hK
    fin_cases i
    · have h2 := hvol ![2, 1, 0] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 1 + (2 : ℝ) • K 0) -
        2 * bodyVolume (K 1 + K 0) + bodyVolume (K 1)
      rw [add_comm (K 1) ((2 : ℝ) • K 0), add_comm (K 1) (K 0), h2, h01, hzero]
      linarith
    · have h2 := hvol ![0, 2, 1] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 2 + (2 : ℝ) • K 1) -
        2 * bodyVolume (K 2 + K 1) + bodyVolume (K 2)
      rw [add_comm (K 2) ((2 : ℝ) • K 1), add_comm (K 2) (K 1), h2, h12, hzero]
      norm_num
    · have h2 := hvol ![1, 0, 2] (by intro j; fin_cases j <;> norm_num)
      norm_num [volumeFunction, weightedSum, Fin.sum_univ_three, value] at h2
      change 0 < bodyVolume (K 0 + (2 : ℝ) • K 2) -
        2 * bodyVolume (K 0 + K 2) + bodyVolume (K 0)
      rw [h2, h02, hzero]
      linarith

/-- The first geometric assertion of Proposition 3.1, with the full parameter
range and every realization retained. -/
theorem centered_linearHulls_are_planes {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i : Fin 3) :
    finrank ℝ (linearHull (K i)) = 2 := by
  first
  | have hproper := (bodyVolume_eq_zero_iff_linearHull_ne_top (h0 i)).mp
      (pure_volumes_zero hK i)
    have hlt := Submodule.finrank_lt hproper
    have hspace : finrank ℝ (Space 3) = 3 := by simp [Space]
    rw [hspace] at hlt
    have hnot : ¬ finrank ℝ (linearHull (K i)) ≤ 1 := by
      intro hdim
      obtain ⟨a, b, _, _, hseg⟩ := exists_segment_of_finrank_linearHull_le_one (K i) (h0 i) hdim
      have hz := bodyVolume_segment_second_difference (K i) (K (nextBody i)) ⟨a, b, hseg⟩
      have hp := second_difference_positive hα hs hK i
      rw [hz] at hp
      exact lt_irrefl 0 hp
    omega

theorem pair_volumes_positive {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (i j : Fin 3) (hij : i ≠ j) : 0 < bodyVolume (K i + K j) := by
  first
  | obtain ⟨h01, h02, h12⟩ := pair_volumes hK
    have hp01 : 0 < bodyVolume (K 0 + K 1) := by rw [h01]; linarith
    have hp02 : 0 < bodyVolume (K 0 + K 2) := by rw [h02]; linarith
    have hp12 : 0 < bodyVolume (K 1 + K 2) := by rw [h12]; norm_num
    have hp10 : 0 < bodyVolume (K 1 + K 0) := by rwa [add_comm]
    have hp20 : 0 < bodyVolume (K 2 + K 0) := by rwa [add_comm]
    have hp21 : 0 < bodyVolume (K 2 + K 1) := by rwa [add_comm]
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | exact hp01
      | exact hp02
      | exact hp12
      | exact hp10
      | exact hp20
      | exact hp21

theorem centered_pair_linearHulls_eq_top {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i j : Fin 3) (hij : i ≠ j) :
    linearHull (K i) ⊔ linearHull (K j) = ⊤ := by
  first
  | have h := (bodyVolume_pos_iff_linearHull_eq_top
      (zero_mem_body_add (h0 i) (h0 j))).mp (pair_volumes_positive hα hs hK i j hij)
    rwa [linearHull_add (h0 i) (h0 j)] at h

theorem centered_plane_intersection_is_line {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z))
    (h0 : ∀ i, (0 : Space 3) ∈ K i) (i j : Fin 3) (hij : i ≠ j) :
    finrank ℝ ((linearHull (K i) ⊓ linearHull (K j)) : Submodule ℝ (Space 3)) = 1 := by
  first
  | have h := Submodule.finrank_sup_add_finrank_inf_eq (linearHull (K i)) (linearHull (K j))
    rw [centered_pair_linearHulls_eq_top hα hs hK h0 i j hij,
      centered_linearHulls_are_planes hα hs hK h0 i,
      centered_linearHulls_are_planes hα hs hK h0 j] at h
    have hspace : finrank ℝ (⊤ : Submodule ℝ (Space 3)) = 3 := by simp [Space]
    rw [hspace] at h
    omega

theorem exists_centered_planar_realization {α s z : ℝ} (hα : 0 < α) (hs : 0 < s)
    {K : Fin 3 → Body 3} (hK : Realizes K (coefficients α s z)) :
    ∃ p : Fin 3 → Space 3, (∀ i, p i ∈ K i) ∧
      Realizes (fun i => translateBody (-p i) (K i)) (coefficients α s z) ∧
      ∀ i, (0 : Space 3) ∈ translateBody (-p i) (K i) ∧
        finrank ℝ (linearHull (translateBody (-p i) (K i))) = 2 := by
  first
  | choose p hp using fun i => (K i).nonempty
    have hreal := hK.translate (fun i => -p i)
    have h0 : ∀ i, (0 : Space 3) ∈ translateBody (-p i) (K i) :=
      fun i => zero_mem_translateBody_neg (hp i)
    exact ⟨p, hp, hreal, fun i => ⟨h0 i, centered_linearHulls_are_planes hα hs hreal h0 i⟩⟩

end VolumePolynomials.CubicSlice
