module

public import tau_ceti.probability.distributions.wishart.bartlett
public import tau_ceti.probability.distributions.gaussian.chi_squared
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# The three-compression overlap obstruction

The example on page 12 of the paper has an actual density-defined
`Wishart(α, I₂)` law, with `1 < α < 2`.  Its three rank-one quadratic forms
are `X₀₀` and `(e₁ ± a e₀)ᵀ X (e₁ ± a e₀)`.  Their selected covariance can
be negative.  The calculation below uses the proved Bartlett pushforward and
scalar chi-squared moments, including nonintegral degrees of freedom.

## Main results

* `covariance_rank_one_overlap`: the exact covariance polynomial for every `α > 1`.
* `covariance_rank_one_overlap_neg`: its negative range when `1 < α < 2`.
* `covariance_rank_one_overlap_three_halves`: the exact value `-27/256` at
  `α = 3/2`, `a = 1/4`.
* `rank_one_overlap_split_fails`: the strict reverse selected-split inequality
  between finite expectations under the actual Wishart law.
* `conditional_mean_rank_one_overlap_bartlett`: the displayed conditional mean,
  conditioning on `X₀₀` in the Bartlett model identified by `bartlett_realizes_wishart`.

The indices in this file start at zero: the paper's `X₁₁` is `selectedQuadratic`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open scoped BigOperators ENNReal

namespace Wishart.OverlapObstruction

abbrev Matrix2 := selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)
abbrev Coordinates := lowerTriangle 2 → ℝ

/-! ### Bartlett coordinates and scalar moments -/

/-- The three independent Bartlett-coordinate laws for a two-dimensional
Wishart matrix. -/
def coordinateMeasure (α : ℝ) : Measure Coordinates :=
  Measure.pi (bartlettCoordinateMeasure (p := 2) α)

/-- The Bartlett product law is a probability measure at every admissible shape. -/
theorem isProbabilityMeasure_coordinateMeasure {α : ℝ} (hα : 1 < α) :
    IsProbabilityMeasure (coordinateMeasure α) := by
  let _ := isProbabilityMeasure_bartlettCoordinateMeasure
    (p := 2) (n := α) (by norm_num; exact hα)
  unfold coordinateMeasure
  infer_instance

/-- The random matrix used below has precisely the density-defined Wishart law. -/
theorem bartlett_realizes_wishart {α : ℝ} (hα : 1 < α) :
    (coordinateMeasure α).map (lowerTriangleGram 2) =
      nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  (nonsingularWishartMeasure_one_eq_map_lowerTriangleGram
    (by norm_num; exact hα)).symm

abbrev diagonalZero : lowerTriangle 2 := ⟨(0, 0), by decide⟩
abbrev offDiagonal : lowerTriangle 2 := ⟨(1, 0), by decide⟩
abbrev diagonalOne : lowerTriangle 2 := ⟨(1, 1), by decide⟩

private theorem lowerTriangle_two_univ :
    (Finset.univ : Finset (lowerTriangle 2)) =
      {diagonalZero, offDiagonal, diagonalOne} := by decide

/-- The coordinate monomial uses powers of the squared coordinates. -/
def monomial (r s t : ℕ) (x : Coordinates) : ℝ :=
  (x diagonalZero ^ 2) ^ r * (x offDiagonal ^ 2) ^ s * (x diagonalOne ^ 2) ^ t

private def coordinateExponent (r s t : ℕ) (ij : lowerTriangle 2) : ℕ :=
  if ij = diagonalZero then r else if ij = offDiagonal then s else t

private theorem monomial_eq_product (r s t : ℕ) (x : Coordinates) :
    monomial r s t x =
      ∏ ij : lowerTriangle 2, (x ij ^ 2) ^ coordinateExponent r s t ij := by
  rw [lowerTriangle_two_univ]
  simp [monomial, coordinateExponent, mul_assoc]

private theorem squared_coordinate_law {α : ℝ} (hα : 1 < α)
    (ij : lowerTriangle 2) :
    (bartlettCoordinateMeasure α ij).map (fun z : ℝ ↦ z ^ 2) =
      chiSquaredMeasure (if ij = diagonalZero then α else if ij = offDiagonal then 1 else α-1) := by
  have hij : ij = diagonalZero ∨ ij = offDiagonal ∨ ij = diagonalOne := by
    have hi := Finset.mem_univ ij
    rw [lowerTriangle_two_univ] at hi
    simpa using hi
  rcases hij with rfl | rfl | rfl
  · simpa using (map_sq_bartlettCoordinateMeasure_of_eq
      (p := 2) (n := α) (by norm_num; exact hα) (ij := diagonalZero) rfl)
  · rw [bartlettCoordinateMeasure_of_ne α (ij := offDiagonal) (by decide), gaussianReal_map_sq]
    simp
  · simpa using (map_sq_bartlettCoordinateMeasure_of_eq
      (p := 2) (n := α) (by norm_num; exact hα) (ij := diagonalOne) rfl)

private theorem integrable_pow_chiSquared {k : ℝ} (hk : 0 < k) (r : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ r) (chiSquaredMeasure k) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk]
  exact integrable_pow_gammaMeasure (by positivity) (by norm_num) r

private theorem chiSquared_moment_zero {k : ℝ} (hk : 0 < k) :
    (∫ x : ℝ, x ^ 0 ∂chiSquaredMeasure k) = 1 := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hk.le
  simp

private theorem chiSquared_moment_one {k : ℝ} (hk : 0 < k) :
    (∫ x : ℝ, x ^ 1 ∂chiSquaredMeasure k) = k := by
  simpa using integral_id_chiSquaredMeasure hk.le

private theorem chiSquared_moment_two {k : ℝ} (hk : 0 < k) :
    (∫ x : ℝ, x ^ 2 ∂chiSquaredMeasure k) = k * (k + 2) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    integral_pow_gammaMeasure (by positivity) (by norm_num)]
  have h0 : k / 2 ≠ 0 := by positivity
  have h1 : k / 2 + 1 ≠ 0 := by positivity
  have hΓ : Real.Gamma (k / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show k / 2 + (2 : ℕ) = (k / 2 + 1) + 1 by norm_num; ring,
    Real.Gamma_add_one h1, Real.Gamma_add_one h0]
  field_simp

private theorem chiSquared_moment_three {k : ℝ} (hk : 0 < k) :
    (∫ x : ℝ, x ^ 3 ∂chiSquaredMeasure k) = k * (k + 2) * (k + 4) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    integral_pow_gammaMeasure (by positivity) (by norm_num)]
  have h0 : k / 2 ≠ 0 := by positivity
  have h1 : k / 2 + 1 ≠ 0 := by positivity
  have h2 : (k / 2 + 1) + 1 ≠ 0 := by positivity
  have hΓ : Real.Gamma (k / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show k / 2 + (3 : ℕ) = ((k / 2 + 1) + 1) + 1 by norm_num; ring,
    Real.Gamma_add_one h2, Real.Gamma_add_one h1, Real.Gamma_add_one h0]
  field_simp
  ring

private theorem integrable_squared_coordinate_power {α : ℝ} (hα : 1 < α)
    (ij : lowerTriangle 2) (r : ℕ) :
    Integrable (fun z : ℝ ↦ (z ^ 2) ^ r) (bartlettCoordinateMeasure α ij) := by
  have hk : 0 < (if ij = diagonalZero then α else if ij = offDiagonal then 1 else α - 1) := by
    split_ifs <;> linarith
  have hi := integrable_pow_chiSquared hk r
  rw [← squared_coordinate_law hα ij] at hi
  exact (integrable_map_measure (g := fun z : ℝ ↦ z ^ r)
    (f := fun z : ℝ ↦ z ^ 2) (by fun_prop) (by fun_prop)).1 hi

private theorem integral_squared_coordinate_power {α : ℝ} (hα : 1 < α)
    (ij : lowerTriangle 2) (r : ℕ) :
    (∫ z : ℝ, (z ^ 2) ^ r ∂bartlettCoordinateMeasure α ij) =
      ∫ z : ℝ, z ^ r ∂chiSquaredMeasure
        (if ij = diagonalZero then α else if ij = offDiagonal then 1 else α - 1) := by
  rw [← squared_coordinate_law hα ij, integral_map (by fun_prop) (by fun_prop)]

/-- All polynomial moments in the squared Bartlett coordinates are finite. -/
theorem integrable_monomial {α : ℝ} (hα : 1 < α) (r s t : ℕ) :
    Integrable (monomial r s t) (coordinateMeasure α) := by
  let _ := isProbabilityMeasure_bartlettCoordinateMeasure
    (p := 2) (n := α) (by norm_num; exact hα)
  simp_rw [show monomial r s t = fun x ↦
    ∏ ij : lowerTriangle 2, (x ij ^ 2) ^ coordinateExponent r s t ij by
      funext x; exact monomial_eq_product r s t x]
  exact Integrable.fintype_prod (fun ij ↦
    integrable_squared_coordinate_power hα ij (coordinateExponent r s t ij))

/-- Bartlett independence factors the three-coordinate moments into scalar moments. -/
theorem integral_monomial {α : ℝ} (hα : 1 < α) (r s t : ℕ) :
    (∫ x, monomial r s t x ∂coordinateMeasure α) =
      (∫ z : ℝ, z ^ r ∂chiSquaredMeasure α) *
      (∫ z : ℝ, z ^ s ∂chiSquaredMeasure 1) *
      (∫ z : ℝ, z ^ t ∂chiSquaredMeasure (α - 1)) := by
  let _ := isProbabilityMeasure_bartlettCoordinateMeasure
    (p := 2) (n := α) (by norm_num; exact hα)
  simp_rw [monomial_eq_product]
  rw [coordinateMeasure,
    integral_fintype_prod_eq_prod (fun ij (z : ℝ) ↦ (z ^ 2) ^ coordinateExponent r s t ij)]
  simp_rw [integral_squared_coordinate_power hα]
  rw [lowerTriangle_two_univ]
  simp [coordinateExponent, mul_assoc]

/-! ### Polynomial expansion and moments -/

private def pairPolynomial (a : ℝ) (x : Coordinates) : ℝ :=
  monomial 0 2 0 x + 2 * monomial 0 1 1 x + monomial 0 0 2 x +
    (2 * a ^ 2) * monomial 1 0 1 x - (2 * a ^ 2) * monomial 1 1 0 x +
    a ^ 4 * monomial 2 0 0 x

private def weightedPairPolynomial (a : ℝ) (x : Coordinates) : ℝ :=
  monomial 1 2 0 x + 2 * monomial 1 1 1 x + monomial 1 0 2 x +
    (2 * a ^ 2) * monomial 2 0 1 x - (2 * a ^ 2) * monomial 2 1 0 x +
    a ^ 4 * monomial 3 0 0 x

private theorem integrable_pairPolynomial {α : ℝ} (hα : 1 < α) (a : ℝ) :
    Integrable (pairPolynomial a) (coordinateMeasure α) := by
  exact (((((integrable_monomial hα 0 2 0).add
    ((integrable_monomial hα 0 1 1).const_mul 2)).add
    (integrable_monomial hα 0 0 2)).add
    ((integrable_monomial hα 1 0 1).const_mul (2 * a ^ 2))).sub
    ((integrable_monomial hα 1 1 0).const_mul (2 * a ^ 2))).add
    ((integrable_monomial hα 2 0 0).const_mul (a ^ 4))

private theorem integrable_weightedPairPolynomial {α : ℝ} (hα : 1 < α) (a : ℝ) :
    Integrable (weightedPairPolynomial a) (coordinateMeasure α) := by
  exact (((((integrable_monomial hα 1 2 0).add
    ((integrable_monomial hα 1 1 1).const_mul 2)).add
    (integrable_monomial hα 1 0 2)).add
    ((integrable_monomial hα 2 0 1).const_mul (2 * a ^ 2))).sub
    ((integrable_monomial hα 2 1 0).const_mul (2 * a ^ 2))).add
    ((integrable_monomial hα 3 0 0).const_mul (a ^ 4))

private theorem integral_six_terms {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f₁ f₂ f₃ f₄ f₅ f₆ : Ω → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) (h₆ : Integrable f₆ μ) :
    (∫ x, f₁ x + f₂ x + f₃ x + f₄ x - f₅ x + f₆ x ∂μ) =
      (∫ x, f₁ x ∂μ) + (∫ x, f₂ x ∂μ) + (∫ x, f₃ x ∂μ) +
      (∫ x, f₄ x ∂μ) - (∫ x, f₅ x ∂μ) + (∫ x, f₆ x ∂μ) := by
  change (∫ x, (f₁ + f₂ + f₃ + f₄ - f₅ + f₆) x ∂μ) = _
  rw [integral_add' ((((h₁.add h₂).add h₃).add h₄).sub h₅) h₆,
    integral_sub' (((h₁.add h₂).add h₃).add h₄) h₅,
    integral_add' ((h₁.add h₂).add h₃) h₄,
    integral_add' (h₁.add h₂) h₃, integral_add' h₁ h₂]

private theorem integral_pairPolynomial {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (∫ x, pairPolynomial a x ∂coordinateMeasure α) =
      α * (α + 2) + 2 * α * (α - 2) * a ^ 2 + α * (α + 2) * a ^ 4 := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  unfold pairPolynomial
  rw [integral_six_terms (integrable_monomial hα 0 2 0)
      ((integrable_monomial hα 0 1 1).const_mul 2) (integrable_monomial hα 0 0 2)
      ((integrable_monomial hα 1 0 1).const_mul (2 * a ^ 2))
      ((integrable_monomial hα 1 1 0).const_mul (2 * a ^ 2))
      ((integrable_monomial hα 2 0 0).const_mul (a ^ 4))]
  simp only [integral_const_mul, integral_monomial hα,
    chiSquared_moment_zero hα0, chiSquared_moment_zero hα1,
    chiSquared_moment_zero (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_one hα0, chiSquared_moment_one hα1,
    chiSquared_moment_one (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_two hα0, chiSquared_moment_two hα1,
    chiSquared_moment_two (by norm_num : (0 : ℝ) < 1)]
  ring

private theorem integral_weightedPairPolynomial {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (∫ x, weightedPairPolynomial a x ∂coordinateMeasure α) =
      α ^ 2 * (α + 2) + 2 * α * (α + 2) * (α - 2) * a ^ 2 +
        α * (α + 2) * (α + 4) * a ^ 4 := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  unfold weightedPairPolynomial
  rw [integral_six_terms (integrable_monomial hα 1 2 0)
      ((integrable_monomial hα 1 1 1).const_mul 2) (integrable_monomial hα 1 0 2)
      ((integrable_monomial hα 2 0 1).const_mul (2 * a ^ 2))
      ((integrable_monomial hα 2 1 0).const_mul (2 * a ^ 2))
      ((integrable_monomial hα 3 0 0).const_mul (a ^ 4))]
  simp only [integral_const_mul, integral_monomial hα, chiSquared_moment_zero hα1,
    chiSquared_moment_zero (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_one hα0, chiSquared_moment_one hα1,
    chiSquared_moment_one (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_two hα0, chiSquared_moment_two hα1,
    chiSquared_moment_two (by norm_num : (0 : ℝ) < 1), chiSquared_moment_three hα0]
  ring

/-! ### Quadratic forms and their covariance -/

/-- The first rank-one quadratic form, `e₀ᵀ X e₀`. -/
def selectedQuadratic (X : Matrix2) : ℝ :=
  (X : Matrix (Fin 2) (Fin 2) ℝ) 0 0

/-- The rank-one quadratic form `(e₁ + a e₀)ᵀ X (e₁ + a e₀)`. -/
def shiftedQuadratic (a : ℝ) (X : Matrix2) : ℝ :=
  dotProduct ![a, 1] ((X : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![a, 1])

/-- The product of the two overlapping rank-one quadratic forms. -/
def overlapProduct (a : ℝ) (X : Matrix2) : ℝ :=
  shiftedQuadratic a X * shiftedQuadratic (-a) X

@[fun_prop]
theorem continuous_selectedQuadratic : Continuous selectedQuadratic :=
  selfAdjoint.continuous_coe_apply 0 0

@[fun_prop]
theorem continuous_shiftedQuadratic (a : ℝ) : Continuous (shiftedQuadratic a) := by
  unfold shiftedQuadratic
  simp only [dotProduct, mulVec, Fin.sum_univ_two]
  refine (((((selfAdjoint.continuous_coe_apply (p := 2) 0 0).mul_const a).add
    (selfAdjoint.continuous_coe_apply 0 1)).const_mul a).add
    (((selfAdjoint.continuous_coe_apply 1 0).mul_const a).add
      (selfAdjoint.continuous_coe_apply 1 1))).congr ?_
  intro X
  simp

@[fun_prop]
theorem continuous_overlapProduct (a : ℝ) : Continuous (overlapProduct a) :=
  (continuous_shiftedQuadratic a).mul (continuous_shiftedQuadratic (-a))

private theorem selectedQuadratic_lowerTriangleGram (x : Coordinates) :
    selectedQuadratic (lowerTriangleGram 2 x) = monomial 1 0 0 x := by
  simp [selectedQuadratic, monomial, coe_lowerTriangleGram, Matrix.mul_apply,
    Fin.sum_univ_two, diagonalZero, pow_two]

private theorem shiftedQuadratic_lowerTriangleGram (a : ℝ) (x : Coordinates) :
    shiftedQuadratic a (lowerTriangleGram 2 x) =
      a ^ 2 * x diagonalZero ^ 2 + 2 * a * x diagonalZero * x offDiagonal +
        x offDiagonal ^ 2 + x diagonalOne ^ 2 := by
  simp [shiftedQuadratic, dotProduct, mulVec, Fin.sum_univ_two,
    coe_lowerTriangleGram, Matrix.mul_apply,
    diagonalZero, offDiagonal, diagonalOne]
  ring

private theorem overlapProduct_lowerTriangleGram (a : ℝ) (x : Coordinates) :
    overlapProduct a (lowerTriangleGram 2 x) = pairPolynomial a x := by
  simp only [overlapProduct, shiftedQuadratic_lowerTriangleGram, pairPolynomial, monomial]
  ring

private theorem weightedPairPolynomial_eq (a : ℝ) :
    (fun x ↦ monomial 1 0 0 x * pairPolynomial a x) = weightedPairPolynomial a := by
  funext x
  simp only [pairPolynomial, weightedPairPolynomial, monomial]
  ring

/-- Only integrability of the two factors and their product is needed to expand
this covariance; no unproved second-moment assumption is introduced. -/
private theorem covariance_eq_sub_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : Integrable (fun x ↦ X x * Y x) μ) :
    covariance X Y μ = (∫ x, X x * Y x ∂μ) - (∫ x, X x ∂μ) * (∫ x, Y x ∂μ) := by
  simp_rw [covariance, sub_mul, mul_sub]
  repeat rw [integral_sub]
  · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
      one_smul]
    ring
  · exact hY.const_mul _
  · exact integrable_const _
  · exact hXY
  · exact hX.mul_const _
  · exact hXY.sub (hX.mul_const _)
  · exact (hY.const_mul _).sub (integrable_const _)

private theorem covariance_bartlett_coordinates {α : ℝ} (hα : 1 < α) (a : ℝ) :
    covariance (monomial 1 0 0) (pairPolynomial a) (coordinateMeasure α) =
      4 * α * a ^ 2 * (α - 2 + (α + 2) * a ^ 2) := by
  let _ := isProbabilityMeasure_bartlettCoordinateMeasure
    (p := 2) (n := α) (by norm_num; exact hα)
  have : IsProbabilityMeasure (coordinateMeasure α) := by
    unfold coordinateMeasure
    infer_instance
  have hXY : Integrable (fun x ↦ monomial 1 0 0 x * pairPolynomial a x)
      (coordinateMeasure α) := by
    rw [weightedPairPolynomial_eq]
    exact integrable_weightedPairPolynomial hα a
  rw [covariance_eq_sub_of_integrable (integrable_monomial hα 1 0 0)
    (integrable_pairPolynomial hα a) hXY,
    weightedPairPolynomial_eq, integral_weightedPairPolynomial hα,
    integral_pairPolynomial hα, integral_monomial hα]
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  simp only [chiSquared_moment_one hα0, chiSquared_moment_zero hα1,
    chiSquared_moment_zero (by norm_num : (0 : ℝ) < 1)]
  ring

/-- **The overlap covariance identity.** The law is the actual Wishart density,
and all expectations used in the calculation are proved integrable by Bartlett
independence. The identity holds at every nonsingular two-dimensional shape. -/
theorem covariance_rank_one_overlap {α : ℝ} (hα : 1 < α) (a : ℝ) :
    covariance selectedQuadratic (overlapProduct a)
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      4 * α * a ^ 2 * (α - 2 + (α + 2) * a ^ 2) := by
  rw [show nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      (coordinateMeasure α).map (lowerTriangleGram 2) from
      nonsingularWishartMeasure_one_eq_map_lowerTriangleGram (by norm_num; exact hα),
    covariance_map_fun continuous_selectedQuadratic.aestronglyMeasurable
      (continuous_overlapProduct a).aestronglyMeasurable
      (measurable_lowerTriangleGram 2).aemeasurable]
  simpa only [selectedQuadratic_lowerTriangleGram, overlapProduct_lowerTriangleGram]
    using covariance_bartlett_coordinates hα a

/-- For every `1 < α < 2`, sufficiently small nonzero overlap makes the
selected split covariance strictly negative. -/
theorem covariance_rank_one_overlap_neg {α a : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2)
    (ha : 0 < a ^ 2) (hsmall : a ^ 2 < (2 - α) / (α + 2)) :
    covariance selectedQuadratic (overlapProduct a)
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) < 0 := by
  rw [covariance_rank_one_overlap hα₁]
  have hp : 0 < 4 * α * a ^ 2 := by positivity
  have hden : 0 < α + 2 := by linarith
  have hs := (lt_div_iff₀ hden).mp hsmall
  have hn : α - 2 + (α + 2) * a ^ 2 < 0 := by nlinarith
  exact mul_neg_of_pos_of_neg hp hn

/-- An exact rational witness: shape `3/2`, overlap coefficient `1/4`. -/
theorem covariance_rank_one_overlap_three_halves :
    covariance selectedQuadratic (overlapProduct (1 / 4))
      (nonsingularWishartMeasure (3 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      -(27 / 256) := by
  rw [covariance_rank_one_overlap (by norm_num : (1 : ℝ) < 3 / 2)]
  norm_num

/-- The exact rational witness is a strict obstruction to unrestricted splitting
of three rank-one real Wishart compressions. -/
theorem covariance_rank_one_overlap_three_halves_neg :
    covariance selectedQuadratic (overlapProduct (1 / 4))
      (nonsingularWishartMeasure (3 / 2) (1 : Matrix (Fin 2) (Fin 2) ℝ)) < 0 := by
  rw [covariance_rank_one_overlap_three_halves]
  norm_num

/-! ### Actual-law moments and failure of the selected split -/

/-- The selected rank-one quadratic form is integrable under the actual law. -/
theorem integrable_selectedQuadratic {α : ℝ} (hα : 1 < α) :
    Integrable selectedQuadratic
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← bartlett_realizes_wishart hα]
  refine (integrable_map_measure
    continuous_selectedQuadratic.aestronglyMeasurable
    (measurable_lowerTriangleGram 2).aemeasurable).2 ?_
  simpa only [Function.comp_def, selectedQuadratic_lowerTriangleGram]
    using integrable_monomial hα 1 0 0

/-- The product of the two overlapping quadratic forms is integrable. -/
theorem integrable_overlapProduct {α : ℝ} (hα : 1 < α) (a : ℝ) :
    Integrable (overlapProduct a)
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← bartlett_realizes_wishart hα]
  refine (integrable_map_measure
    (continuous_overlapProduct a).aestronglyMeasurable
    (measurable_lowerTriangleGram 2).aemeasurable).2 ?_
  simpa only [Function.comp_def, overlapProduct_lowerTriangleGram]
    using integrable_pairPolynomial hα a

/-- The joint product of all three quadratic forms is integrable. -/
theorem integrable_selected_overlapProduct {α : ℝ} (hα : 1 < α) (a : ℝ) :
    Integrable (fun X ↦ selectedQuadratic X * overlapProduct a X)
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← bartlett_realizes_wishart hα]
  refine (integrable_map_measure
    (continuous_selectedQuadratic.mul (continuous_overlapProduct a)).aestronglyMeasurable
    (measurable_lowerTriangleGram 2).aemeasurable).2 ?_
  change Integrable (fun x ↦ selectedQuadratic (lowerTriangleGram 2 x) *
    overlapProduct a (lowerTriangleGram 2 x)) (coordinateMeasure α)
  simp only [selectedQuadratic_lowerTriangleGram, overlapProduct_lowerTriangleGram]
  rw [weightedPairPolynomial_eq]
  exact integrable_weightedPairPolynomial hα a

/-- The mean of the first rank-one form is the shape parameter. -/
theorem integral_selectedQuadratic {α : ℝ} (hα : 1 < α) :
    (∫ X, selectedQuadratic X
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) = α := by
  rw [← bartlett_realizes_wishart hα,
    integral_map_of_stronglyMeasurable (measurable_lowerTriangleGram 2)
      continuous_selectedQuadratic.stronglyMeasurable]
  simp only [selectedQuadratic_lowerTriangleGram]
  rw [integral_monomial hα]
  simp only [chiSquared_moment_one (by linarith : 0 < α),
    chiSquared_moment_zero (by linarith : 0 < α - 1),
    chiSquared_moment_zero (by norm_num : (0 : ℝ) < 1), mul_one]

/-- The exact mean of the pair of overlapping quadratic forms. -/
theorem integral_overlapProduct {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (∫ X, overlapProduct a X
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      α * (α + 2) + 2 * α * (α - 2) * a ^ 2 + α * (α + 2) * a ^ 4 := by
  rw [← bartlett_realizes_wishart hα,
    integral_map_of_stronglyMeasurable (measurable_lowerTriangleGram 2)
      (continuous_overlapProduct a).stronglyMeasurable]
  simpa only [overlapProduct_lowerTriangleGram] using integral_pairPolynomial hα a

/-- The exact joint moment of all three quadratic forms. -/
theorem integral_selected_overlapProduct {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (∫ X, selectedQuadratic X * overlapProduct a X
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      α ^ 2 * (α + 2) + 2 * α * (α + 2) * (α - 2) * a ^ 2 +
        α * (α + 2) * (α + 4) * a ^ 4 := by
  rw [← bartlett_realizes_wishart hα,
    integral_map_of_stronglyMeasurable (measurable_lowerTriangleGram 2)
      (f := fun X ↦ selectedQuadratic X * overlapProduct a X) (by fun_prop)]
  simp only [selectedQuadratic_lowerTriangleGram, overlapProduct_lowerTriangleGram]
  rw [weightedPairPolynomial_eq, integral_weightedPairPolynomial hα]

/-- The failed selected split is a strict inequality between finite moments. -/
theorem rank_one_overlap_split_fails {α a : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2)
    (ha : 0 < a ^ 2) (hsmall : a ^ 2 < (2 - α) / (α + 2)) :
    (∫ X, selectedQuadratic X * overlapProduct a X
      ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) <
      (∫ X, selectedQuadratic X
        ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (∫ X, overlapProduct a X
        ∂nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have := isProbabilityMeasure_coordinateMeasure hα₁
  have : IsProbabilityMeasure
      (nonsingularWishartMeasure α (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [← bartlett_realizes_wishart hα₁]
    infer_instance
  have hn := covariance_rank_one_overlap_neg hα₁ hα₂ ha hsmall
  rw [covariance_eq_sub_of_integrable (integrable_selectedQuadratic hα₁)
    (integrable_overlapProduct hα₁ a) (integrable_selected_overlapProduct hα₁ a)] at hn
  exact sub_neg.mp hn

/-! ### The conditional mean printed in the paper -/

private def selectedCoordinate (x : Coordinates) : ℝ := x diagonalZero ^ 2

private theorem measurable_selectedCoordinate : Measurable selectedCoordinate := by
  unfold selectedCoordinate
  fun_prop

private abbrev selectedSigma : MeasurableSpace Coordinates :=
  (borel ℝ).comap selectedCoordinate

private theorem measurable_monomial (r s t : ℕ) : Measurable (monomial r s t) := by
  unfold monomial
  fun_prop

private theorem noise_monomial_independent {α : ℝ} (hα : 1 < α) (s t : ℕ) :
    IndepFun (monomial 0 s t) selectedCoordinate (coordinateMeasure α) := by
  let _ := isProbabilityMeasure_bartlettCoordinateMeasure
    (p := 2) (n := α) (by norm_num; exact hα)
  let f : lowerTriangle 2 → Coordinates → ℝ :=
    fun ij x ↦ (x ij ^ 2) ^ coordinateExponent 1 s t ij
  have hf : iIndepFun f (coordinateMeasure α) :=
    iIndepFun_pi (X := fun ij (z : ℝ) ↦ (z ^ 2) ^ coordinateExponent 1 s t ij)
      (fun ij ↦ by fun_prop)
  have hp := hf.indepFun_finsetProd_of_notMem
    (fun ij ↦ by unfold f; fun_prop)
    (s := {offDiagonal, diagonalOne}) (i := diagonalZero) (by decide)
  have hnoise : (∏ ij ∈ ({offDiagonal, diagonalOne} : Finset (lowerTriangle 2)), f ij) =
      monomial 0 s t := by
    funext x
    simp [f, coordinateExponent, monomial]
  have hselected : f diagonalZero = selectedCoordinate := by
    funext x
    simp [f, coordinateExponent, selectedCoordinate]
  rw [hnoise, hselected] at hp
  exact hp

private theorem condExp_noise_monomial {α : ℝ} (hα : 1 < α) (s t : ℕ) :
    (coordinateMeasure α)[monomial 0 s t | selectedSigma] =ᵐ[coordinateMeasure α]
      fun _ ↦ ∫ x, monomial 0 s t x ∂coordinateMeasure α := by
  have := isProbabilityMeasure_coordinateMeasure hα
  exact condExp_indep_eq (m₁ := (borel ℝ).comap (monomial 0 s t))
    (m₂ := selectedSigma) (μ := coordinateMeasure α)
    (measurable_monomial 0 s t).comap_le
    measurable_selectedCoordinate.comap_le
    (comap_measurable (monomial 0 s t)).stronglyMeasurable
    ((IndepFun_iff_Indep _ _ _).1 (noise_monomial_independent hα s t))

private theorem condExp_monomial {α : ℝ} (hα : 1 < α) (r s t : ℕ) :
    (coordinateMeasure α)[monomial r s t | selectedSigma] =ᵐ[coordinateMeasure α]
      fun x ↦ selectedCoordinate x ^ r *
        (∫ z : ℝ, z ^ s ∂chiSquaredMeasure 1) *
        (∫ z : ℝ, z ^ t ∂chiSquaredMeasure (α - 1)) := by
  have hfactor : monomial r s t =
      (fun x ↦ selectedCoordinate x ^ r) * monomial 0 s t := by
    funext x
    simp [monomial, selectedCoordinate, mul_assoc]
  have hm : StronglyMeasurable[selectedSigma] (fun x ↦ selectedCoordinate x ^ r) :=
    ((comap_measurable selectedCoordinate).pow_const r).stronglyMeasurable
  have hi : Integrable ((fun x ↦ selectedCoordinate x ^ r) * monomial 0 s t)
      (coordinateMeasure α) := hfactor ▸ integrable_monomial hα r s t
  rw [hfactor]
  have hp := condExp_mul_of_stronglyMeasurable_left hm hi (integrable_monomial hα 0 s t)
  filter_upwards [hp, condExp_noise_monomial hα s t] with x hx hn
  rw [hx, Pi.mul_apply, hn, integral_monomial hα]
  simp only [chiSquared_moment_zero (by linarith : 0 < α)]
  ring

private theorem condExp_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : MeasurableSpace Ω) (c : ℝ) (f : Ω → ℝ) :
    μ[(fun x ↦ c * f x) | m] =ᵐ[μ] fun x ↦ c * (μ[f | m]) x := by
  change μ[c • f | m] =ᵐ[μ] c • μ[f | m]
  exact condExp_smul c f m

private theorem condExp_six_terms {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (m : MeasurableSpace Ω) {f₁ f₂ f₃ f₄ f₅ f₆ : Ω → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) (h₆ : Integrable f₆ μ) :
    μ[(fun x ↦ f₁ x + f₂ x + f₃ x + f₄ x - f₅ x + f₆ x) | m] =ᵐ[μ]
      fun x ↦ (μ[f₁ | m]) x + (μ[f₂ | m]) x + (μ[f₃ | m]) x +
        (μ[f₄ | m]) x - (μ[f₅ | m]) x + (μ[f₆ | m]) x := by
  change μ[f₁ + f₂ + f₃ + f₄ - f₅ + f₆ | m] =ᵐ[μ] _
  filter_upwards [condExp_add ((((h₁.add h₂).add h₃).add h₄).sub h₅) h₆ m,
    condExp_sub (((h₁.add h₂).add h₃).add h₄) h₅ m,
    condExp_add ((h₁.add h₂).add h₃) h₄ m,
    condExp_add (h₁.add h₂) h₃ m, condExp_add h₁ h₂ m] with x h₆x h₅x h₄x h₃x h₂x
  simp only [Pi.add_apply, Pi.sub_apply] at h₆x h₅x h₄x h₃x h₂x
  rw [h₆x, h₅x, h₄x, h₃x, h₂x]

private theorem conditional_pairPolynomial {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (coordinateMeasure α)[pairPolynomial a | selectedSigma] =ᵐ[coordinateMeasure α]
      fun x ↦ α * (α + 2) + 2 * (α - 2) * a ^ 2 * selectedCoordinate x +
        a ^ 4 * selectedCoordinate x ^ 2 := by
  have hsix := condExp_six_terms selectedSigma (integrable_monomial hα 0 2 0)
    ((integrable_monomial hα 0 1 1).const_mul 2) (integrable_monomial hα 0 0 2)
    ((integrable_monomial hα 1 0 1).const_mul (2 * a ^ 2))
    ((integrable_monomial hα 1 1 0).const_mul (2 * a ^ 2))
    ((integrable_monomial hα 2 0 0).const_mul (a ^ 4))
  filter_upwards [hsix,
    condExp_const_mul (coordinateMeasure α) selectedSigma 2 (monomial 0 1 1),
    condExp_const_mul (coordinateMeasure α) selectedSigma (2 * a ^ 2) (monomial 1 0 1),
    condExp_const_mul (coordinateMeasure α) selectedSigma (2 * a ^ 2) (monomial 1 1 0),
    condExp_const_mul (coordinateMeasure α) selectedSigma (a ^ 4) (monomial 2 0 0),
    condExp_monomial hα 0 2 0, condExp_monomial hα 0 1 1,
    condExp_monomial hα 0 0 2, condExp_monomial hα 1 0 1,
    condExp_monomial hα 1 1 0, condExp_monomial hα 2 0 0]
    with x hx hc₂ hc₄ hc₅ hc₆ h020 h011 h002 h101 h110 h200
  change ((coordinateMeasure α)[(fun y ↦ monomial 0 2 0 y + 2 * monomial 0 1 1 y +
    monomial 0 0 2 y + (2 * a ^ 2) * monomial 1 0 1 y -
    (2 * a ^ 2) * monomial 1 1 0 y + a ^ 4 * monomial 2 0 0 y) | selectedSigma]) x = _
  rw [hx, hc₂, hc₄, hc₅, hc₆, h020, h011, h002, h101, h110, h200]
  have hα1 : 0 < α - 1 := by linarith
  simp only [chiSquared_moment_zero hα1, chiSquared_moment_one hα1,
    chiSquared_moment_two hα1, chiSquared_moment_zero (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_one (by norm_num : (0 : ℝ) < 1),
    chiSquared_moment_two (by norm_num : (0 : ℝ) < 1)]
  ring

/-- **The conditional mean from the overlap example.** In the Bartlett realization
`X = lowerTriangleGram 2`, whose pushforward is the actual Wishart measure by
`bartlett_realizes_wishart`, conditioning is on the σ-algebra generated by `X₀₀`.
Thus this is a genuine conditional expectation, with all independence and moment
claims proved from the product law. -/
theorem conditional_mean_rank_one_overlap_bartlett {α : ℝ} (hα : 1 < α) (a : ℝ) :
    (coordinateMeasure α)[(fun x ↦ overlapProduct a (lowerTriangleGram 2 x)) |
      (borel ℝ).comap (fun x ↦ selectedQuadratic (lowerTriangleGram 2 x))]
      =ᵐ[coordinateMeasure α]
      fun x ↦ α * (α + 2) + 2 * (α - 2) * a ^ 2 *
        selectedQuadratic (lowerTriangleGram 2 x) +
        a ^ 4 * selectedQuadratic (lowerTriangleGram 2 x) ^ 2 := by
  have hs : (fun x ↦ selectedQuadratic (lowerTriangleGram 2 x)) = selectedCoordinate := by
    funext x
    simp [selectedQuadratic_lowerTriangleGram, selectedCoordinate, monomial]
  have hp : (fun x ↦ overlapProduct a (lowerTriangleGram 2 x)) = pairPolynomial a :=
    funext (overlapProduct_lowerTriangleGram a)
  rw [hs, hp]
  have hs_apply (x : Coordinates) :
      selectedQuadratic (lowerTriangleGram 2 x) = selectedCoordinate x := congr_fun hs x
  simpa only [hs_apply] using conditional_pairPolynomial hα a

end Wishart.OverlapObstruction
