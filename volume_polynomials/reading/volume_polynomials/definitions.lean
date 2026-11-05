module
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-!
# Literal geometric semantics for volume-polynomial coefficients

The carrier is the actual set of points in `ℝᵈ`, with Mathlib's product Lebesgue
measure. `ConvexBody` means nonempty, compact, convex; it does not require
nonempty interior. No mixed-volume axioms or realization hypotheses are built
into the definitions below.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Pointwise BigOperators ENNReal

namespace VolumePolynomials

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Body (d : ℕ) := ConvexBody (Space d)

/-- Exactly the multi-indices of total degree `d`. The coordinate bound is
redundant mathematically, and makes the finiteness instance explicit. -/
abbrev MultiIndex (n d : ℕ) :=
  {α : Fin n → Fin (d + 1) // ∑ i, (α i : ℕ) = d}

abbrev Coefficients (n d : ℕ) := MultiIndex n d → ℝ

def exponent {n d : ℕ} (α : MultiIndex n d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (α.1 i : ℕ))

@[simp] theorem exponent_apply {n d : ℕ} (α : MultiIndex n d) (i : Fin n) :
    exponent α i = (α.1 i : ℕ) := by simp [exponent]

theorem exponent_injective {n d : ℕ} : Function.Injective (exponent (n := n) (d := d)) := by
  intro α β h
  apply Subtype.ext
  funext i
  apply Fin.ext
  simpa using congrArg (fun e : Fin n →₀ ℕ => e i) h

def coefficientPolynomial {n d : ℕ} (c : Coefficients n d) : MvPolynomial (Fin n) ℝ :=
  ∑ α, MvPolynomial.monomial (exponent α) (c α)

def evaluate {n d : ℕ} (c : Coefficients n d) (t : Fin n → ℝ) : ℝ :=
  ∑ α, c α * ∏ i, t i ^ (α.1 i : ℕ)

theorem evaluate_eq_polynomial_eval {n d : ℕ} (c : Coefficients n d) (t : Fin n → ℝ) :
    evaluate c t = MvPolynomial.eval t (coefficientPolynomial c) := by
  classical
  simp only [evaluate, coefficientPolynomial, MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [exponent_apply]

@[simp] theorem coefficientPolynomial_coeff {n d : ℕ} (c : Coefficients n d)
    (α : MultiIndex n d) : (coefficientPolynomial c).coeff (exponent α) = c α := by
  classical
  simp [coefficientPolynomial, MvPolynomial.coeff_monomial, exponent_injective.eq_iff]

theorem coefficientPolynomial_injective {n d : ℕ} :
    Function.Injective (coefficientPolynomial (n := n) (d := d)) := by
  intro c e h
  funext α
  simpa using congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (exponent α)) h

/-- The geometric definition determines every coefficient, even though weights
are only required to be nonnegative. The proof uses the infinite positive
orthant, not a finite-instance check. -/
theorem coefficients_eq_of_evaluate_nonneg {n d : ℕ} {c e : Coefficients n d}
    (h : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → evaluate c t = evaluate e t) : c = e := by
  apply coefficientPolynomial_injective
  apply MvPolynomial.funext_set (fun _ => Set.Ici (0 : ℝ)) (fun _ => Set.Ici_infinite 0)
  intro t ht
  simpa only [← evaluate_eq_polynomial_eval] using h t (fun i => ht i (Set.mem_univ i))

@[simp] theorem degree_exponent {n d : ℕ} (α : MultiIndex n d) :
    (exponent α).degree = d := by
  simpa only [Finsupp.degree_eq_sum, exponent_apply] using α.2

theorem coefficientPolynomial_homogeneous {n d : ℕ} (c : Coefficients n d) :
    (coefficientPolynomial c).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.sum
  intro α _
  exact MvPolynomial.isHomogeneous_monomial (c α) (degree_exponent α)

def weightedSum {n d : ℕ} (K : Fin n → Body d) (t : Fin n → ℝ) : Body d :=
  ∑ i, t i • K i

def bodyVolume {d : ℕ} (K : Body d) : ℝ := volume.real (K : Set (Space d))

def volumeFunction {n d : ℕ} (K : Fin n → Body d) (t : Fin n → ℝ) : ℝ :=
  bodyVolume (weightedSum K t)

/-- The paper's realization condition, with every nonnegative real weight
universally quantified. This does not mean merely matching finitely many samples. -/
def Realizes {n d : ℕ} (K : Fin n → Body d) (c : Coefficients n d) : Prop :=
  ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → evaluate c t = volumeFunction K t

def VolumeLocus (n d : ℕ) : Set (Coefficients n d) := {c | ∃ K, Realizes K c}

@[simp] theorem mem_volumeLocus {n d : ℕ} {c : Coefficients n d} :
    c ∈ VolumeLocus n d ↔ ∃ K, Realizes K c := Iff.rfl

theorem bodyVolume_nonneg {d : ℕ} (K : Body d) : 0 ≤ bodyVolume K :=
  ENNReal.toReal_nonneg

theorem bodyVolume_finite {d : ℕ} (K : Body d) : volume (K : Set (Space d)) ≠ ∞ :=
  K.isCompact.measure_lt_top.ne

theorem bodyVolume_smul {d : ℕ} (K : Body d) {r : ℝ} (hr : 0 ≤ r) :
    bodyVolume (r • K) = r ^ d * bodyVolume K := by
  simp only [bodyVolume, Measure.real, ConvexBody.coe_smul]
  rw [Measure.addHaar_smul_of_nonneg volume hr]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal, pow_nonneg hr]

@[simp] theorem evaluate_one {n d : ℕ} (c : Coefficients n d) :
    evaluate c (fun _ => 1) = ∑ α, c α := by simp [evaluate]

@[simp] theorem weightedSum_one {n d : ℕ} (K : Fin n → Body d) :
    weightedSum K (fun _ => 1) = ∑ i, K i := by simp [weightedSum]

theorem Realizes.sum_coefficients {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) :
    ∑ α, c α = bodyVolume (∑ i, K i) := by
  simpa [volumeFunction] using h (fun _ => 1) (fun _ => zero_le_one)

theorem Realizes.sum_coefficients_nonneg {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) : 0 ≤ ∑ α, c α := by
  rw [h.sum_coefficients]
  exact bodyVolume_nonneg _

theorem Realizes.evaluate_nonneg {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) {t : Fin n → ℝ}
    (ht : ∀ i, 0 ≤ t i) : 0 ≤ evaluate c t := by
  rw [h t ht]
  exact bodyVolume_nonneg _

theorem Realizes.unique {n d : ℕ} {K : Fin n → Body d} {c e : Coefficients n d}
    (hc : Realizes K c) (he : Realizes K e) : c = e := by
  apply coefficients_eq_of_evaluate_nonneg
  intro t ht
  exact (hc t ht).trans (he t ht).symm

end VolumePolynomials
