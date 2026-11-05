module

public import VolumePolynomials.AreaAnalytic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.RingTheory.Polynomial.ScaleRoots

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Filter Polynomial

/-- The precise leading-coefficient argument used in Theorem 7.3. It only uses a polynomial
identity along one sequence and a nonzero rescaled limit; no theorem about algebraic branches
is assumed. -/
theorem radial_polynomial_leadingCoeff (P : Polynomial (Polynomial ℂ))
    (z h δ : ℕ → ℂ) (ζ β : ℂ)
    (hz : Tendsto z atTop (𝓝 ζ)) (hδ : Tendsto δ atTop (𝓝 0))
    (hres : Tendsto (fun n => δ n * h n) atTop (𝓝 β))
    (hrel : ∀ n, P.eval₂ (Polynomial.evalRingHom (z n)) (h n) = 0) :
    P.leadingCoeff.eval ζ * β ^ P.natDegree = 0 := by
  first
  | classical
    let N := P.natDegree
    have heq (n : ℕ) :
        δ n ^ N * P.eval₂ (Polynomial.evalRingHom (z n)) (h n) =
          ∑ k ∈ Finset.range (N + 1),
            (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k) := by
      rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
      simp only [Polynomial.coe_evalRingHom]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : δ n ^ N = δ n ^ k * δ n ^ (N - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkN]
      rw [hpow, mul_pow]
      ring
    have hterm (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
        Tendsto (fun n => (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k))
          atTop (𝓝 (if k = N then P.leadingCoeff.eval ζ * β ^ N else 0)) := by
      have hc := (P.coeff k).continuous.continuousAt.tendsto.comp hz
      have ht := (hc.mul (hres.pow k)).mul (hδ.pow (N - k))
      by_cases he : k = N
      · subst k
        simpa only [N, Function.comp_apply, Nat.sub_self, pow_zero, mul_one,
          if_pos rfl, ite_true, Polynomial.leadingCoeff] using ht
      · have hkN : k < N := lt_of_le_of_ne
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) he
        have hsub : N - k ≠ 0 := Nat.sub_ne_zero_of_lt hkN
        simpa [he, zero_pow hsub] using ht
    have hsum : Tendsto (fun n => ∑ k ∈ Finset.range (N + 1),
        (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k))
        atTop (𝓝 (P.leadingCoeff.eval ζ * β ^ N)) := by
      simpa using tendsto_finsetSum (Finset.range (N + 1)) hterm
    have hzero : Tendsto (fun n => ∑ k ∈ Finset.range (N + 1),
        (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k)) atTop (𝓝 0) := by
      have hf : (fun n => ∑ k ∈ Finset.range (N + 1),
          (P.coeff k).eval (z n) * (δ n * h n) ^ k * δ n ^ (N - k)) = fun _ => 0 := by
        funext n
        rw [← heq n, hrel, mul_zero]
      rw [hf]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hsum hzero

/-- Infinitely many distinct nonzero radial residues rule out every polynomial relation with
complex polynomial coefficients. Density is unnecessary for this algebraic assertion. -/
theorem weightedCauchySeries_no_polynomial_relation {ι : Type*} [Infinite ι]
    (β u : ι → ℂ) (hβ : Summable fun i => ‖β i‖)
    (hβne : ∀ i, β i ≠ 0) (hu : ∀ i, ‖u i‖ = 1) (huinj : Function.Injective u)
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (weightedCauchySeries β u z) = 0 := by
  first
  | intro hrel
    have hroot (j : ι) : P.leadingCoeff.eval ((u j)⁻¹) = 0 := by
      have hrC : Tendsto (fun n => (radialSequence n : ℂ)) atTop (𝓝 1) := by
        simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp radialSequence_tendsto
      have hz : Tendsto (fun n => (radialSequence n : ℂ) / u j) atTop (𝓝 ((u j)⁻¹)) := by
        simpa only [one_div] using hrC.div_const (u j)
      have hδ : Tendsto (fun n => (1 : ℂ) - (radialSequence n : ℂ)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hrC
      have hc := radial_polynomial_leadingCoeff P
        (fun n => (radialSequence n : ℂ) / u j)
        (fun n => weightedCauchySeries β u ((radialSequence n : ℂ) / u j))
        (fun n => 1 - (radialSequence n : ℂ)) ((u j)⁻¹) (β j)
        hz hδ (weighted_radial_residue β u hβ hu huinj radialSequence
          radialSequence_nonneg radialSequence_lt_one radialSequence_tendsto j) (by
          intro n
          apply hrel
          simpa [norm_div, hu, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (radialSequence_nonneg n)] using radialSequence_lt_one n)
      exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ (hβne j))
    have hinj : Function.Injective (fun j => (u j)⁻¹) := inv_injective.comp huinj
    have hinfinite : Set.Infinite {z : ℂ | P.leadingCoeff.IsRoot z} :=
      (Set.infinite_range_of_injective hinj).mono (by
        rintro z ⟨j, rfl⟩
        exact hroot j)
    exact (Polynomial.leadingCoeff_ne_zero.mpr hP)
      (P.leadingCoeff.eq_zero_of_infinite_isRoot hinfinite)

theorem sineGeneratingFunction_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (sineGeneratingFunction θ z) = 0 := by
  first
  | intro hrel
    apply weightedCauchySeries_no_polynomial_relation sineFourierCoefficient (rotationFrequency θ)
      sineFourier_summable_norm sineFourier_ne_zero (rotationFrequency_norm θ)
      (rotationFrequency_injective hθ) P hP
    intro z hz
    rw [← sineGeneratingFunction_eq_cauchy θ z hz]
    exact hrel z hz

/-- Clearing the actual area denominator preserves a nonzero polynomial by `scaleRoots`.
Consequently the complete area formula has no polynomial relation over `ℂ[z]`. -/
theorem areaGeneratingFunction_no_polynomial_relation {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (hsin : Real.sin θ ≠ 0)
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0) :
    ¬ ∀ z : ℂ, ‖z‖ < 1 →
      P.eval₂ (Polynomial.evalRingHom z) (areaGeneratingFunction θ z) = 0 := by
  first
  | intro hrel
    let D : Polynomial ℂ := (1 - X ^ 2) * C (Real.sin θ : ℂ)
    apply sineGeneratingFunction_no_polynomial_relation hθ (P.scaleRoots D)
      (Polynomial.scaleRoots_ne_zero hP D)
    intro z hz
    have hD : D.eval z ≠ 0 := by
      simp only [D, eval_mul, eval_sub, eval_one, eval_pow, eval_X, eval_C]
      exact mul_ne_zero (one_sub_sq_ne_zero_of_norm_lt_one hz) (by exact_mod_cast hsin)
    have hDeval : D.eval z = (1 - z ^ 2) * (Real.sin θ : ℂ) := by
      simp [D]
    have hmul : D.eval z * areaGeneratingFunction θ z = sineGeneratingFunction θ z := by
      rw [areaGeneratingFunction, ← hDeval]
      field_simp [hD]
    have heq := Polynomial.scaleRoots_eval₂_eq_zero (s := D)
      (Polynomial.evalRingHom z) (hrel z hz)
    simpa only [Polynomial.coe_evalRingHom, hmul] using heq

end VolumePolynomials
