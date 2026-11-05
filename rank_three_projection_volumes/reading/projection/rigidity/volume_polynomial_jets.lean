module

public import Projection.AreaEquality
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Real polynomial extensions of actual Minkowski volume

Negative coefficients below belong only to a finite-dimensional multilinear
extension. Actual convex bodies are evaluated only at nonnegative weights,
where the extension is proved equal to the genuine mixed-volume functional.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module Polynomial
open scoped BigOperators Pointwise NNReal
namespace RankThreeProjection.Rigidity
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Finite coordinate extension of the actual mixed volume. -/
def weightedMixedForm {m : ℕ} (B : Fin m → ConvexBody E) (n : ℕ) :
    MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ :=
  ∑ r : Fin n → Fin m,
    mixedVolume μ (fun i => B (r i)) •
      ((MultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compLinearMap
        (fun i => LinearMap.proj (r i)))

theorem weightedMixedForm_apply {m n : ℕ} (B : Fin m → ConvexBody E)
    (w : Fin n → Fin m → ℝ) :
    weightedMixedForm μ B n w =
      ∑ r : Fin n → Fin m,
        (∏ i, w i (r i)) * mixedVolume μ (fun i => B (r i)) := by
  simp [weightedMixedForm, MultilinearMap.mkPiAlgebra_apply, mul_comm]

/-- The real extension agrees with genuine bodies whenever all their
Minkowski coefficients are nonnegative. -/
theorem weightedMixedForm_nonnegative {m n : ℕ} (B : Fin m → ConvexBody E)
    (w : Fin n → Fin m → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    weightedMixedForm μ B n w =
      mixedVolume μ (fun i => ∑ j, w i j • B j) := by
  rw [weightedMixedForm_apply]
  symm
  calc
    _ = ∑ r : Fin n → Fin m,
        mixedVolume μ (fun i => w i (r i) • B (r i)) := by
      let c : Fin n → Fin m → ℝ≥0 := fun i j => NNReal.mk (w i j) (hw i j)
      exact (mixedVolumeMultilinear μ n).map_sum (fun i j => c i j • B j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact mixedVolume_independent_smul μ (fun i => B (r i))
        (fun i => w i (r i)) (fun i => hw i (r i))

theorem weightedMixedForm_single {m n : ℕ} (B : Fin m → ConvexBody E)
    (r : Fin n → Fin m) :
    weightedMixedForm μ B n (fun i => Pi.single (r i) 1) =
      mixedVolume μ (fun i => B (r i)) := by
  rw [weightedMixedForm_apply]
  classical
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _hs hsr
    have hex : ∃ i, s i ≠ r i := by
      by_contra h
      push_neg at h
      exact hsr (funext h)
    obtain ⟨i, hi⟩ := hex
    have hz : (∏ j, (Pi.single (r j) 1 : Fin m → ℝ) (s j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Pi.single_apply, hi, Ne.symm hi]
    rw [hz, zero_mul]
  · simp

theorem weightedMixedForm_symmetric {m n : ℕ} (B : Fin m → ConvexBody E) :
    MultilinearDiagonal.PermutationSymmetric (weightedMixedForm μ B n) := by
  intro w e
  have he : (weightedMixedForm μ B n).domDomCongr e = weightedMixedForm μ B n := by
    apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℝ (Fin m))
    intro r
    simp only [MultilinearMap.domDomCongr_apply, Pi.basisFun_apply]
    change weightedMixedForm μ B n (fun i => Pi.single (r (e i)) 1) =
      weightedMixedForm μ B n (fun i => Pi.single (r i) 1)
    rw [weightedMixedForm_single, weightedMixedForm_single]
    exact mixedVolume_reindex μ (fun i => B (r i)) e
  exact congrArg (fun F : MultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℝ => F w) he

/-- An ordinary polynomial, with no artificial negative dilation of a body. -/
def weightedLinePolynomial {m : ℕ} (B : Fin m → ConvexBody E)
    (n : ℕ) (p x : Fin m → ℝ) : ℝ[X] :=
  ∑ r : Fin n → Fin m,
    C (mixedVolume μ (fun i => B (r i))) *
      ∏ i, (C (p (r i)) + C (x (r i)) * X)

theorem weightedLinePolynomial_eval {m n : ℕ} (B : Fin m → ConvexBody E)
    (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B n p x).eval t =
      weightedMixedForm μ B n (fun _ => p + t • x) := by
  simp only [weightedLinePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, weightedMixedForm_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_comm]
  apply congrArg (fun z : ℝ => z * mixedVolume μ (fun i => B (r i)))
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem weightedLinePolynomial_derivative {m d : ℕ}
    (B : Fin m → ConvexBody E) (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B (d + 1) p x).derivative.eval t =
      (d + 1 : ℝ) * weightedMixedForm μ B (d + 1)
        (Fin.cons x (fun _ : Fin d => p + t • x)) := by
  have hcurve := MultilinearDiagonal.hasDerivAt_diagonal
    (weightedMixedForm μ B (d + 1)) (weightedMixedForm_symmetric μ B) p x t
  have he : (fun s => (weightedLinePolynomial μ B (d + 1) p x).eval s) =
      (fun s : ℝ => weightedMixedForm μ B (d + 1) (fun _ => p + s • x)) :=
    funext (weightedLinePolynomial_eval μ B p x)
  rw [← he] at hcurve
  simpa only [Nat.cast_add, Nat.cast_one] using
    ((weightedLinePolynomial μ B (d + 1) p x).hasDerivAt t).unique hcurve

theorem weightedLinePolynomial_second_derivative {m d : ℕ}
    (B : Fin m → ConvexBody E) (p x : Fin m → ℝ) (t : ℝ) :
    (weightedLinePolynomial μ B (d + 2) p x).derivative.derivative.eval t =
      (d + 2 : ℝ) * (d + 1 : ℝ) * weightedMixedForm μ B (d + 2)
        (Fin.cons x (Fin.cons x (fun _ : Fin d => p + t • x))) := by
  have hcurve := MultilinearDiagonal.hasDerivAt_first_diagonal_derivative
    (weightedMixedForm μ B (d + 2)) (weightedMixedForm_symmetric μ B) p x t
  push_cast at hcurve
  have he : (fun s => (weightedLinePolynomial μ B (d + 2) p x).derivative.eval s) =
      (fun s : ℝ => (d + 2 : ℝ) * weightedMixedForm μ B (d + 2)
        (Fin.cons x (fun _ : Fin (d + 1) => p + s • x))) := by
    funext s
    have h := weightedLinePolynomial_derivative (d := d + 1) μ B p x s
    convert h using 1 <;> push_cast <;> ring
  rw [← he] at hcurve
  have hu := ((weightedLinePolynomial μ B (d + 2) p x).derivative.hasDerivAt t).unique hcurve
  convert hu using 1 <;> push_cast <;> ring

/-- Polynomial along the actual Minkowski ray from K in direction A. -/
def minkowskiRayPolynomial (K A : ConvexBody E) (n : ℕ) : ℝ[X] :=
  weightedLinePolynomial μ ![K,A] n (Pi.single 0 1) (Pi.single 1 1)

theorem minkowskiRayPolynomial_eval {n : ℕ} (hdim : finrank ℝ E = n)
    (K A : ConvexBody E) (t : ℝ) (ht : 0 ≤ t) :
    (minkowskiRayPolynomial μ K A n).eval t =
      μ.real ((K + t • A : ConvexBody E) : Set E) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_eval,
    weightedMixedForm_nonnegative μ ![K,A] _ (by
      intro i j
      fin_cases j <;> simp [ht])]
  have he : (fun _ : Fin n =>
      ∑ j : Fin 2, ((Pi.single 0 1 + t • Pi.single 1 1 : Fin 2 → ℝ) j) •
        (![K,A] : Fin 2 → ConvexBody E) j) = (fun _ => K + t • A) := by
    funext i
    simp [Fin.sum_univ_succ]
  rw [he]
  exact mixedVolume_diagonal μ hdim (K + t • A)

theorem minkowskiRayPolynomial_zero {n : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A n).eval 0 = mixedVolume μ (fun _ : Fin n => K) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_eval]
  simp only [zero_smul, add_zero]
  exact weightedMixedForm_single μ ![K,A] (fun _ : Fin n => (0 : Fin 2))

theorem minkowskiRayPolynomial_first_zero {d : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A (d + 1)).derivative.eval 0 =
      (d + 1 : ℝ) * mixedVolume μ (Fin.cons A (fun _ : Fin d => K)) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_derivative]
  simp only [zero_smul, add_zero]
  congr 1
  have he : (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
      (fun _ : Fin d => Pi.single (0 : Fin 2) (1 : ℝ)) :
        Fin (d + 1) → Fin 2 → ℝ) =
      (fun i : Fin (d + 1) => (Pi.single
        ((Fin.cons (1 : Fin 2) (fun _ : Fin d => 0) : Fin (d + 1) → Fin 2) i)
        (1 : ℝ) : Fin 2 → ℝ)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he, weightedMixedForm_single]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem minkowskiRayPolynomial_second_zero {d : ℕ}
    (K A : ConvexBody E) :
    (minkowskiRayPolynomial μ K A (d + 2)).derivative.derivative.eval 0 =
      (d + 2 : ℝ) * (d + 1 : ℝ) *
        mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) := by
  rw [minkowskiRayPolynomial, weightedLinePolynomial_second_derivative]
  simp only [zero_smul, add_zero]
  congr 1
  have he : (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
      (Fin.cons (Pi.single (1 : Fin 2) (1 : ℝ))
        (fun _ : Fin d => Pi.single (0 : Fin 2) (1 : ℝ))) :
        Fin (d + 2) → Fin 2 → ℝ) =
      (fun i : Fin (d + 2) => (Pi.single ((Fin.cons (1 : Fin 2)
        (Fin.cons 1 (fun _ : Fin d => 0)) : Fin (d + 2) → Fin 2) i) (1 : ℝ) :
          Fin 2 → ℝ)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  rw [he, weightedMixedForm_single]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

end RankThreeProjection.Rigidity

