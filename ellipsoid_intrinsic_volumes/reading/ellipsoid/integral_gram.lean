module

public import Ellipsoid.PositiveJacobians
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set
open scoped BigOperators

namespace EllipsoidVerification

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem integral_gram_posSemidef (μ : Measure Ω) (f : ι → Ω → ℝ)
    (hf : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    Matrix.PosSemidef ((fun i j => ∫ x, f i x * f j x ∂μ) : Matrix ι ι ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, mul_comm]
  · intro c
    have hnonneg : 0 ≤ ∫ x, (∑ i, c i * f i x) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    have heq : (∫ x, (∑ i, c i * f i x) ^ 2 ∂μ) =
        c ⬝ᵥ (((fun i j => ∫ x, f i x * f j x ∂μ) : Matrix ι ι ℝ) *ᵥ c) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => ((hf i j).const_mul (c i * c j)).congr (ae_of_all _ fun x => by ring)))]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => ((hf i j).const_mul (c i * c j)).congr
        (ae_of_all _ fun x => by ring))]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∫ x, c j * f j x * (c i * f i x) ∂μ) =
            ∫ x, (c i * c j) * (f i x * f j x) ∂μ :=
          integral_congr_ae (ae_of_all _ fun x => by ring)
        _ = _ := by rw [integral_const_mul]; ring
    simpa only [star_trivial, heq] using hnonneg

theorem integral_matrix_posSemidef (μ : Measure Ω) (A : Ω → Matrix ι ι ℝ)
    (hA : ∀ᵐ x ∂μ, (A x).PosSemidef)
    (hAi : ∀ i j, Integrable (fun x => A x i j) μ) :
    Matrix.PosSemidef ((fun i j => ∫ x, A x i j ∂μ) : Matrix ι ι ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    exact hx.isHermitian.isSymm.apply i j
  · intro c
    have h : 0 ≤ ∫ x, c ⬝ᵥ (A x *ᵥ c) ∂μ :=
      integral_nonneg_of_ae (hA.mono fun x hx => by
        simpa only [star_trivial, Pi.zero_apply] using hx.dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum] at h ⊢
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => ((hAi i j).mul_const (c j)).const_mul (c i)))] at h
    simp only [integral_finsetSum _ (fun j _ =>
      ((hAi _ j).mul_const (c j)).const_mul _), integral_const_mul, integral_mul_const] at h
    simpa only [star_trivial] using h

/-- The covariance kernel `min(a_i,a_j)` is positive semidefinite for
arbitrary nonnegative times, including coincidences and zero times. -/
theorem minKernel_posSemidef (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Matrix.PosSemidef ((fun i j => min (a i) (a j)) : Matrix ι ι ℝ) := by
  let f : ι → ℝ → ℝ := fun i => (Ioo 0 (a i)).indicator (fun _ => 1)
  have hprod (i j : ι) : (fun t => f i t * f j t) =
      (Ioo 0 (min (a i) (a j))).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases hi : t ∈ Ioo 0 (a i) <;> by_cases hj : t ∈ Ioo 0 (a j)
    · simp only [f, Set.indicator_of_mem hi, Set.indicator_of_mem hj, mul_one]
      rw [Set.indicator_of_mem
        (show t ∈ Ioo 0 (min (a i) (a j)) from ⟨hi.1, lt_min hi.2 hj.2⟩)]
    · simp only [f, Set.indicator_of_mem hi, Set.indicator_of_notMem hj, mul_zero]
      rw [Set.indicator_of_notMem (by simpa [Set.mem_Ioo, lt_min_iff, hi.1, hi.2] using hj)]
    · simp only [f, Set.indicator_of_notMem hi, zero_mul]
      rw [Set.indicator_of_notMem (by
        intro ht
        exact hi ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)]
    · simp only [f, Set.indicator_of_notMem hi, zero_mul]
      rw [Set.indicator_of_notMem (by
        intro ht
        exact hi ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)]
  have hfi (i j : ι) : Integrable (fun t => f i t * f j t) volume := by
    rw [hprod]
    exact (integrableOn_const (by simp [Real.volume_Ioo]) :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 (min (a i) (a j))) ).integrable_indicator
      measurableSet_Ioo
  have h := integral_gram_posSemidef volume f hfi
  have heq (i j : ι) : (∫ t, f i t * f j t) = min (a i) (a j) := by
    rw [hprod, integral_indicator measurableSet_Ioo, integral_const]
    simp only [Real.volume_Ioo, measureReal_def, Measure.restrict_apply_univ,
      sub_zero, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (le_min (ha i) (ha j))]
  simpa only [heq] using h

theorem weighted_minKernel_posSemidef (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Matrix.PosSemidef ((fun i j => v i * v j * min (a i) (a j)) : Matrix ι ι ℝ) := by
  have h := (minKernel_posSemidef a ha).mul_mul_conjTranspose_same (Matrix.diagonal v)
  have heq : Matrix.diagonal v * Matrix.of (fun i j => min (a i) (a j)) *
      (Matrix.diagonal v)ᴴ = Matrix.of (fun i j => v i * v j * min (a i) (a j)) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose,
      star_trivial]
    ring
  change (Matrix.diagonal v * Matrix.of (fun i j => min (a i) (a j)) *
    (Matrix.diagonal v)ᴴ).PosSemidef at h
  rw [heq] at h
  exact h

end EllipsoidVerification
