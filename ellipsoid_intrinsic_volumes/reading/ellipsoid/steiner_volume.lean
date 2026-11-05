module

public import Ellipsoid.NormalOffsetJacobian
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

noncomputable section

open MeasureTheory Polynomial Set Filter
open scoped BigOperators Pointwise Topology RealInnerProductSpace

namespace EllipsoidVerification

theorem continuousAt_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) (k : ℕ) :
    ContinuousAt (fun z => (normalOffsetJacobianPolynomial a z).coeff k) x := by
  have hs := (hasFDerivAt_axisSupport ha hx).continuousAt
  have hv := (hasFDerivAt_supportPoint ha hx).continuousAt
  have hr := continuous_norm.continuousAt.div hs (axisSupport_pos ha hx).ne'
  have hInv := continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)
  have hc (i : Fin n) : ContinuousAt (fun z : Space n => ‖z‖ / axisSupport a z * a i ^ 2) x :=
    hr.mul continuousAt_const
  have hp (s : Finset (Fin n)) (j : ℕ) : ContinuousAt
      (fun z : Space n => (∏ i ∈ s, (X + C (‖z‖ / axisSupport a z * a i ^ 2))).coeff j) x := by
    apply Polynomial.continuousAt_coeff_prod
    intro i hi l hl
    simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> fun_prop
  simp only [normalOffsetJacobianPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]
  apply (hp Finset.univ k).add
  apply tendsto_finsetSum
  intro i hi
  apply ContinuousAt.mul
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.comp hv).mul
      ((hInv.mul (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt).sub
        (hr.mul ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.comp hv)))
  · exact hp _ _

theorem measurable_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    Measurable (fun z : Space n => (normalOffsetJacobianPolynomial a z).coeff k) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (continuousAt_normalOffsetJacobianPolynomial_coeff ha hx k).continuousWithinAt

theorem bounded_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    ∃ C : ℝ, ∀ x : Space n, ‖(normalOffsetJacobianPolynomial a x).coeff k‖ ≤ C := by
  have hc : ContinuousOn (fun x : Space n => (normalOffsetJacobianPolynomial a x).coeff k)
      (Metric.sphere 0 1) := by
    intro x hx
    apply (continuousAt_normalOffsetJacobianPolynomial_coeff ha _ k).continuousWithinAt
    intro h
    simpa [h] using hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space n) 1).exists_bound_of_continuousOn hc
  refine ⟨max C ‖(normalOffsetJacobianPolynomial a 0).coeff k‖, fun x => ?_⟩
  by_cases hx : x = 0
  · simpa [hx] using le_max_right C ‖(normalOffsetJacobianPolynomial a 0).coeff k‖
  · have hb := hC _ (normalized_mem_unitSphere hx)
    rw [normalOffsetJacobianPolynomial_smul_pos a (inv_pos.mpr (norm_pos_iff.mpr hx))] at hb
    exact hb.trans (le_max_left _ _)

theorem integrableOn_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    IntegrableOn (fun z : Space n => (normalOffsetJacobianPolynomial a z).coeff k)
      (Metric.closedBall 0 1) := by
  obtain ⟨C, hC⟩ := bounded_normalOffsetJacobianPolynomial_coeff ha k
  exact Measure.integrableOn_of_bounded
    (isCompact_closedBall (0 : Space n) 1).measure_lt_top.ne
    (measurable_normalOffsetJacobianPolynomial_coeff ha k).aestronglyMeasurable
    (ae_of_all _ hC)

def normalOffsetVolumePolynomial {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (∫ x in Metric.closedBall (0 : Space n) 1,
    (normalOffsetJacobianPolynomial a x).coeff k.val) * X ^ k.val

theorem normalOffsetVolumePolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) :
    (normalOffsetVolumePolynomial a).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using Nat.le_of_lt_succ k.isLt)

theorem normalOffsetVolumePolynomial_eval {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (t : ℝ) :
    (normalOffsetVolumePolynomial a).eval t =
      ∫ x in Metric.closedBall (0 : Space n) 1, (normalOffsetJacobianPolynomial a x).eval t := by
  simp only [normalOffsetVolumePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp only [← integral_mul_const]
  rw [← integral_finsetSum _ (fun k _ =>
    (integrableOn_normalOffsetJacobianPolynomial_coeff ha k.val).mul_const (t ^ k.val))]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x hx
  calc
    (∑ k : Fin (n + 1), (normalOffsetJacobianPolynomial a x).coeff k.val * t ^ k.val) =
        ∑ k ∈ Finset.range (n + 1), (normalOffsetJacobianPolynomial a x).coeff k * t ^ k :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (normalOffsetJacobianPolynomial a x).coeff k * t ^ k) (n + 1)
    _ = (normalOffsetJacobianPolynomial a x).eval t :=
      (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le
        (normalOffsetJacobianPolynomial_natDegree a x)) t).symm

theorem normalOffset_image_punctured_unitBall {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 ≤ t) :
    normalOffset a t '' (Metric.closedBall (0 : Space n) 1 \ {0}) =
      parallelBody (axisBody a) t \ {0} := by
  rw [← normalOffset_image_unitBall ha ht]
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simpa only [Set.mem_singleton_iff] using normalOffset_ne_zero ha ht hx0
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hx0
    apply hne
    simpa only [Set.mem_singleton_iff, normalOffset_zero] using congrArg (normalOffset a t) hx0

/-- An ellipsoid-specific Steiner formula derived from the actual geometric
normal map and the finite-dimensional change-of-variables theorem. -/
theorem parallelVolume_axisBody_eq_polynomial {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 ≤ t) :
    parallelVolume (axisBody a) t = (normalOffsetVolumePolynomial a).eval t := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hrestrict (s : Set (Space n)) : volume.restrict (s \ {0}) = volume.restrict s := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    simp [hx]
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (s := Metric.closedBall (0 : Space n) 1 \ {0})
    (measurableSet_closedBall.diff (measurableSet_singleton 0))
    (fun x hx => (hasFDerivAt_normalOffset ha t hx.2).hasFDerivWithinAt)
    (normalOffset_injective ha ht).injOn (fun _ : Space n => (1 : ℝ))
  rw [normalOffset_image_punctured_unitBall ha ht] at hcv
  simp only [MeasureTheory.IntegrableOn, hrestrict, smul_eq_mul, mul_one] at hcv
  have hl : (∫ _ in parallelBody (axisBody a) t, (1 : ℝ)) = parallelVolume (axisBody a) t := by
    simp [integral_const, parallelVolume, Measure.real]
  rw [hl] at hcv
  rw [normalOffsetVolumePolynomial_eval ha]
  refine hcv.trans (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Space n))] with x hx
  change |LinearMap.det (normalOffsetDerivative a t x).toLinearMap| =
    (normalOffsetJacobianPolynomial a x).eval t
  rw [det_normalOffsetDerivative, abs_of_pos (normalOffsetMatrix_det_pos ha hx ht),
    normalOffsetJacobianPolynomial_eval ha hx ht]

theorem steinerInterpolant_axisBody {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    steinerInterpolant (axisBody a) = normalOffsetVolumePolynomial a := by
  symm
  unfold steinerInterpolant
  apply Lagrange.eq_interpolate_of_eval_eq
    (v := fun i : Fin (n + 1) => (i.val : ℝ))
    (fun i : Fin (n + 1) => parallelVolume (axisBody a) i.val)
  · intro i hi j hj hij
    exact Fin.ext (Nat.cast_injective hij)
  · apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (Nat.lt_succ_of_le (normalOffsetVolumePolynomial_natDegree a))
  · intro i hi
    exact (parallelVolume_axisBody_eq_polynomial hn ha (Nat.cast_nonneg i.val)).symm

theorem axisBody_hasSteinerFormula {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) : HasSteinerFormula (axisBody a) := by
  intro t ht
  rw [steinerInterpolant_axisBody hn ha]
  exact parallelVolume_axisBody_eq_polynomial hn ha ht

theorem intrinsicVolume_axisBody_eq_jacobianIntegral {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      (∫ x in Metric.closedBall (0 : Space n) 1,
        (normalOffsetJacobianPolynomial a x).coeff (n - k)) / unitBallVolume (n - k) := by
  rw [intrinsicVolume, if_pos hk, steinerInterpolant_axisBody hn ha]
  congr 1
  simp only [normalOffsetVolumePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (⟨n - k, by omega⟩ : Fin (n + 1))]
  · simp
  · intro j hj hne
    have hval : n - k ≠ j.val := fun h => hne (Fin.ext h.symm)
    simp [hval]
  · simp

end EllipsoidVerification
