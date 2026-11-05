module

public import Ellipsoid.GaussianIntegrals
public import Ellipsoid.AxisElementary
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def axisAngularFunction {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n) (x : Space n) : ℝ :=
  (x i) ^ 2 * axisSupport a x ^ (-β)

def axisMellinIntegrand {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  t ^ (β - 1) * (1 + a i ^ 2 * t ^ 2)⁻¹ *
    (∏ j, (1 + a j ^ 2 * t ^ 2)) ^ (-(1 / 2 : ℝ))

def axisLaplaceKernel {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n)
    (s : ℝ) (x : Space n) : ℝ :=
  s ^ (β / 2 - 1) * (x i) ^ 2 *
    Real.exp (-‖x‖ ^ 2 - s * axisSupport a x ^ 2)

theorem continuousOn_axisAngularFunction {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (β : ℝ) (i : Fin n) :
    ContinuousOn (axisAngularFunction a β i) ({0}ᶜ : Set (Space n)) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.pow 2).mul
  exact (continuous_axisSupport a).continuousAt.rpow_const
    (Or.inl (axisSupport_pos ha hx).ne')

theorem homogeneous_axisAngularFunction {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    PositivelyHomogeneous (axisAngularFunction a β i) (2 - β) := by
  intro r hr x
  have hmul : (r * axisSupport a x) ^ (-β) =
      r ^ (-β) * axisSupport a x ^ (-β) :=
    Real.mul_rpow hr.le (show 0 ≤ axisSupport a x from norm_nonneg _)
  have hpow : r ^ (2 - β) = r ^ (2 : ℝ) * r ^ (-β) := by
    simpa only [sub_eq_add_neg] using Real.rpow_add hr (2 : ℝ) (-β)
  simp only [axisAngularFunction, PiLp.smul_apply, smul_eq_mul, axisSupport_smul,
    abs_of_pos hr, mul_pow, hmul, hpow, Real.rpow_two] <;> ring

theorem integrable_axisAngular_gaussian {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ : β < n + 2) (i : Fin n) :
    Integrable (fun x : Space n => axisAngularFunction a β i x * Real.exp (-‖x‖ ^ 2)) :=
  integrable_homogeneous_gaussian (by have := i.isLt; omega) (continuousOn_axisAngularFunction ha β i)
    (homogeneous_axisAngularFunction a β i) (by linarith)

theorem axisLaplaceKernel_nonneg {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n)
    {s : ℝ} (hs : 0 < s) (x : Space n) : 0 ≤ axisLaplaceKernel a β i s x := by
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg _)) (Real.exp_pos _).le

theorem integrable_axisLaplaceKernel_parameter {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ : 0 < β) (i : Fin n)
    {x : Space n} (hx : x ≠ 0) :
    IntegrableOn (fun s => axisLaplaceKernel a β i s x) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := β / 2 - 1) (p := 1) (b := axisSupport a x ^ 2)
    (by linarith) (by norm_num) (sq_pos_of_pos (axisSupport_pos ha hx))
  apply (hi.const_mul ((x i) ^ 2 * Real.exp (-‖x‖ ^ 2))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simp only [axisLaplaceKernel, Real.rpow_one]
  rw [show -‖x‖ ^ 2 - s * axisSupport a x ^ 2 =
    -‖x‖ ^ 2 + -(axisSupport a x ^ 2 * s) by ring, Real.exp_add]
  simp only [neg_mul]
  ring

theorem integral_axisLaplaceKernel_parameter {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ : 0 < β) (i : Fin n)
    {x : Space n} (hx : x ≠ 0) :
    (∫ s in Ioi (0 : ℝ), axisLaplaceKernel a β i s x) =
      Real.Gamma (β / 2) * (axisAngularFunction a β i x * Real.exp (-‖x‖ ^ 2)) := by
  have hp := axisSupport_pos ha hx
  have heq : (∫ s in Ioi (0 : ℝ), axisLaplaceKernel a β i s x) =
      ((x i) ^ 2 * Real.exp (-‖x‖ ^ 2)) *
        ∫ s in Ioi (0 : ℝ), s ^ (β / 2 - 1) * Real.exp (-(axisSupport a x ^ 2 * s)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only [axisLaplaceKernel]
    rw [show -‖x‖ ^ 2 - s * axisSupport a x ^ 2 =
      -‖x‖ ^ 2 + -(axisSupport a x ^ 2 * s) by ring, Real.exp_add]
    ring
  rw [heq, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (sq_pos_of_pos hp)]
  have hpow : (1 / axisSupport a x ^ 2) ^ (β / 2) = axisSupport a x ^ (-β) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_natCast_mul hp.le,
      ← Real.rpow_mul hp.le]
    congr 1
    ring
  rw [hpow]
  dsimp [axisAngularFunction]
  ring

theorem integrable_axisLaplaceKernel {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ0 : 0 < β) (hβn : β < n + 2) (i : Fin n) :
    Integrable (fun p : ℝ × Space n => axisLaplaceKernel a β i p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  have hm : Measurable (fun p : ℝ × Space n => axisLaplaceKernel a β i p.1 p.2) := by
    unfold axisLaplaceKernel axisSupport
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    exact integrable_axisLaplaceKernel_parameter ha hβ0 i hx
  · apply ((integrable_axisAngular_gaussian ha hβn i).const_mul (Real.Gamma (β / 2))).congr
    filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    rw [show (∫ s in Ioi (0 : ℝ), ‖axisLaplaceKernel a β i s x‖) =
      ∫ s in Ioi (0 : ℝ), axisLaplaceKernel a β i s x by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact Real.norm_of_nonneg (axisLaplaceKernel_nonneg a β i hs x)]
    exact (integral_axisLaplaceKernel_parameter ha hβ0 i hx).symm

theorem integral_axisLaplaceKernel_space {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n)
    {s : ℝ} (hs : 0 < s) :
    (∫ x : Space n, axisLaplaceKernel a β i s x) =
      ((Real.sqrt Real.pi) ^ n / 2) *
        (s ^ (β / 2 - 1) * (1 + s * a i ^ 2)⁻¹ *
          (∏ j, (1 + s * a j ^ 2)) ^ (-(1 / 2 : ℝ))) := by
  have hb (j : Fin n) : 0 < 1 + s * a j ^ 2 := by positivity
  have heq (x : Space n) :
      -‖x‖ ^ 2 - s * axisSupport a x ^ 2 = -(∑ j, (1 + s * a j ^ 2) * (x j) ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, axisSupport_sq]
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [axisLaplaceKernel, heq, mul_assoc, integral_const_mul]
  rw [integral_diagonal_gaussian_coordinate_sq _ hb i,
    finite_product_rpow _ (fun j => (hb j).le)]
  ring

def axisLaplaceIntegrand {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  s ^ (β / 2 - 1) * (1 + s * a i ^ 2)⁻¹ *
    (∏ j, (1 + s * a j ^ 2)) ^ (-(1 / 2 : ℝ))

theorem integral_axisLaplace_eq_gaussian {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ0 : 0 < β) (hβn : β < n + 2) (i : Fin n) :
    Real.Gamma (β / 2) *
      (∫ x : Space n, axisAngularFunction a β i x * Real.exp (-‖x‖ ^ 2)) =
      ((Real.sqrt Real.pi) ^ n / 2) * ∫ s in Ioi (0 : ℝ), axisLaplaceIntegrand a β i s := by
  letI : Nonempty (Fin n) := ⟨i⟩
  rw [← integral_const_mul]
  calc
    _ = ∫ x : Space n, ∫ s in Ioi (0 : ℝ), axisLaplaceKernel a β i s x := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : Space n)] with x hx
      exact (integral_axisLaplaceKernel_parameter ha hβ0 i hx).symm
    _ = ∫ s in Ioi (0 : ℝ), ∫ x : Space n, axisLaplaceKernel a β i s x :=
      (integral_integral_swap (integrable_axisLaplaceKernel ha hβ0 hβn i)).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact integral_axisLaplaceKernel_space a β i hs

theorem axisLaplaceIntegrand_square_substitution {n : ℕ} (a : Fin n → ℝ) (β : ℝ)
    (i : Fin n) {t : ℝ} (ht : 0 < t) :
    (2 * t ^ ((2 : ℝ) - 1)) * axisLaplaceIntegrand a β i (t ^ (2 : ℝ)) =
      2 * axisMellinIntegrand a β i t := by
  unfold axisLaplaceIntegrand axisMellinIntegrand
  rw [← Real.rpow_mul ht.le]
  have hp : t ^ (1 : ℝ) * t ^ (2 * (β / 2 - 1)) = t ^ (β - 1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  norm_num only at hp ⊢
  simp only [Real.rpow_one] at hp ⊢
  rw [Real.rpow_two]
  simp only [mul_comm (t ^ 2) (a i ^ 2), mul_comm (t ^ 2) (a _ ^ 2)]
  calc
    _ = 2 * (t * t ^ (2 * (β / 2 - 1))) *
        (1 + a i ^ 2 * t ^ 2)⁻¹ *
          (∏ j, (1 + a j ^ 2 * t ^ 2)) ^ (-(1 / 2 : ℝ)) := by ring
    _ = _ := by rw [hp]; ring

theorem integral_axisLaplaceIntegrand {n : ℕ} (a : Fin n → ℝ) (β : ℝ) (i : Fin n) :
    (∫ s in Ioi (0 : ℝ), axisLaplaceIntegrand a β i s) =
      2 * ∫ t in Ioi (0 : ℝ), axisMellinIntegrand a β i t := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := (2 : ℝ)) (by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact axisLaplaceIntegrand_square_substitution a β i ht

theorem integrableOn_axisMellinIntegrand {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ0 : 0 < β) (hβn : β < n + 2) (i : Fin n) :
    IntegrableOn (axisMellinIntegrand a β i) (Ioi 0) := by
  have h := (integrable_axisLaplaceKernel ha hβ0 hβn i).integral_prod_left
  have hconst : IntegrableOn (fun s => ((Real.sqrt Real.pi) ^ n / 2) *
      axisLaplaceIntegrand a β i s) (Ioi 0) := by
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact integral_axisLaplaceKernel_space a β i hs
  have hL : IntegrableOn (axisLaplaceIntegrand a β i) (Ioi 0) :=
    (integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (by positivity : (Real.sqrt Real.pi) ^ n / 2 ≠ 0))
      (axisLaplaceIntegrand a β i)).mp hconst
  have hT := (integrableOn_Ioi_comp_rpow_iff (axisLaplaceIntegrand a β i)
    (by norm_num : (2 : ℝ) ≠ 0)).mpr hL
  have htwo : IntegrableOn (fun t => 2 * axisMellinIntegrand a β i t) (Ioi 0) := by
    apply hT.congr_fun _ measurableSet_Ioi
    intro t ht
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul] using
      axisLaplaceIntegrand_square_substitution a β i ht
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℝ) ≠ 0))
    (axisMellinIntegrand a β i)).mp htwo

/-- The spherical Mellin identity used in the GSZ formula. Both integrations
are the actual Lebesgue/surface integrations, and their convergence is proved
for the full interval `0 < β < n+2`. -/
theorem sphere_axisAngularFunction_eq_mellin {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {β : ℝ} (hβ0 : 0 < β) (hβn : β < n + 2) (i : Fin n) :
    (∫ u : sphere (0 : Space n) 1, axisAngularFunction a β i u ∂volume.toSphere) =
      (2 * (Real.sqrt Real.pi) ^ n /
        (Real.Gamma (β / 2) * Real.Gamma (((n : ℝ) + 2 - β) / 2))) *
          ∫ t in Ioi (0 : ℝ), axisMellinIntegrand a β i t := by
  have h := integral_axisLaplace_eq_gaussian ha hβ0 hβn i
  rw [integral_homogeneous_gaussian (by have := i.isLt; omega)
    (continuousOn_axisAngularFunction ha β i) (homogeneous_axisAngularFunction a β i)
    (by linarith), integral_axisLaplaceIntegrand] at h
  have hg0 : Real.Gamma (β / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hgn : Real.Gamma (((n : ℝ) + 2 - β) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [show (n : ℝ) + (2 - β) = (n : ℝ) + 2 - β by ring] at h
  field_simp [hg0, hgn]
  nlinarith [h]

end EllipsoidVerification
