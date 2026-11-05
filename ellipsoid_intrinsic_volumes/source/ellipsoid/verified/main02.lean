module

public import ellipsoid.verified.main01
public import tau_ceti.analysis.calculus.parametric_integral
public import tau_ceti.analysis.special_functions.beta
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/- Generated ordinary proof stage. See audit/staged_ellipsoid_main/Main02/manifest.json. -/

@[expose] public section

section CanonicalSource10
/- Source: Ellipsoid/AxisElementary.lean -/



noncomputable section

open Polynomial Finset
open scoped BigOperators

namespace EllipsoidVerification

def elementaryOn {ι : Type*} (s : Finset ι) (d : ι → ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ s, (1 + C (d i) * X)).coeff k

theorem elementaryOn_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i) (k : ℕ) : 0 ≤ elementaryOn s d k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
      by_cases hk : k = 0 <;> simp [elementaryOn, Polynomial.coeff_one, hk]
  | @insert i s hi ih =>
      rw [elementaryOn, Finset.prod_insert hi, Polynomial.coeff_mul]
      apply Finset.sum_nonneg
      intro p hp
      apply mul_nonneg
      · have hdi := hd i (Finset.mem_insert_self i s)
        simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
        split_ifs <;> linarith
      · exact ih (fun j hj => hd j (Finset.mem_insert_of_mem hj)) p.2

theorem elementaryOn_scaling {ι : Type*} (s : Finset ι) (d : ι → ℝ) (c : ℝ) (k : ℕ) :
    elementaryOn s (fun i => c * d i) k = c ^ k * elementaryOn s d k := by
  have hp : (∏ i ∈ s, (1 + C (c * d i) * X)) =
      (∏ i ∈ s, (1 + C (d i) * X)).comp (C c * X) := by
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_mul]
    ring
  rw [elementaryOn, hp, Polynomial.comp_C_mul_X_coeff]
  exact mul_comm _ _

theorem coeff_prod_X_add_C {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {k : ℕ} (hk : k ≤ s.card) :
    (∏ i ∈ s, (X + C (d i))).coeff (s.card - k) = elementaryOn s d k := by
  have hone : (1 : ℝ[X]).reverse = 1 := by
    simpa only [Polynomial.C_1] using Polynomial.reverse_C (1 : ℝ)
  have hX : (X : ℝ[X]).reverse = 1 := by
    simpa only [mul_one, hone] using Polynomial.reverse_X_mul (1 : ℝ[X])
  have hrev (s : Finset ι) : (∏ i ∈ s, (X + C (d i))).reverse =
      ∏ i ∈ s, (1 + C (d i) * X) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, hone]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.reverse_mul_of_domain, ih]
      simp [hX]
  have hn : (∏ i ∈ s, (X + C (d i))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_add_C _)]
    simp
  rw [elementaryOn, ← hrev, Polynomial.coeff_reverse, hn, Polynomial.revAt_le hk]

theorem elementaryOn_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {i : ι} (hi : i ∈ s) {k : ℕ} (hk : 0 < k) :
    elementaryOn s d k = elementaryOn (s.erase i) d k + d i * elementaryOn (s.erase i) d (k - 1) := by
  rw [elementaryOn, ← Finset.mul_prod_erase s (fun i => 1 + C (d i) * X) hi,
    add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  congr 1
  rw [show k = (k - 1) + 1 by omega, Polynomial.coeff_X_mul]
  rfl

theorem elementaryOn_euler {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℝ)
    {k : ℕ} (hk : 0 < k) :
    (∑ i ∈ s, d i * elementaryOn (s.erase i) d (k - 1)) = (k : ℝ) * elementaryOn s d k := by
  have h := congrArg (fun p : ℝ[X] => p.coeff (k - 1))
    (Polynomial.derivative_prod_finset (s := s) (f := fun i => 1 + C (d i) * X))
  simp only [Polynomial.coeff_derivative, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Nat.sub_add_cancel hk] at h
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  simpa only [elementaryOn, mul_comm, hcast] using h.symm

theorem axisCoefficientPolynomial_natDegree_le {n : ℕ} (a : Fin n → ℝ) :
    (axisCoefficientPolynomial a).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  have h (i : Fin n) : (1 + C (a i ^ 2) * X).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  exact (Finset.sum_le_sum fun i hi => h i).trans_eq (by simp)

theorem axisCoefficients_admissible {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    coefficientAdmissible (axisCoefficients a) := by
  refine ⟨fun j => elementaryOn_nonneg Finset.univ (fun i => a i ^ 2)
    (fun i hi => sq_nonneg _) _, ?_, ?_⟩
  · simp [axisCoefficients, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]
  · have h := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
      (fun i : Fin n => 1 + C (a i ^ 2) * X) 1 (fun i hi => by
        apply Polynomial.natDegree_add_le_of_degree_le (by simp)
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at h
    change 0 < (axisCoefficientPolynomial a).coeff n
    rw [axisCoefficientPolynomial, h]
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      if_false, one_ne_zero, if_true, zero_add]
    exact Finset.prod_pos fun i _ => sq_pos_of_pos (ha i)

theorem coefficientPolynomial_axisCoefficients {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    coefficientPolynomial (axisCoefficients a) t = ∏ i, (1 + a i ^ 2 * t ^ 2) := by
  have h := Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (axisCoefficientPolynomial_natDegree_le a)) (t ^ 2)
  rw [axisCoefficientPolynomial, Polynomial.eval_prod] at h
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at h
  rw [h]
  simp only [coefficientPolynomial, axisCoefficients, ← pow_mul]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (axisCoefficientPolynomial a).coeff j * t ^ (2 * j)) (n + 1)

def axisA {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (x : Space n) : ℝ :=
  ∑ i, a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)

def axisC {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (x : Space n) : ℝ :=
  ∑ i, a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k

theorem axisC_identity {n k : ℕ} (a : Fin n → ℝ) (hk : 0 < k) (x : Space n) :
    axisC a k x = elementaryOn Finset.univ (fun i => a i ^ 2) k * axisSupport a x ^ 2 -
      ∑ i, (a i ^ 2) ^ 2 * (x i) ^ 2 *
        elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
  rw [axisSupport_sq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [elementaryOn_erase Finset.univ (fun j => a j ^ 2) (Finset.mem_univ i) hk]
  ring

end EllipsoidVerification
end
end CanonicalSource10

section CanonicalSource11
/- Source: Ellipsoid/AngularMellin.lean -/



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
end
end CanonicalSource11

section CanonicalSource12
/- Source: Ellipsoid/CoefficientCompactification.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace EllipsoidVerification

abbrev CompactUnitInterval := {u : ℝ // u ∈ Icc (0 : ℝ) 1}

theorem integral_compactUnitInterval (f : ℝ → ℝ) :
    (∫ u : CompactUnitInterval, f u) = ∫ u in Icc (0 : ℝ) 1, f u :=
  unitInterval.measurePreserving_coe.integral_comp unitInterval.measurableEmbedding_coe f

theorem integrable_compactUnitInterval_iff (f : ℝ → ℝ) :
    Integrable (fun u : CompactUnitInterval => f u) ↔ IntegrableOn f (Icc (0 : ℝ) 1) :=
  unitInterval.measurePreserving_coe.integrable_comp_emb unitInterval.measurableEmbedding_coe

def homogeneousCoefficientPolynomial {n : ℕ} (e : Coefficients n) (u : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), e j * u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)

def positiveCoefficientDomain (n : ℕ) : Set (Coefficients n) :=
  {e | ∀ u ∈ Icc (0 : ℝ) 1, 0 < homogeneousCoefficientPolynomial e u}

def coefficientMellinPower {n : ℕ} (e : Coefficients n) (s r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (r - 1) * (coefficientPolynomial e t) ^ (-s)

def compactMellinWeight (n : ℕ) (s r u : ℝ) : ℝ :=
  u ^ (r - 1) * (1 - u) ^ (2 * n * s - r - 1)

def compactMellinPower {n : ℕ} (e : Coefficients n) (s r : ℝ) : ℝ :=
  ∫ u : CompactUnitInterval, compactMellinWeight n s r u *
    (homogeneousCoefficientPolynomial e u) ^ (-s)

@[fun_prop] theorem contDiff_homogeneousCoefficientPolynomial {n : ℕ}
    (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2) := by
  unfold homogeneousCoefficientPolynomial
  fun_prop

theorem admissible_mem_positiveCoefficientDomain {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) : e ∈ positiveCoefficientDomain n := by
  intro u hu
  have hterm (j : Fin (n + 1)) :
      0 ≤ e j * u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val) := by
    have hej := he.1 j
    have hu0 := hu.1
    have hu1 := sub_nonneg.mpr hu.2
    positivity
  by_cases hu1 : u = 1
  · have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hterm j) (Finset.mem_univ (Fin.last n))
    have hpos : 0 < e (Fin.last n) * u ^ (2 * (Fin.last n).val) *
        (1 - u) ^ (2 * n - 2 * (Fin.last n).val) := by simpa [hu1] using he.2.2
    exact hpos.trans_le h
  · have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      hterm j) (Finset.mem_univ 0)
    have h1u : 0 < 1 - u := sub_pos.mpr (lt_of_le_of_ne hu.2 hu1)
    have hpos : 0 < e 0 * u ^ (2 * (0 : Fin (n + 1)).val) *
        (1 - u) ^ (2 * n - 2 * (0 : Fin (n + 1)).val) := by
      simpa using mul_pos he.2.1 (pow_pos h1u (2 * n))
    exact hpos.trans_le h

theorem isOpen_positiveCoefficientDomain (n : ℕ) : IsOpen (positiveCoefficientDomain n) := by
  rw [isOpen_iff_forall_mem_open]
  intro e he
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  obtain ⟨U, V, hU, hV, heU, hIV, hUV⟩ := generalized_tube_lemma
    (t := Icc (0 : ℝ) 1)
    (isCompact_singleton : IsCompact ({e} : Set (Coefficients n))) isCompact_Icc hW
    (by rintro ⟨x, u⟩ ⟨rfl, hu⟩; exact he u hu)
  refine ⟨U, ?_, hU, heU (mem_singleton e)⟩
  intro x hx u hu
  exact hUV (show (x, u) ∈ U ×ˢ V from ⟨hx, hIV hu⟩)

theorem homogeneousCoefficientPolynomial_compactification {n : ℕ}
    (e : Coefficients n) {u : ℝ} (hu : u ≠ 1) :
    homogeneousCoefficientPolynomial e u =
      (1 - u) ^ (2 * n) * coefficientPolynomial e (u / (1 - u)) := by
  unfold homogeneousCoefficientPolynomial coefficientPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : 2 * j.val + (2 * n - 2 * j.val) = 2 * n := by omega
  have hne : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  calc
    _ = (1 - u) ^ (2 * j.val + (2 * n - 2 * j.val)) *
        (e j * (u / (1 - u)) ^ (2 * j.val)) := by
      rw [div_pow, pow_add]
      field_simp [hne] <;> ring
    _ = _ := by rw [hpow]

def positiveCompactification (u : ℝ) : ℝ := u / (1 - u)

theorem positiveCompactification_image : positiveCompactification '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact div_pos hu.1 (sub_pos.mpr hu.2)
  · intro ht
    change 0 < t at ht
    have hd : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t), ⟨div_pos ht hd,
      (div_lt_one hd).2 (by linarith)⟩, ?_⟩
    dsimp [positiveCompactification]
    have hden : 1 - t / (1 + t) = 1 / (1 + t) := by
      field_simp [hd.ne'] <;> ring
    rw [hden]
    field_simp [hd.ne'] <;> ring

theorem positiveCompactification_injOn : Set.InjOn positiveCompactification (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  dsimp [positiveCompactification] at huv
  have h := (div_eq_div_iff (sub_ne_zero.mpr hu.2.ne') (sub_ne_zero.mpr hv.2.ne')).mp huv
  nlinarith

theorem hasDerivAt_positiveCompactification {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt positiveCompactification ((1 - u) ^ (-2 : ℤ)) u := by
  have hne : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have h := (hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1) hne
  have hf : positiveCompactification = id / (fun x : ℝ => 1 - id x) := by
    funext x
    rfl
  rw [hf]
  convert h using 1 <;>
    simp only [id_eq, mul_one, one_mul, mul_neg, sub_neg_eq_add,
      sub_add_cancel, zpow_neg, zpow_ofNat, one_div]

theorem compactMellinWeight_integrable {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    Integrable (fun u : CompactUnitInterval => compactMellinWeight n s r u) volume := by
  apply (integrable_compactUnitInterval_iff _).2
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff.mpr ⟨hr, sub_pos.mpr hrn⟩

theorem contDiffOn_compactMellinPower {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => compactMellinPower e s r)
      (positiveCoefficientDomain n) := by
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  have hF : ContDiffOn ℝ ∞
      (fun z : Coefficients n × ℝ => (homogeneousCoefficientPolynomial z.1 z.2) ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) ∞).contDiffOn.rpow_const_of_ne
    intro z hz
    exact hz.ne'
  simpa only [compactMellinPower, smul_eq_mul] using
    TauCeti.contDiffOn_integral_smul_of_contDiffOn
      (compactMellinWeight_integrable hr hrn)
      (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hW hF
      (isOpen_positiveCoefficientDomain n)
      (fun e he u => he u u.property)

end EllipsoidVerification
end
end CanonicalSource12

section CanonicalSource13
/- Source: Ellipsoid/MellinCompactification.lean -/



noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace EllipsoidVerification

theorem compactified_mellin_integrand {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (s r : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    |(1 - u) ^ (-2 : ℤ)| *
      (positiveCompactification u ^ (r - 1) *
        coefficientPolynomial e (positiveCompactification u) ^ (-s)) =
      compactMellinWeight n s r u * homogeneousCoefficientPolynomial e u ^ (-s) := by
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  have hq : 0 < homogeneousCoefficientPolynomial e u := he u ⟨hu.1.le, hu.2.le⟩
  have ht : 0 < positiveCompactification u := div_pos hu.1 hv
  have hQ : coefficientPolynomial e (positiveCompactification u) =
      homogeneousCoefficientPolynomial e u / (1 - u) ^ (2 * n) := by
    apply (eq_div_iff (pow_ne_zero _ hv.ne')).2
    simpa only [positiveCompactification, mul_comm] using
      (homogeneousCoefficientPolynomial_compactification e hu.2.ne).symm
  rw [hQ]
  have hlog : Real.log (homogeneousCoefficientPolynomial e u / (1 - u) ^ (2 * n)) =
      Real.log (homogeneousCoefficientPolynomial e u) - (2 * n : ℝ) * Real.log (1 - u) := by
    rw [Real.log_div hq.ne' (pow_ne_zero _ hv.ne'), Real.log_pow]
    norm_cast
  have hjac : |(1 - u) ^ (-2 : ℤ)| = Real.exp (-2 * Real.log (1 - u)) := by
    rw [abs_of_pos (zpow_pos hv _), ← Real.rpow_intCast]
    rw [Real.rpow_def_of_pos hv]
    congr 1
    push_cast
    ring
  rw [hjac, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos (div_pos hq (pow_pos hv _)), hlog,
    show Real.log (positiveCompactification u) = Real.log u - Real.log (1 - u) by
      exact Real.log_div hu.1.ne' hv.ne']
  unfold compactMellinWeight
  rw [Real.rpow_def_of_pos hu.1, Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hq]
  simp only [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem coefficientMellinPower_eq_compactMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) (s r : ℝ) :
    coefficientMellinPower e s r = compactMellinPower e s r := by
  rw [coefficientMellinPower, ← positiveCompactification_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun u hu => (hasDerivAt_positiveCompactification hu.2.ne).hasDerivWithinAt)
      positiveCompactification_injOn]
  rw [compactMellinPower, integral_compactUnitInterval
    (fun u : ℝ => compactMellinWeight n s r u *
      homogeneousCoefficientPolynomial e u ^ (-s)), integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact compactified_mellin_integrand he s r hu

theorem integrable_coefficientMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * coefficientPolynomial e t ^ (-s)) (Ioi 0) := by
  let W : Set (Coefficients n × ℝ) := {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hF : ContinuousOn
      (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous.continuousOn.rpow_const
    intro z hz
    exact Or.inl hz.ne'
  have hi := TauCeti.integrable_smul_of_continuousOn
    (compactMellinWeight_integrable hr hrn)
    (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hF
    (fun u => he u u.property)
  have hic : IntegrableOn (fun u : ℝ => compactMellinWeight n s r u *
      homogeneousCoefficientPolynomial e u ^ (-s)) (Icc (0 : ℝ) 1) := by
    apply (integrable_compactUnitInterval_iff _).1
    simpa only [smul_eq_mul] using hi
  rw [← positiveCompactification_image]
  apply (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (hasDerivAt_positiveCompactification hu.2.ne).hasDerivWithinAt)
    positiveCompactification_injOn _).2
  apply (hic.mono_set Ioo_subset_Icc_self).congr_fun
  · intro u hu
    exact (compactified_mellin_integrand he s r hu).symm
  · exact measurableSet_Ioo

theorem contDiffOn_coefficientMellinPower {n : ℕ} {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => coefficientMellinPower e s r)
      (positiveCoefficientDomain n) :=
  (contDiffOn_compactMellinPower hr hrn).congr
    (fun e he => coefficientMellinPower_eq_compactMellinPower he s r)

theorem integrable_mellinMoment {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))
      (Ioi 0) := by
  apply integrable_coefficientMellinPower (admissible_mem_positiveCoefficientDomain he) hr
  nlinarith

theorem contDiffOn_mellinMoment {n : ℕ} {r : ℝ} (hr : 0 < r) (hrn : r < 3 * n) :
    ContDiffOn ℝ ∞ (fun e : Coefficients n => mellinMoment e r) (positiveCoefficientDomain n) := by
  exact contDiffOn_coefficientMellinPower hr (by nlinarith)

end EllipsoidVerification
end
end CanonicalSource13

section CanonicalSource14
/- Source: Ellipsoid/MellinDifferentiation.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def homogeneousCoefficientEvaluation (n : ℕ) (u : ℝ) : Coefficients n →L[ℝ] ℝ :=
  ∑ j : Fin (n + 1), (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)) •
    ContinuousLinearMap.proj j

@[simp] theorem homogeneousCoefficientEvaluation_apply {n : ℕ} (u : ℝ)
    (e : Coefficients n) :
    homogeneousCoefficientEvaluation n u e = homogeneousCoefficientPolynomial e u := by
  simp [homogeneousCoefficientEvaluation, homogeneousCoefficientPolynomial,
    mul_comm, mul_left_comm, mul_assoc]

@[fun_prop] theorem continuous_homogeneousCoefficientEvaluation (n : ℕ) :
    Continuous (homogeneousCoefficientEvaluation n) := by
  unfold homogeneousCoefficientEvaluation
  fun_prop

theorem hasFDerivAt_homogeneousCoefficientPolynomial {n : ℕ}
    (e : Coefficients n) (u : ℝ) :
    HasFDerivAt (fun e : Coefficients n => homogeneousCoefficientPolynomial e u)
      (homogeneousCoefficientEvaluation n u) e := by
  have heq : (fun d : Coefficients n => homogeneousCoefficientPolynomial d u) =
      homogeneousCoefficientEvaluation n u := by
    funext d
    exact (homogeneousCoefficientEvaluation_apply u d).symm
  rw [heq]
  exact (homogeneousCoefficientEvaluation n u).hasFDerivAt

theorem fderiv_homogeneousCoefficient_rpow {n : ℕ} {e : Coefficients n} {u : ℝ}
    (hu : 0 < homogeneousCoefficientPolynomial e u) (s : ℝ) :
    fderiv ℝ (fun e : Coefficients n => homogeneousCoefficientPolynomial e u ^ (-s)) e =
      (-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n u :=
  ((hasFDerivAt_homogeneousCoefficientPolynomial e u).rpow_const (Or.inl hu.ne')).fderiv

theorem hasFDerivAt_coefficientMellinPower {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    HasFDerivAt (fun e : Coefficients n => coefficientMellinPower e s r)
      (∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
          homogeneousCoefficientEvaluation n u)) e := by
  let W : Set (Coefficients n × ℝ) :=
    {z | 0 < homogeneousCoefficientPolynomial z.1 z.2}
  have hW : IsOpen W := isOpen_lt continuous_const
    (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous
  have hF : ContDiffOn ℝ 1
      (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s)) W := by
    apply (contDiff_homogeneousCoefficientPolynomial (n := n) 1).contDiffOn.rpow_const_of_ne
    intro z hz
    exact hz.ne'
  have h := TauCeti.hasFDerivAt_integral_smul_of_contDiffOn
    (compactMellinWeight_integrable hr hrn)
    (continuous_subtype_val : Continuous (fun u : CompactUnitInterval => (u : ℝ))) hW hF
    (fun u => he u u.property)
  have hderiv :
      (∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        fderiv ℝ (fun e : Coefficients n => homogeneousCoefficientPolynomial e u ^ (-s)) e) =
      ∫ u : CompactUnitInterval, compactMellinWeight n s r u •
        ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
          homogeneousCoefficientEvaluation n u) := by
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      dsimp only
      rw [fderiv_homogeneousCoefficient_rpow (he u u.property) s]
  rw [hderiv] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_positiveCoefficientDomain n).mem_nhds he] with e he
  exact coefficientMellinPower_eq_compactMellinPower he s r

set_option backward.isDefEq.respectTransparency false in
theorem compact_mellin_derivative_integrable {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    Integrable (fun u : CompactUnitInterval => compactMellinWeight n s r u •
      ((-s * homogeneousCoefficientPolynomial e u ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n u)) volume := by
  apply TauCeti.integrable_smul_of_continuousOn
    (compactMellinWeight_integrable hr hrn) continuous_subtype_val
    (W := {z : Coefficients n × ℝ | 0 < homogeneousCoefficientPolynomial z.1 z.2})
    (F := fun z : Coefficients n × ℝ =>
      (-s * homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1)) •
        homogeneousCoefficientEvaluation n z.2)
    (x := e)
  · have hpow : ContinuousOn
        (fun z : Coefficients n × ℝ => homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1))
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} :=
      (contDiff_homogeneousCoefficientPolynomial (n := n) 0).continuous.continuousOn.rpow_const
        (fun z hz => Or.inl hz.ne')
    have hscalar : ContinuousOn
        (fun z : Coefficients n × ℝ => -s * homogeneousCoefficientPolynomial z.1 z.2 ^ (-s - 1))
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} := by
      exact (continuousOn_const (c := -s)).fun_mul hpow
    have hlinear : ContinuousOn
        (fun z : Coefficients n × ℝ => homogeneousCoefficientEvaluation n z.2)
        {z | 0 < homogeneousCoefficientPolynomial z.1 z.2} :=
      ((continuous_homogeneousCoefficientEvaluation n).comp continuous_snd).continuousOn
    exact hscalar.fun_smul hlinear
  · intro u
    exact he u u.property

theorem compact_mellin_shift_identity (n : ℕ) (s r : ℝ) (j : Fin (n + 1))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    compactMellinWeight n s r u *
      (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)) =
        compactMellinWeight n (s + 1) (r + 2 * j.val) u := by
  have hv : 0 < 1 - u := sub_pos.mpr hu.2
  unfold compactMellinWeight
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [show u ^ (r - 1) * (1 - u) ^ (2 * n * s - r - 1) *
      (u ^ ((2 * j.val : ℕ) : ℝ) * (1 - u) ^ ((2 * n - 2 * j.val : ℕ) : ℝ)) =
      (u ^ (r - 1) * u ^ ((2 * j.val : ℕ) : ℝ)) *
        ((1 - u) ^ (2 * n * s - r - 1) *
          (1 - u) ^ ((2 * n - 2 * j.val : ℕ) : ℝ)) by ring]
  rw [← Real.rpow_add hu.1, ← Real.rpow_add hv]
  rw [Nat.cast_sub (by omega : 2 * j.val ≤ 2 * n)]
  congr 1 <;> push_cast <;> ring

/-- Every partial derivative of the Mellin transform is another convergent
Mellin transform. The allowed range is precisely `0 < r < 2ns`. -/
theorem fderiv_coefficientMellinPower_single {n : ℕ} {e : Coefficients n}
    (he : e ∈ positiveCoefficientDomain n) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) (j : Fin (n + 1)) :
    fderiv ℝ (fun e : Coefficients n => coefficientMellinPower e s r) e (Pi.single j 1) =
      -s * coefficientMellinPower e (s + 1) (r + 2 * j.val) := by
  rw [(hasFDerivAt_coefficientMellinPower he hr hrn).fderiv,
    ContinuousLinearMap.integral_apply (compact_mellin_derivative_integrable he hr hrn),
    coefficientMellinPower_eq_compactMellinPower he, compactMellinPower, ← integral_const_mul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    homogeneousCoefficientEvaluation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [integral_compactUnitInterval (fun u : ℝ =>
      compactMellinWeight n s r u *
        (-s * homogeneousCoefficientPolynomial e u ^ (-s - 1) *
          (u ^ (2 * j.val) * (1 - u) ^ (2 * n - 2 * j.val)))),
    integral_compactUnitInterval (fun u : ℝ =>
      -s * (compactMellinWeight n (s + 1) (r + 2 * j.val) u *
        homogeneousCoefficientPolynomial e u ^ (-(s + 1)))),
    integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [show -(s + 1) = -s - 1 by ring,
    ← compact_mellin_shift_identity n s r j hu]
  ring

end EllipsoidVerification
end
end CanonicalSource14

section CanonicalSource15
/- Source: Ellipsoid/MellinIntegrationByParts.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

theorem hasDerivAt_coefficientPolynomial {n : ℕ} (e : Coefficients n) (t : ℝ) :
    HasDerivAt (coefficientPolynomial e) (coefficientDerivative e t) t := by
  unfold coefficientPolynomial coefficientDerivative
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [id_eq, mul_one, one_mul, Nat.cast_mul, Nat.cast_ofNat,
    mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).fun_pow (2 * j.val)).const_mul (e j))

theorem coefficientPolynomial_mul_rpow {n : ℕ} (e : Coefficients n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) :
    t ^ r * coefficientPolynomial e t =
      ∑ j : Fin (n + 1), e j * t ^ (r + 2 * j.val) := by
  unfold coefficientPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add ht]
  congr 2
  push_cast
  ring

theorem coefficientDerivative_mul_rpow {n : ℕ} (e : Coefficients n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) :
    t ^ r * coefficientDerivative e t =
      ∑ j : Fin (n + 1), (2 * j.val : ℝ) * e j * t ^ (r + 2 * j.val - 1) := by
  unfold coefficientDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j.val = 0
  · simp [hj0]
  · rw [← Real.rpow_natCast]
    have hj1 : 1 ≤ 2 * j.val := by omega
    rw [Nat.cast_sub hj1]
    push_cast
    rw [show t ^ r * ((2 * (j.val : ℝ)) * e j * t ^ (2 * (j.val : ℝ) - 1)) =
        (2 * (j.val : ℝ)) * e j * (t ^ r * t ^ (2 * (j.val : ℝ) - 1)) by ring,
      ← Real.rpow_add ht]
    congr 2
    ring

theorem mellinBoundary_derivative {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (s r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s))
      (∑ j : Fin (n + 1), (r - 2 * s * j.val) * e j *
        (t ^ (r + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(s + 1)))) t := by
  have hq := coefficientPolynomial_pos he t
  have hd := (Real.hasDerivAt_rpow_const (Or.inl ht.ne') :
      HasDerivAt (fun t : ℝ => t ^ r) (r * t ^ (r - 1)) t).mul
    ((hasDerivAt_coefficientPolynomial e t).rpow_const (p := -s) (Or.inl hq.ne'))
  convert hd using 1
  symm
  have hpow : coefficientPolynomial e t ^ (-s) =
      coefficientPolynomial e t * coefficientPolynomial e t ^ (-(s + 1)) := by
    calc
      _ = coefficientPolynomial e t ^ (1 : ℝ) *
          coefficientPolynomial e t ^ (-(s + 1)) := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  have h1 := coefficientPolynomial_mul_rpow e (r - 1) ht
  have h2 := coefficientDerivative_mul_rpow e r ht
  have hrewrite :
      r * t ^ (r - 1) *
          (coefficientPolynomial e t * coefficientPolynomial e t ^ (-(s + 1))) +
        t ^ r * (coefficientDerivative e t * -s * coefficientPolynomial e t ^ (-s - 1)) =
      (r * (t ^ (r - 1) * coefficientPolynomial e t) -
        s * (t ^ r * coefficientDerivative e t)) * coefficientPolynomial e t ^ (-(s + 1)) := by
    rw [show -s - 1 = -(s + 1) by ring]
    ring
  rw [hrewrite, h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r - 1 + 2 * (j.val : ℝ) = r + 2 * j.val - 1 by ring]
  ring

theorem mellinBoundary_tendsto_atTop {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {s r : ℝ} (hs : 0 < s) (hr : r < 2 * n * s) :
    Tendsto (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ t : ℝ in atTop,
      0 ≤ t ^ r * coefficientPolynomial e t ^ (-s) ∧
        t ^ r * coefficientPolynomial e t ^ (-s) ≤
          e (Fin.last n) ^ (-s) * t ^ (-(2 * n * s - r)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine ⟨mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg
      (coefficientPolynomial_pos he t).le _), ?_⟩
    have hp := Real.rpow_le_rpow_of_nonpos
      (mul_pos he.2.2 (pow_pos ht (2 * n)))
      (coefficientPolynomial_ge_leading he.1 t) (neg_nonpos.mpr hs.le)
    have hp' := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le r)
    convert hp' using 1
    rw [Real.mul_rpow he.2.2.le (pow_nonneg ht.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le]
    rw [show t ^ r * (e (Fin.last n) ^ (-s) * t ^ (((2 * n : ℕ) : ℝ) * -s)) =
        e (Fin.last n) ^ (-s) * (t ^ r * t ^ (((2 * n : ℕ) : ℝ) * -s)) by ring,
      ← Real.rpow_add ht]
    congr 2
    push_cast
    ring
  have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).const_mul
    (e (Fin.last n) ^ (-s))
  simpa using squeeze_zero' (hbound.mono fun _ h => h.1)
    (hbound.mono fun _ h => h.2) (by simpa only [mul_zero] using hlim)

/-- The complete integration-by-parts recurrence for positive Mellin
parameters. Every term is integrable, and both boundary values vanish. -/
theorem coefficientMellinPower_recurrence {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {s r : ℝ}
    (hr : 0 < r) (hrn : r < 2 * n * s) :
    ∑ j : Fin (n + 1), (r - 2 * s * j.val) * e j *
      coefficientMellinPower e (s + 1) (r + 2 * j.val) = 0 := by
  have hs : 0 < s := by
    by_contra hs
    have hn := Nat.cast_nonneg (α := ℝ) n
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (2 : ℝ) * n)
      (le_of_not_gt hs)
    linarith
  have hi (j : Fin (n + 1)) :
      IntegrableOn (fun t : ℝ => t ^ (r + 2 * j.val - 1) *
        coefficientPolynomial e t ^ (-(s + 1))) (Ioi 0) := by
    apply integrable_coefficientMellinPower (admissible_mem_positiveCoefficientDomain he)
    · positivity
    · have hj : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      nlinarith
  have hsum : IntegrableOn (fun t : ℝ => ∑ j : Fin (n + 1),
      (r - 2 * s * j.val) * e j *
        (t ^ (r + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(s + 1)))) (Ioi 0) :=
    integrable_finsetSum _ fun j _ => (hi j).const_mul _
  have hcont : ContinuousWithinAt
      (fun t : ℝ => t ^ r * coefficientPolynomial e t ^ (-s)) (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    apply (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).mul
    exact (continuous_coefficientPolynomial e).continuousAt.rpow_const
      (Or.inl (coefficientPolynomial_pos he 0).ne')
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun t ht => mellinBoundary_derivative he s r ht) hsum
    (mellinBoundary_tendsto_atTop he hs hrn)
  simp only [Real.zero_rpow hr.ne', zero_mul, sub_zero] at h
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)] at h
  simpa only [integral_const_mul, coefficientMellinPower] using h

end EllipsoidVerification
end
end CanonicalSource15

section CanonicalSource16
/- Source: Ellipsoid/AxisRationalIdentity.lean -/



noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace EllipsoidVerification

def axisRational {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (u : ℝ) : ℝ :=
  ∑ i, a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) /
    (1 + a i ^ 2 * u)

def axisHeadPolynomial {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ l ∈ Finset.range k, C ((axisCoefficientPolynomial a).coeff l) * X ^ l

theorem elementaryOn_zero {ι : Type*} (s : Finset ι) (d : ι → ℝ) :
    elementaryOn s d 0 = 1 := by
  simp [elementaryOn, Polynomial.coeff_zero_prod]

theorem axisRational_one {n : ℕ} (a : Fin n → ℝ) (u : ℝ) :
    axisRational a 1 u = ∑ i, a i ^ 2 / (1 + a i ^ 2 * u) := by
  simp [axisRational, elementaryOn_zero]

theorem axisRational_recurrence {n k : ℕ} (a : Fin n → ℝ) (hk : 0 < k)
    {u : ℝ} (hu : 0 ≤ u) :
    u * axisRational a (k + 1) u - axisRational a k u =
      (axisCoefficientPolynomial a).coeff k * (u * axisRational a 1 u - k) := by
  let e := elementaryOn Finset.univ (fun i => a i ^ 2) k
  have hden (i : Fin n) : 1 + a i ^ 2 * u ≠ 0 := by positivity
  have heach (i : Fin n) :
      u * (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k /
        (1 + a i ^ 2 * u)) -
      a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) /
        (1 + a i ^ 2 * u) =
      e * u * (a i ^ 2 / (1 + a i ^ 2 * u)) -
        a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
    dsimp [e]
    rw [elementaryOn_erase Finset.univ (fun j => a j ^ 2) (Finset.mem_univ i) hk]
    field_simp [hden i]
    ring
  rw [axisRational, axisRational, Nat.add_sub_cancel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [heach]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, elementaryOn_euler _ _ hk, axisRational_one]
  change e * u * _ - (k : ℝ) * e = e * (u * _ - k)
  ring

theorem axisHeadPolynomial_succ {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    axisHeadPolynomial a (k + 1) = axisHeadPolynomial a k +
      C ((axisCoefficientPolynomial a).coeff k) * X ^ k := by
  exact Finset.sum_range_succ _ _

theorem axisHeadPolynomial_wronskian {n k : ℕ} (a : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * axisRational a (k + 1) u =
      (axisHeadPolynomial a (k + 1)).eval u * axisRational a 1 u -
        (axisHeadPolynomial a (k + 1)).derivative.eval u := by
  induction k with
  | zero =>
      simp [axisHeadPolynomial, axisCoefficientPolynomial, Polynomial.coeff_zero_prod]
  | succ k ih =>
      have hr := axisRational_recurrence a (k := k + 1) (by omega) hu
      rw [axisHeadPolynomial_succ a (k + 1)]
      simp only [Polynomial.eval_add,
        Polynomial.derivative_add, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ] at hr ⊢
      linear_combination u ^ k * hr + ih

theorem axisCoefficientPolynomial_derivative_eval {n : ℕ} (a : Fin n → ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    (axisCoefficientPolynomial a).derivative.eval u =
      (axisCoefficientPolynomial a).eval u * axisRational a 1 u := by
  have hden (i : Fin n) : 1 + a i ^ 2 * u ≠ 0 := by positivity
  rw [axisCoefficientPolynomial, Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum, Polynomial.eval_prod, axisRational_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, zero_add, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => 1 + a j ^ 2 * u) (Finset.mem_univ i)]
  field_simp [hden i]
  simp_rw [mul_comm u]
  ring

theorem coefficientHead_axisCoefficients {n k : ℕ} (a : Fin n → ℝ) (hk : k ≤ n + 1) (t : ℝ) :
    coefficientHead (axisCoefficients a) k t = (axisHeadPolynomial a k).eval (t ^ 2) := by
  simp only [coefficientHead, axisCoefficients, axisHeadPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ =>
    if l < k then (axisCoefficientPolynomial a).coeff l * t ^ (2 * l) else 0) (n + 1)]
  have hsub : Finset.range k ⊆ Finset.range (n + 1) := Finset.range_mono hk
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro l hl
    simp [Finset.mem_range.mp hl]
  · intro l hl hlk
    simp [show ¬ l < k from fun h => hlk (Finset.mem_range.mpr h)]

theorem hasDerivAt_coefficientHead {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) :
    HasDerivAt (coefficientHead e k) (coefficientHeadDerivative e k t) t := by
  unfold coefficientHead coefficientHeadDerivative
  apply HasDerivAt.fun_sum
  intro l hl
  by_cases h : l.val < k
  · simp only [h, if_true]
    simpa only [Pi.pow_apply, id_eq, mul_one, one_mul, Nat.cast_mul, Nat.cast_ofNat,
      mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id t).pow (2 * l.val)).const_mul (e l)
  · simp only [h, if_false]
    exact hasDerivAt_const t 0

theorem coefficientDerivative_axisCoefficients {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    coefficientDerivative (axisCoefficients a) t =
      2 * t * (axisCoefficientPolynomial a).derivative.eval (t ^ 2) := by
  have hp : coefficientPolynomial (axisCoefficients a) =
      fun z => (axisCoefficientPolynomial a).eval (z ^ 2) := by
    funext z
    rw [coefficientPolynomial_axisCoefficients]
    simp only [axisCoefficientPolynomial, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h := ((axisCoefficientPolynomial a).hasDerivAt (t ^ 2)).comp t
    ((hasDerivAt_id t).pow 2)
  have h₀ : HasDerivAt (fun z : ℝ => (axisCoefficientPolynomial a).eval (z ^ 2))
      ((axisCoefficientPolynomial a).derivative.eval (t ^ 2) * (2 * t)) t := by
    simpa only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one] using h
  have h' := hasDerivAt_coefficientPolynomial (axisCoefficients a) t
  rw [hp] at h'
  calc
    _ = (axisCoefficientPolynomial a).derivative.eval (t ^ 2) * (2 * t) := h'.unique h₀
    _ = _ := by ring

theorem coefficientHeadDerivative_axisCoefficients {n k : ℕ} (a : Fin n → ℝ)
    (hk : k ≤ n + 1) (t : ℝ) :
    coefficientHeadDerivative (axisCoefficients a) k t =
      2 * t * (axisHeadPolynomial a k).derivative.eval (t ^ 2) := by
  have h := ((axisHeadPolynomial a k).hasDerivAt (t ^ 2)).comp t
    ((hasDerivAt_id t).pow 2)
  have h₀ : HasDerivAt (fun z : ℝ => (axisHeadPolynomial a k).eval (z ^ 2))
      ((axisHeadPolynomial a k).derivative.eval (t ^ 2) * (2 * t)) t := by
    simpa only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_one] using h
  have hp : coefficientHead (axisCoefficients a) k =
      fun z => (axisHeadPolynomial a k).eval (z ^ 2) := by
    funext z
    exact coefficientHead_axisCoefficients a hk z
  have h' := hasDerivAt_coefficientHead (axisCoefficients a) k t
  rw [hp] at h'
  calc
    _ = (axisHeadPolynomial a k).derivative.eval (t ^ 2) * (2 * t) := h'.unique h₀
    _ = _ := by ring

theorem coefficientTransform_integrand_axis {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℝ) * t ^ (-(k : ℝ)) *
      (coefficientHead (axisCoefficients a) k t * coefficientDerivative (axisCoefficients a) t -
        coefficientHeadDerivative (axisCoefficients a) k t * coefficientPolynomial (axisCoefficients a) t) *
      coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) =
      t ^ ((k : ℝ) - 1) * axisRational a k (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  have hq := coefficientPolynomial_pos (axisCoefficients_admissible a ha) t
  have hQ : (axisCoefficientPolynomial a).eval (t ^ 2) =
      coefficientPolynomial (axisCoefficients a) t := by
    simp only [coefficientPolynomial_axisCoefficients, axisCoefficientPolynomial,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
  have hW := axisHeadPolynomial_wronskian (k := k - 1) a (sq_nonneg t)
  rw [Nat.sub_add_cancel hk] at hW
  rw [coefficientHead_axisCoefficients a (by omega), coefficientDerivative_axisCoefficients,
    coefficientHeadDerivative_axisCoefficients a (by omega),
    axisCoefficientPolynomial_derivative_eval a (sq_nonneg t), hQ]
  have hwronskian :
      (axisHeadPolynomial a k).eval (t ^ 2) *
          (2 * t * (coefficientPolynomial (axisCoefficients a) t * axisRational a 1 (t ^ 2))) -
        (2 * t * (axisHeadPolynomial a k).derivative.eval (t ^ 2)) *
          coefficientPolynomial (axisCoefficients a) t =
      2 * t * coefficientPolynomial (axisCoefficients a) t *
        ((t ^ 2) ^ (k - 1) * axisRational a k (t ^ 2)) := by
    rw [hW]
    ring
  rw [hwronskian]
  have htPow : t ^ (-(k : ℝ)) * t * (t ^ 2) ^ (k - 1) = t ^ ((k : ℝ) - 1) := by
    have hnat : (t ^ 2) ^ (k - 1) = t ^ ((2 : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      calc
        _ = (t ^ (2 : ℕ)) ^ ((k - 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast (t ^ (2 : ℕ)) (k - 1)).symm
        _ = _ := (Real.rpow_natCast_mul ht.le 2 ((k - 1 : ℕ) : ℝ)).symm
    calc
      _ = (t ^ (-(k : ℝ)) * t ^ (1 : ℝ)) *
          t ^ ((2 : ℝ) * ((k - 1 : ℕ) : ℝ)) := by rw [hnat, Real.rpow_one]
      _ = t ^ (-(k : ℝ) + 1 + 2 * ((k - 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add ht, ← Real.rpow_add ht]
      _ = _ := by
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        ring
  have hqPow : coefficientPolynomial (axisCoefficients a) t *
      coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) =
      coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = coefficientPolynomial (axisCoefficients a) t ^ (1 : ℝ) *
          coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = coefficientPolynomial (axisCoefficients a) t ^ ((1 : ℝ) + -(3 / 2 : ℝ)) :=
        (Real.rpow_add hq 1 (-(3 / 2 : ℝ))).symm
      _ = _ := by norm_num
  calc
    _ = (t ^ (-(k : ℝ)) * t * (t ^ 2) ^ (k - 1)) * axisRational a k (t ^ 2) *
      (coefficientPolynomial (axisCoefficients a) t *
        coefficientPolynomial (axisCoefficients a) t ^ (-(3 / 2 : ℝ))) := by ring
    _ = _ := by rw [htPow, hqPow]

end EllipsoidVerification
end
end CanonicalSource16

section CanonicalSource17
/- Source: Ellipsoid/JacobianSphereCoefficient.lean -/



noncomputable section

open MeasureTheory Polynomial Set Metric
open scoped BigOperators

namespace EllipsoidVerification

theorem normalOffsetJacobianPolynomial_coeff_unit {n k : ℕ}
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n)
    {x : Space n} (hx : ‖x‖ = 1) :
    (normalOffsetJacobianPolynomial a x).coeff (n - k) =
      axisA a k x / axisSupport a x ^ k + axisC a k x / axisSupport a x ^ (k + 2) := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  let h := axisSupport a x
  have hh : 0 < h := axisSupport_pos ha hx0
  have hcoef (s : Finset (Fin n)) (l : ℕ) (hl : l ≤ s.card) :
      (∏ i ∈ s, (X + C (h⁻¹ * a i ^ 2))).coeff (s.card - l) =
        (h⁻¹) ^ l * elementaryOn s (fun i => a i ^ 2) l := by
    rw [coeff_prod_X_add_C s _ hl, elementaryOn_scaling]
  have hfirst : (∏ i : Fin n, (X + C (h⁻¹ * a i ^ 2))).coeff (n - k) =
      elementaryOn Finset.univ (fun i => a i ^ 2) k / h ^ k := by
    simpa [div_eq_mul_inv, inv_pow, mul_comm] using
      hcoef Finset.univ k (by simpa using hkn)
  have hminor (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k) =
        (h⁻¹) ^ (k - 1) * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1) := by
    have hcard : (Finset.univ.erase i : Finset (Fin n)).card = n - 1 := by simp
    have h := hcoef (Finset.univ.erase i) (k - 1) (by rw [hcard]; omega)
    simpa only [hcard, show n - 1 - (k - 1) = n - k by omega] using h
  have hv (i : Fin n) : supportPoint a x i = a i ^ 2 * x i / h := by
    simp only [supportPoint_eq, PiLp.smul_apply, axisMap, PiLp.toLp_apply, smul_eq_mul]
    dsimp [h]
    ring
  have hterm (i : Fin n) :
      supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        ((h⁻¹) ^ (k - 1) * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) =
      (a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) / h ^ k -
      ((a i ^ 2) ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) /
        h ^ (k + 2) := by
    rw [hv]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hsub : l.succ - 1 = l := by omega
    simp only [hsub, inv_pow, pow_succ]
    field_simp [hh.ne']
  have hsum :
      (∑ i : Fin n, supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k)) =
      axisA a k x / h ^ k -
        (∑ i : Fin n, (a i ^ 2) ^ 2 * (x i) ^ 2 *
          elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) / h ^ (k + 2) := by
    calc
      _ = ∑ i : Fin n,
          ((a i ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i)
            (fun j => a j ^ 2) (k - 1)) / h ^ k -
          ((a i ^ 2) ^ 2 * (x i) ^ 2 * elementaryOn (Finset.univ.erase i)
            (fun j => a j ^ 2) (k - 1)) / h ^ (k + 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hminor i]
        exact hterm i
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
        rfl
  simp only [normalOffsetJacobianPolynomial, hx, one_div, inv_one, one_mul,
    Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  change (∏ i : Fin n, (X + C (h⁻¹ * a i ^ 2))).coeff (n - k) +
      (∑ i : Fin n, supportPoint a x i * (x i - h⁻¹ * supportPoint a x i) *
        (∏ j ∈ Finset.univ.erase i, (X + C (h⁻¹ * a j ^ 2))).coeff (n - k)) = _
  rw [hfirst, hsum, axisC_identity a hk x]
  change _ = axisA a k x / h ^ k + _ / h ^ (k + 2)
  rw [pow_add]
  dsimp [axisA]
  field_simp [hh.ne']
  ring

theorem intrinsicVolume_axisBody_eq_sphereJacobian {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      ((n : ℝ) * unitBallVolume (n - k))⁻¹ *
        ∫ u : sphere (0 : Space n) 1,
          (normalOffsetJacobianPolynomial a (u : Space n)).coeff (n - k) ∂volume.toSphere := by
  rw [intrinsicVolume_axisBody_eq_jacobianIntegral hn ha hk,
    integral_homogeneous_zero_unitBall hn
      (integrableOn_normalOffsetJacobianPolynomial_coeff ha (n - k))
      (fun r hr x => by simp only [normalOffsetJacobianPolynomial_smul_pos a hr,
        Real.rpow_zero, one_mul])]
  rw [_root_.mul_inv_rev]
  ring

theorem intrinsicVolume_axisBody_eq_sphere {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      ((n : ℝ) * unitBallVolume (n - k))⁻¹ *
        ∫ u : sphere (0 : Space n) 1,
          (axisA a k u / axisSupport a u ^ k + axisC a k u / axisSupport a u ^ (k + 2))
            ∂volume.toSphere := by
  rw [intrinsicVolume_axisBody_eq_sphereJacobian hn ha hkn]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun u => normalOffsetJacobianPolynomial_coeff_unit ha hk hkn
    (by simpa using u.property)

end EllipsoidVerification
end
end CanonicalSource17

section CanonicalSource18
/- Source: Ellipsoid/GeometricInvariance.lean -/



noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

@[simp] theorem unitBallVolume_zero : unitBallVolume 0 = 1 := by
  simp [unitBallVolume, volume_euclideanSpace_eq_dirac]

theorem unitBallVolume_eq (n : ℕ) :
    unitBallVolume n = (Real.sqrt Real.pi) ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [unitBallVolume, EuclideanSpace.volume_closedBall (Fin (n + 1))]
    simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
    exact ENNReal.toReal_ofReal (by positivity)

theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := by
  rw [unitBallVolume_eq]
  positivity

theorem parallelBody_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    (K : Set (Space n)) (r : ℝ) :
    parallelBody ((fun x => c + U x) '' K) r =
      (fun x => c + U x) '' parallelBody K r := by
  ext z
  constructor
  · rintro ⟨v, ⟨x, hx, rfl⟩, w, hw, heq⟩
    refine ⟨x + U.symm w, ⟨x, hx, U.symm w, ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, U.symm.norm_map] using hw
    · simpa only [map_add, U.apply_symm_apply, add_assoc] using heq
  · rintro ⟨v, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨c + U x, ⟨x, hx, rfl⟩, U w, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, U.norm_map] using hw
    · simp only [map_add, add_assoc]

theorem volume_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) :
    volume ((fun x => c + U x) '' K) = volume K := by
  have hMP : MeasurePreserving (fun x : Space n => c + U x) :=
    (measurePreserving_add_left volume c).comp U.measurePreserving
  have hinj : Function.Injective (fun x : Space n => c + U x) :=
    fun x y hxy => U.injective (add_left_cancel hxy)
  have hcont : Continuous (fun x : Space n => c + U x) :=
    continuous_const.add U.continuous
  have h := hMP.measure_preimage (s := (fun x : Space n => c + U x) '' K)
    (hK.image hcont).measurableSet.nullMeasurableSet
  simpa only [Set.preimage_image_eq _ hinj] using h.symm

theorem parallelVolume_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (r : ℝ) :
    parallelVolume ((fun x => c + U x) '' K) r = parallelVolume K r := by
  change (volume (parallelBody ((fun x => c + U x) '' K) r)).toReal =
    (volume (parallelBody K r)).toReal
  rw [parallelBody_rigidImage]
  have hcompact : IsCompact (parallelBody K r) := by
    change IsCompact (K + Metric.closedBall 0 r)
    exact hK.add (isCompact_closedBall 0 r)
  exact congrArg ENNReal.toReal (volume_rigidImage c U hcompact)

theorem FullEllipsoid.body_eq_rigidImage {n : ℕ} (E : FullEllipsoid n) :
    E.body = (fun x => E.center + E.frame x) '' axisBody E.semiaxis := by
  simp [FullEllipsoid.body, axisBody, Set.image_image]

theorem isCompact_axisBody {n : ℕ} (a : Fin n → ℝ) : IsCompact (axisBody a) :=
  (isCompact_closedBall (0 : Space n) 1).image (continuous_axisMap a)

theorem FullEllipsoid.steinerInterpolant_eq_axes {n : ℕ} (E : FullEllipsoid n) :
    steinerInterpolant E.body = steinerInterpolant (axisBody E.semiaxis) := by
  apply Lagrange.interpolate_eq_of_values_eq_on
  intro i hi
  rw [E.body_eq_rigidImage,
    parallelVolume_rigidImage E.center E.frame (isCompact_axisBody E.semiaxis)]

theorem FullEllipsoid.volume_eq_axes {n : ℕ} (E : FullEllipsoid n) (k : ℕ) :
    E.volume k = intrinsicVolume (axisBody E.semiaxis) k := by
  simp only [FullEllipsoid.volume, intrinsicVolume, E.steinerInterpolant_eq_axes]

theorem FullEllipsoid.hasSteinerFormula {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n) :
    HasSteinerFormula E.body := by
  intro r hr
  rw [E.body_eq_rigidImage,
    parallelVolume_rigidImage E.center E.frame (isCompact_axisBody E.semiaxis)]
  rw [← E.body_eq_rigidImage, E.steinerInterpolant_eq_axes]
  exact axisBody_hasSteinerFormula hn E.semiaxis_pos r hr

theorem intrinsicVolume_top_of_hasSteinerFormula {n : ℕ} {K : Set (Space n)}
    (hK : HasSteinerFormula K) : intrinsicVolume K n = (volume K).toReal := by
  rw [intrinsicVolume, if_pos le_rfl, Nat.sub_self, unitBallVolume_zero, div_one,
    Polynomial.coeff_zero_eq_eval_zero, ← hK 0 le_rfl]
  simp [parallelVolume, parallelBody]

theorem axisLinear_det {n : ℕ} (a : Fin n → ℝ) : LinearMap.det (axisLinear a) = ∏ i, a i := by
  have hM : axisLinear a = (Matrix.diagonal a).toEuclideanLin := by
    ext x i
    simp [axisLinear, axisMap, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal]
  rw [hM]
  change (Matrix.toLpLin 2 2 (Matrix.diagonal a)).det = ∏ i, a i
  rw [LinearMap.det_toLpLin, Matrix.det_diagonal]

theorem volume_axisBody {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    (volume (axisBody a)).toReal = unitBallVolume n * ∏ i, a i := by
  have h := MeasureTheory.Measure.addHaar_image_linearMap (volume : Measure (Space n))
    (axisLinear a) (Metric.closedBall 0 1)
  change volume (axisBody a) = _ at h
  rw [h, axisLinear_det, abs_of_pos (Finset.prod_pos fun i _ => ha i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (ha i).le)]
  exact mul_comm _ _

theorem FullEllipsoid.volume_top {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n) :
    E.volume n = unitBallVolume n * ∏ i, E.semiaxis i := by
  rw [E.volume_eq_axes, intrinsicVolume_top_of_hasSteinerFormula
    (axisBody_hasSteinerFormula hn E.semiaxis_pos), volume_axisBody E.semiaxis_pos]

end EllipsoidVerification
end
end CanonicalSource18

section CanonicalSource19
/- Source: Ellipsoid/AxisIntegralTransform.lean -/



noncomputable section

open MeasureTheory Set Polynomial Metric
open scoped BigOperators

namespace EllipsoidVerification

def axisHeadMellinIntegrand {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) *
    axisMellinIntegrand a k i t

def axisTailMellinIntegrand {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k) *
    axisMellinIntegrand a ((k : ℝ) + 2) i t

theorem axisHeadMellinIntegrand_eq {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    axisHeadMellinIntegrand a k t =
      t ^ ((k : ℝ) - 1) * axisRational a k (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  rw [axisHeadMellinIntegrand, axisRational, coefficientPolynomial_axisCoefficients,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [axisMellinIntegrand]
  ring

theorem axisTailMellinIntegrand_eq {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    axisTailMellinIntegrand a k t =
      t ^ ((k : ℝ) + 1) * axisRational a (k + 1) (t ^ 2) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
  rw [axisTailMellinIntegrand, axisRational, Nat.add_sub_cancel,
    coefficientPolynomial_axisCoefficients, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [axisMellinIntegrand]
  rw [show (k : ℝ) + 2 - 1 = (k : ℝ) + 1 by ring]
  ring

theorem integrableOn_axisHeadMellinIntegrand {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    IntegrableOn (axisHeadMellinIntegrand a k) (Ioi 0) := by
  exact integrable_finsetSum _ fun i _ => (integrableOn_axisMellinIntegrand ha
    (by exact_mod_cast hk) (by exact_mod_cast (show k < n + 2 by omega)) i).const_mul _

theorem integrableOn_axisTailMellinIntegrand {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    IntegrableOn (axisTailMellinIntegrand a k) (Ioi 0) := by
  exact integrable_finsetSum _ fun i _ => (integrableOn_axisMellinIntegrand ha
    (by positivity) (by exact_mod_cast Nat.add_lt_add_right hkn 2) i).const_mul _

theorem coefficientTransform_eq_axisHeadIntegral {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k ≤ n) :
    coefficientTransform (axisCoefficients a) k = ∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t := by
  unfold coefficientTransform
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [axisHeadMellinIntegrand_eq]
  exact coefficientTransform_integrand_axis ha hk hkn ht

theorem mellinBoundary_axis_rational {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ (k : ℝ) *
      coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)))
      (t ^ ((k : ℝ) - 1) * ((k : ℝ) - t ^ 2 * axisRational a 1 (t ^ 2)) *
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ))) t := by
  have hq := coefficientPolynomial_pos (axisCoefficients_admissible a ha) t
  have hD : coefficientDerivative (axisCoefficients a) t =
      2 * t * (coefficientPolynomial (axisCoefficients a) t * axisRational a 1 (t ^ 2)) := by
    rw [coefficientDerivative_axisCoefficients,
      axisCoefficientPolynomial_derivative_eval a (sq_nonneg t)]
    congr 2
    simp only [axisCoefficientPolynomial, coefficientPolynomial_axisCoefficients,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hd := (Real.hasDerivAt_rpow_const (p := (k : ℝ)) (Or.inl ht.ne')).mul
    ((hasDerivAt_coefficientPolynomial (axisCoefficients a) t).rpow_const
      (p := -(1 / 2 : ℝ)) (Or.inl hq.ne'))
  convert hd using 1
  symm
  rw [hD]
  have htP : t ^ (k : ℝ) = t ^ ((k : ℝ) - 1) * t := by
    calc
      _ = t ^ ((k : ℝ) - 1) * t ^ (1 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  have hqP : coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
      coefficientPolynomial (axisCoefficients a) t =
        coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
          coefficientPolynomial (axisCoefficients a) t ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hq]
        congr 1
        ring
  rw [htP]
  calc
    _ = (k : ℝ) * t ^ ((k : ℝ) - 1) * coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ)) -
      t ^ ((k : ℝ) - 1) * t ^ 2 * axisRational a 1 (t ^ 2) *
        (coefficientPolynomial (axisCoefficients a) t ^ (-(1 / 2 : ℝ) - 1) *
          coefficientPolynomial (axisCoefficients a) t) := by ring
    _ = _ := by rw [hqP]; ring

theorem axisHeadTail_integral_eq {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t) =
      ∫ t in Ioi (0 : ℝ), axisTailMellinIntegrand a k t := by
  let e := axisCoefficients a
  have he := axisCoefficients_admissible a ha
  have hi (j : Fin (n + 1)) : IntegrableOn (fun t : ℝ =>
      t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
    apply integrable_mellinMoment he
    · positivity
    · have hj : (j.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      have hkr : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
  have hsum : (∫ t in Ioi (0 : ℝ), ∑ j : Fin (n + 1), ((k : ℝ) - j.val) * e j *
      (t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))) = 0 := by
    rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
    simp only [integral_const_mul]
    have hrec := coefficientMellinPower_recurrence he
      (s := (1 / 2 : ℝ)) (r := (k : ℝ)) (by exact_mod_cast hk)
      (by
        have hkr : (k : ℝ) < n := by exact_mod_cast hkn
        push_cast
        nlinarith)
    norm_num [coefficientMellinPower] at hrec
    exact hrec
  have hpoint (t : ℝ) (ht : 0 < t) :
      axisHeadMellinIntegrand a k t - axisTailMellinIntegrand a k t =
      (axisCoefficientPolynomial a).coeff k *
        ∑ j : Fin (n + 1), ((k : ℝ) - j.val) * e j *
          (t ^ ((k : ℝ) + 2 * j.val - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) := by
    have hd := (mellinBoundary_axis_rational (k := k) ha ht).unique
      (mellinBoundary_derivative he (1 / 2) k ht)
    norm_num only [one_mul] at hd
    rw [axisHeadMellinIntegrand_eq, axisTailMellinIntegrand_eq, ← hd]
    have hpow : t ^ ((k : ℝ) + 1) = t ^ ((k : ℝ) - 1) * t ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add ht]
      congr 1
      ring
    rw [hpow]
    have hr := axisRational_recurrence a hk (sq_nonneg t)
    linear_combination -(t ^ ((k : ℝ) - 1) * coefficientPolynomial e t ^ (-(1 / 2 : ℝ))) * hr
  apply sub_eq_zero.mp
  rw [← integral_sub (integrableOn_axisHeadMellinIntegrand ha hk hkn)
    (integrableOn_axisTailMellinIntegrand ha hk hkn)]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul, hsum, mul_zero]

def angularMellinConstant (n : ℕ) (β : ℝ) : ℝ :=
  2 * (Real.sqrt Real.pi) ^ n /
    (Real.Gamma (β / 2) * Real.Gamma (((n : ℝ) + 2 - β) / 2))

theorem sphere_axisA_eq_headMellin {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ u : sphere (0 : Space n) 1, axisA a k u / axisSupport a u ^ k ∂volume.toSphere) =
      angularMellinConstant n k * ∫ t in Ioi (0 : ℝ), axisHeadMellinIntegrand a k t := by
  have hs (i : Fin n) := integrable_sphere_of_continuousOn_compl_zero
    (continuousOn_axisAngularFunction ha (k : ℝ) i)
  have hi (i : Fin n) := integrableOn_axisMellinIntegrand (β := (k : ℝ)) ha (by exact_mod_cast hk)
    (by exact_mod_cast (show k < n + 2 by omega)) i
  have hp (u : sphere (0 : Space n) 1) :
      axisA a k u / axisSupport a u ^ k =
        ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) (k - 1)) *
          axisAngularFunction a k i u := by
    have hu : 0 ≤ axisSupport a u := norm_nonneg _
    simp only [axisA, Finset.sum_div, axisAngularFunction, Real.rpow_neg hu,
      Real.rpow_natCast, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => (hs i).const_mul _)]
  simp only [integral_const_mul]
  simp_rw [sphere_axisAngularFunction_eq_mellin (β := (k : ℝ)) ha (by exact_mod_cast hk)
    (by exact_mod_cast (show k < n + 2 by omega))]
  simp only [axisHeadMellinIntegrand]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, angularMellinConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem sphere_axisC_eq_tailMellin {n k : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hk : 0 < k) (hkn : k < n) :
    (∫ u : sphere (0 : Space n) 1, axisC a k u / axisSupport a u ^ (k + 2) ∂volume.toSphere) =
      angularMellinConstant n ((k : ℝ) + 2) * ∫ t in Ioi (0 : ℝ), axisTailMellinIntegrand a k t := by
  have hs (i : Fin n) := integrable_sphere_of_continuousOn_compl_zero
    (continuousOn_axisAngularFunction ha ((k : ℝ) + 2) i)
  have hi (i : Fin n) := integrableOn_axisMellinIntegrand (β := (k : ℝ) + 2) ha (by positivity)
    (by exact_mod_cast Nat.add_lt_add_right hkn 2) i
  have hp (u : sphere (0 : Space n) 1) :
      axisC a k u / axisSupport a u ^ (k + 2) =
        ∑ i, (a i ^ 2 * elementaryOn (Finset.univ.erase i) (fun j => a j ^ 2) k) *
          axisAngularFunction a ((k : ℝ) + 2) i u := by
    have hu : 0 ≤ axisSupport a u := norm_nonneg _
    have hpow : axisSupport a u ^ ((k : ℝ) + 2) = axisSupport a u ^ (k + 2) := by
      rw [show (k : ℝ) + 2 = ((k + 2 : ℕ) : ℝ) by simp only [Nat.cast_add, Nat.cast_ofNat],
        Real.rpow_natCast]
    simp only [axisC, Finset.sum_div, axisAngularFunction, Real.rpow_neg hu,
      hpow, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => (hs i).const_mul _)]
  simp only [integral_const_mul]
  simp_rw [sphere_axisAngularFunction_eq_mellin (β := (k : ℝ) + 2) ha (by positivity)
    (by exact_mod_cast Nat.add_lt_add_right hkn 2)]
  simp only [axisTailMellinIntegrand]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, angularMellinConstant, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end EllipsoidVerification
end
end CanonicalSource19
