module

public import Projection.Rigidity.WulffVariation
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Localized first variation of an actual convex body

Polar integration converts a volume integral with a continuous spatial test
function into a one-dimensional primitive along each ray. Differentiating the
radial endpoint gives the localized form of the Wulff variation formula. The
body may be nonsmooth and the added body may have any affine dimension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

/-- The actual radial endpoint of the body in a unit direction. -/
def bodyRadius {n : ℕ} (K : Set (Space n)) (u : Sphere n) : ℝ :=
  (gauge K (u : Space n))⁻¹

/-- A weighted radial primitive; the polar Jacobian is included. -/
def radialPrimitive {n : ℕ} (ψ : Space n → ℝ) (u : Sphere n) (r : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..r, a ^ (n - 1) * ψ (a • (u : Space n))

theorem continuous_radialPrimitive {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) : Continuous (fun p : Sphere n × ℝ => radialPrimitive ψ p.1 p.2) := by
  have hc : Continuous (fun p : (Sphere n × ℝ) × ℝ =>
      (p.1.2 * p.2) ^ (n - 1) * ψ ((p.1.2 * p.2) • (p.1.1 : Space n))) := by
    fun_prop
  have hi := continuous_parametric_integral_of_continuous
    (X := Sphere n × ℝ) (Y := ℝ) (E := ℝ) (μ := volume)
    (f := fun (p : Sphere n × ℝ) (a : ℝ) =>
      (p.2 * a) ^ (n - 1) * ψ ((p.2 * a) • (p.1 : Space n))) hc
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have he (p : Sphere n × ℝ) : radialPrimitive ψ p.1 p.2 =
      p.2 * ∫ a in Icc (0 : ℝ) 1,
        (p.2 * a) ^ (n - 1) * ψ ((p.2 * a) • (p.1 : Space n)) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    simpa only [smul_eq_mul, mul_zero, mul_one, radialPrimitive] using
      (intervalIntegral.smul_integral_comp_mul_left
        (fun a : ℝ => a ^ (n - 1) * ψ (a • (p.1 : Space n)))
        (a := 0) (b := 1) p.2).symm
  simp_rw [he]
  exact continuous_snd.mul hi

theorem radialPrimitive_hasDerivAt {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) (u : Sphere n) (r : ℝ) :
    HasDerivAt (radialPrimitive ψ u)
      (r ^ (n - 1) * ψ (r • (u : Space n))) r := by
  exact (show Continuous (fun a : ℝ =>
    a ^ (n - 1) * ψ (a • (u : Space n))) by fun_prop).integral_hasStrictDerivAt 0 r
    |>.hasDerivAt

theorem radialPrimitive_lipschitz {n : ℕ} {ψ : Space n → ℝ}
    (hψ : Continuous ψ) {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hb : ∀ x ∈ closedBall (0 : Space n) R, ‖ψ x‖ ≤ B) (u : Sphere n) :
    LipschitzOnWith (NNReal.mk (R ^ (n - 1) * B) (by positivity))
      (radialPrimitive ψ u) (Icc 0 R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  have hc : Continuous (fun a : ℝ => a ^ (n - 1) * ψ (a • (u : Space n))) := by
    fun_prop
  rw [Real.dist_eq, Real.dist_eq, ← Real.norm_eq_abs]
  change ‖(∫ a in (0 : ℝ)..r, a ^ (n - 1) * ψ (a • (u : Space n))) -
      ∫ a in (0 : ℝ)..s, a ^ (n - 1) * ψ (a • (u : Space n))‖ ≤ _
  rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := r) (C := R ^ (n - 1) * B) (f := fun a : ℝ =>
      a ^ (n - 1) * ψ (a • (u : Space n))) (fun a ha => by
        have ha0 : 0 ≤ a := (le_min hs.1 hr.1).trans ha.1.le
        have haR : a ≤ R := ha.2.trans (max_le hs.2 hr.2)
        have hx : a • (u : Space n) ∈ closedBall (0 : Space n) R := by
          simpa only [mem_closedBall, dist_zero_right, norm_smul, norm_coe,
            mul_one, Real.norm_of_nonneg ha0] using haR
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha0 _)]
        exact mul_le_mul (pow_le_pow_left₀ ha0 haR _) (hb _ hx)
          (norm_nonneg _) (pow_nonneg hR _))
  simpa only [NNReal.coe_mk, Real.norm_eq_abs, abs_sub_comm s r] using h

theorem surface_integral_eq_mul_mean {n : ℕ} [NeZero n] (f : Sphere n → ℝ) :
    (∫ u, f u ∂surface n) = (n : ℝ) * kappa n * mean f := by
  rw [mean, sigma, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul]
  change _ = (n : ℝ) * kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ, ← mul_assoc]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [mul_inv_cancel₀ (mul_ne_zero hn (kappa_pos n).ne'), one_mul]

/-- Polar integration with an arbitrary continuous spatial test. -/
theorem integral_body_eq_radialPrimitive {n : ℕ} [NeZero n]
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) {ψ : Space n → ℝ} (hψ : Continuous ψ) :
    (∫ x in K, ψ x) = (n : ℝ) * kappa n *
      mean (fun u : Sphere n => radialPrimitive ψ u (bodyRadius K u)) := by
  have hp (u : Sphere n) : 0 < gauge K (u : Space n) := by
    apply (gauge_pos (absorbent_nhds_zero h0)
      ((NormedSpace.isVonNBounded_iff ℝ).2 hK.isBounded)).2
    intro hu
    simpa [hu] using norm_coe u
  have hi : Integrable (K.indicator ψ) volume :=
    (hψ.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rw [← integral_indicator hK.measurableSet,
    TauCeti.integral_eq_integral_toSphere_integral_Ioi _ hi]
  have hinner (u : Sphere n) :
      (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        K.indicator ψ (r • (u : Space n))) = radialPrimitive ψ u (bodyRadius K u) := by
    have hmem (r : ℝ) (hr : 0 < r) :
        r • (u : Space n) ∈ K ↔ r ≤ bodyRadius K u := by
      have hmem' : r • (u : Space n) ∈ K ↔
          gauge K (r • (u : Space n)) ≤ 1 := by
        simpa only [hK.isClosed.closure_eq] using
          (gauge_le_one_iff_mem_closure (x := r • (u : Space n)) hc h0).symm
      rw [hmem', gauge_smul_of_nonneg (α := ℝ) hr.le, smul_eq_mul]
      change r * gauge K (u : Space n) ≤ 1 ↔ r ≤ (gauge K (u : Space n))⁻¹
      rw [inv_eq_one_div, le_div_iff₀ (hp u)]
    have he : (fun r : ℝ => r ^ (Module.finrank ℝ (Space n) - 1) •
        K.indicator ψ (r • (u : Space n))) =ᶠ[ae (volume.restrict (Ioi 0))]
        (Iic (bodyRadius K u)).indicator
          (fun r : ℝ => r ^ (n - 1) * ψ (r • (u : Space n))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      by_cases hm : r ≤ bodyRadius K u
      · simp only [indicator_of_mem ((hmem r hr).mpr hm),
          indicator_of_mem (show r ∈ Iic (bodyRadius K u) from hm), finrank_euclideanSpace_fin, smul_eq_mul]
      · simp only [indicator_of_notMem (fun hk => hm ((hmem r hr).mp hk)),
          indicator_of_notMem (show r ∉ Iic (bodyRadius K u) from hm), smul_zero]
    rw [integral_congr_ae he, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
    exact (intervalIntegral.integral_of_le (inv_nonneg.mpr (hp u).le)).symm
  simp_rw [hinner]
  exact surface_integral_eq_mul_mean _

theorem wulff_radius_param_bounds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      (∀ t ∈ T, ∀ u : Sphere n, 0 ≤ bodyRadius (wulff ⇑(s + t • φ)) u ∧
        bodyRadius (wulff ⇑(s + t • φ)) u ≤ R) ∧
      ∀ u : Sphere n, LipschitzOnWith C
        (fun t : ℝ => bodyRadius (wulff ⇑(s + t • φ)) u) T := by
  obtain ⟨m, M, hm, hM, he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s + t • φ) u ∧ (s + t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact (contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').contDiffWithinAt
  obtain ⟨D, hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := NNReal.mk (‖φ‖ / m ^ 2) (by positivity)
  refine ⟨T, hT, M, hM, D * C, ?_, ?_⟩
  · intro t ht u
    have hq := wulff_sphere_gauge_bounds (s + t • φ) hm ht u
    have hqp : 0 < gauge (wulff ⇑(s + t • φ)) (u : Space n) :=
      (inv_pos.mpr hM).trans_le hq.1
    refine ⟨inv_nonneg.mpr hqp.le, ?_⟩
    simpa only [inv_inv, bodyRadius] using inv_anti₀ (inv_pos.mpr hM) hq.1
  · intro u
    apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
    intro t ht
    exact wulff_sphere_gauge_bounds (s + t • φ) hm ht u

theorem wulff_radius_derivative {n : ℕ} [NeZero n]
    (s : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u)
    (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ, 0 < a → ∀ x, φ (a • x) = a * φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => bodyRadius
      (wulff ⇑(s + t • (⟨fun v : Sphere n => φ v,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n, ℝ)))) u)
      (bodyRadius (wulff s) u * φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := (wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul, add_zero] using hp.ne')
  apply h.congr_deriv
  simp only [bodyRadius, zero_smul, add_zero]
  field_simp [hp.ne']

/-- Localized two-sided Wulff first variation. The test `ψ` is a genuine
continuous function on the ambient space and is evaluated at boundary points. -/
theorem wulff_integral_derivative {n : ℕ} [NeZero n]
    (s : C(Sphere n, ℝ)) (hs : ∀ u, 0 < s u)
    (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ a : ℝ, 0 < a → ∀ x, φ (a • x) = a * φ x)
    (ψ : Space n → ℝ) (hψ : Continuous ψ) :
    HasDerivAt (fun t : ℝ => ∫ x in
      wulff ⇑(s + t • (⟨fun u : Sphere n => φ u,
        hφ.comp continuous_subtype_val⟩ : C(Sphere n, ℝ))), ψ x)
      ((n : ℝ) * kappa n * mean (fun u : Sphere n =>
        bodyRadius (wulff s) u ^ n *
          ψ (bodyRadius (wulff s) u • (u : Space n)) *
          φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n, ℝ) := ⟨fun u => φ u, hφ.comp continuous_subtype_val⟩
  let ρ : ℝ → Sphere n → ℝ := fun t u => bodyRadius (wulff ⇑(s + t • φs)) u
  let F : ℝ → Sphere n → ℝ := fun t u => radialPrimitive ψ u (ρ t u)
  let F' : Sphere n → ℝ := fun u => bodyRadius (wulff s) u ^ n *
    ψ (bodyRadius (wulff s) u • (u : Space n)) *
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hρc (t : ℝ) (ht : ∀ u, 0 < (s + t • φs) u) : Continuous (ρ t) := by
    apply ((continuous_gauge (wulff_convex _) (wulff_nhds (s + t • φs) ht)).comp
      continuous_subtype_val).inv₀
    intro u
    change gauge (wulff ⇑(s + t • φs)) (u : Space n) ≠ 0
    rw [gauge_wulff_eq_max (s + t • φs) ht]
    exact (wulffMax_pos (s + t • φs) ht (by intro h; simpa [h] using norm_coe u)).ne'
  have hFc (t : ℝ) (ht : ∀ u, 0 < (s + t • φs) u) : Continuous (F t) :=
    (continuous_radialPrimitive hψ).comp (continuous_id.prodMk (hρc t ht))
  have hF0 : Continuous (F 0) := hFc 0 (by simpa using hs)
  obtain ⟨T, hT, R, hR, C, hρbound, hρlip⟩ := wulff_radius_param_bounds s φs hs
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space n) R).exists_bound_of_continuousOn
    hψ.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0 (by simp [hR.le]))
  let L : ℝ≥0 := NNReal.mk (R ^ (n - 1) * B) (by positivity)
  have hFl (u : Sphere n) : LipschitzOnWith (L * C) (fun t => F t u) T :=
    (radialPrimitive_lipschitz hψ hR.le hB0 hB u).comp (hρlip u)
      (fun t ht => hρbound t ht u)
  have hFm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (sigma n) :=
    (positive_constraints_nhds s φs hs).mono (fun t ht => (hFc t ht).aestronglyMeasurable)
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    have hrad : Continuous (bodyRadius (wulff s)) := by simpa only [ρ, zero_smul, add_zero] using hρc 0 (by simpa using hs)
    apply Measurable.aestronglyMeasurable
    exact ((hrad.measurable.pow_const n).mul
      (hψ.measurable.comp (hrad.measurable.smul measurable_subtype_coe))).mul
        (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hd : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    have h := (radialPrimitive_hasDerivAt hψ u (ρ 0 u)).comp 0
      (wulff_radius_derivative s hs φ hφ hh hu)
    simp only [ρ, zero_smul, add_zero] at h
    apply h.congr_deriv
    have hn : n - 1 + 1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
    have hp : bodyRadius (wulff s) u ^ (n - 1) * bodyRadius (wulff s) u =
        bodyRadius (wulff s) u ^ n := by rw [← pow_succ, hn]
    dsimp only [F']
    calc
      _ = (bodyRadius (wulff s) u ^ (n - 1) * bodyRadius (wulff s) u) *
          ψ (bodyRadius (wulff s) u • (u : Space n)) *
          φ (∇ (gauge (wulff s)) (u : Space n)) := by ring
      _ = _ := by rw [hp]
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hF0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hFl u))
    (integrable_const ((L * C : ℝ≥0) : ℝ)) hd).2
  have he : (fun t : ℝ => ∫ x in wulff ⇑(s + t • φs), ψ x) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (n : ℝ) * kappa n * ∫ u, F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact integral_body_eq_radialPrimitive (wulff_compact _ ht) (wulff_convex _)
      (wulff_nhds _ ht) hψ
  exact (hI.const_mul ((n : ℝ) * kappa n)).congr_of_eventuallyEq he

/-- The localized first variation under actual Minkowski addition. -/
theorem minkowski_integral_derivative {n : ℕ} [NeZero n]
    {K A : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (hA : IsCompact A) (hcA : Convex ℝ A)
    (hAn : A.Nonempty) (ψ : Space n → ℝ) (hψ : Continuous ψ) :
    HasDerivWithinAt (fun t : ℝ => ∫ x in K + t • A, ψ x)
      ((n : ℝ) * kappa n * mean (fun u : Sphere n => bodyRadius K u ^ n *
        ψ (bodyRadius K u • (u : Space n)) *
        support A (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0, mem_of_mem_nhds h0⟩
  let s : C(Sphere n, ℝ) := ⟨fun u => support K u,
    (support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u, 0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n, ℝ) := ⟨fun u => support A u,
    (support_continuous hA).comp continuous_subtype_val⟩
  have he (t : ℝ) (ht : 0 ≤ t) : wulff ⇑(s + t • φ) = K + t • A := by
    have hf : ⇑(s + t • φ) = fun u : Sphere n => support (K + t • A) u := by
      funext u
      change support K u + t * support A u = support (K + t • A) u
      rw [support_minkowski hK hKn (hA.smul t) (hAn.smul_set (a := t)),
        support_smul_set hA hAn ht]
    rw [hf]
    exact wulff_support (hK.add (hA.smul t)) (hcK.add (hcA.smul t))
      (hKn.add (hAn.smul_set (a := t)))
  have h := (wulff_integral_derivative s hs (support A) (support_continuous hA)
    (fun a ha x => support_smul hA hAn ha.le x) ψ hψ).hasDerivWithinAt (s := Ici (0 : ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg (fun B => ∫ x in B, ψ x) (he t ht).symm)
    (congrArg (fun B => ∫ x in B, ψ x) (he 0 le_rfl).symm)

end OAI.PettyProjection
