module

public import wishart.verified.core05

/- Generated ordinary proof stage. See audit/staged_compact_proportionateshifts/ProportionateShifts01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/MonotoneTilts.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Probability tilts and increasing expectations

The normalizer is the actual integral of the tilt. The signed bounded-test
form below records stochastic domination, while the integrable nonnegative
form also permits the unbounded determinant powers in exponent comparisons.
-/

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω]

theorem normalizedWeight_probability_of_integrable_pos_ae
    (μ : Measure Ω) (w : Ω → ℝ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hwi : Integrable w μ) (hpos : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (normalizedWeight μ w) := by
  have hZ : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) = ENNReal.ofReal (∫ x, w x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hwi hw0).symm
  apply normalizedWeight_probability
  · rw [hZ]
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · rw [hZ]
    exact ENNReal.ofReal_ne_top

theorem normalizedWeight_integral_ae (μ : Measure Ω) (w f : Ω → ℝ)
    (hwm : Measurable w) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) (hwi : Integrable w μ) :
    (∫ x, f x ∂normalizedWeight μ w) =
      (∫ x, w x * f x ∂μ) / (∫ x, w x ∂μ) := by
  rw [normalizedWeight, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f,
    ENNReal.toReal_inv, ← ofReal_integral_eq_lintegral_ofReal hwi hw0,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hw0)]
  have heq : (fun x ↦ (ENNReal.ofReal (w x)).toReal • f x) =ᵐ[μ]
      (fun x ↦ w x * f x) := hw0.mono fun x hx ↦ by
    change (ENNReal.ofReal (w x)).toReal • f x = w x * f x
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
  rw [integral_congr_ae heq]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem normalizedWeight_probability_of_integrable_pos
    (μ : Measure Ω) (w : Ω → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hwi : Integrable w μ) (hpos : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (normalizedWeight μ w) := by
  have hZ : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) = ENNReal.ofReal (∫ x, w x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hw0)).symm
  apply normalizedWeight_probability
  · rw [hZ]
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · rw [hZ]
    exact ENNReal.ofReal_ne_top

theorem normalizedWeight_congr_ae (μ : Measure Ω) (u v : Ω → ℝ)
    (h : u =ᵐ[μ] v) : normalizedWeight μ u = normalizedWeight μ v := by
  have he : (fun x ↦ ENNReal.ofReal (u x)) =ᵐ[μ] (fun x ↦ ENNReal.ofReal (v x)) :=
    h.fun_comp ENNReal.ofReal
  unfold normalizedWeight
  rw [lintegral_congr_ae he, withDensity_congr_ae he]

theorem normalizedWeight_const_mul (μ : Measure Ω) (w : Ω → ℝ)
    (hwm : Measurable w) {c : ℝ} (hc : 0 < c) :
    normalizedWeight μ (fun x ↦ c * w x) = normalizedWeight μ w := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hwd : μ.withDensity (fun x => ENNReal.ofReal c * ENNReal.ofReal (w x)) =
      ENNReal.ofReal c • μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
    have h := withDensity_smul (μ := μ) (ENNReal.ofReal c) hwm.ennreal_ofReal
    have heq : (ENNReal.ofReal c • fun x => ENNReal.ofReal (w x)) =
        (fun x => ENNReal.ofReal c * ENNReal.ofReal (w x)) := by
      funext x
      rfl
    rw [heq] at h
    exact h
  unfold normalizedWeight
  simp_rw [ENNReal.ofReal_mul hc.le]
  rw [lintegral_const_mul _ hwm.ennreal_ofReal,
    hwd,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), smul_smul]
  congr 1
  calc
    (ENNReal.ofReal c)⁻¹ * (∫⁻ x, ENNReal.ofReal (w x) ∂μ)⁻¹ * ENNReal.ofReal c =
        (∫⁻ x, ENNReal.ofReal (w x) ∂μ)⁻¹ * ((ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, mul_one]

/-- Successive probability tilts multiply their actual densities. This is an
equality of measures, not merely equality on a chosen family of moments. -/
theorem normalizedWeight_iterate (μ : Measure Ω) (u v : Ω → ℝ)
    (hum : Measurable u) (hvm : Measurable v) (hu0 : ∀ x, 0 ≤ u x)
    [IsProbabilityMeasure (normalizedWeight (normalizedWeight μ u) v)] :
    normalizedWeight (normalizedWeight μ u) v =
      normalizedWeight μ (fun x ↦ u x * v x) := by
  let c := (∫⁻ x, ENNReal.ofReal (v x) ∂normalizedWeight μ u)⁻¹ *
    (∫⁻ x, ENNReal.ofReal (u x) ∂μ)⁻¹
  have hlaw : normalizedWeight (normalizedWeight μ u) v =
      c • μ.withDensity (fun x ↦ ENNReal.ofReal (u x * v x)) := by
    change (∫⁻ x, ENNReal.ofReal (v x) ∂normalizedWeight μ u)⁻¹ •
      (((∫⁻ x, ENNReal.ofReal (u x) ∂μ)⁻¹ •
        μ.withDensity (fun x ↦ ENNReal.ofReal (u x))).withDensity
          (fun x ↦ ENNReal.ofReal (v x))) = _
    rw [withDensity_smul_measure, ← withDensity_mul μ hum.ennreal_ofReal hvm.ennreal_ofReal,
      smul_smul]
    congr 2
    funext x
    exact (ENNReal.ofReal_mul (hu0 x)).symm
  exact (normalizedWeight_eq_of_probability_density _ μ _ c hlaw).2.2

theorem integrable_bounded_test (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hfm : Measurable f) (M : ℝ) (hbound : ∀ x, |f x| ≤ M) :
    Integrable f μ := by
  apply (integrable_const M).mono' hfm.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hbound x

theorem measure_eq_of_bounded_measurable_integrals
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : Ω → ℝ, Measurable f → (∃ M : ℝ, ∀ x, |f x| ≤ M) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext
  intro s hs
  have hi := h (s.indicator (fun _ ↦ (1 : ℝ))) (measurable_const.indicator hs)
    ⟨1, fun x ↦ by by_cases hx : x ∈ s <;> simp [hx]⟩
  have hreal : (μ s).toReal = (ν s).toReal := by
    simpa only [integral_indicator_const _ hs, smul_eq_mul, mul_one, measureReal_def] using hi
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp hreal

/-- Comparison against every bounded Borel increasing real-valued test. The
order restriction is only on the common support set. -/
def IncreasingExpectationLE [Preorder Ω] (s : Set Ω) (μ ν : Measure Ω) : Prop :=
  ∀ f : Ω → ℝ, Measurable f → MonotoneOn f s →
    (∃ M : ℝ, ∀ x, |f x| ≤ M) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν

section Association

variable [Preorder Ω]

/-- The nonnegative integrable version of stochastic domination by an
increasing probability tilt. The association input will be supplied by the
actual separately tilted Vandermonde density in Proposition 4.1. -/
theorem integral_le_normalizedWeight_of_association
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hassoc : ∀ f g : Ω → ℝ, Measurable f → Measurable g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → MonotoneOn f s → MonotoneOn g s →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ)
    (w f : Ω → ℝ) (hwm : Measurable w) (hfm : Measurable f)
    (hw0 : ∀ x, 0 ≤ w x) (hf0 : ∀ x, 0 ≤ f x)
    (hwmn : MonotoneOn w s) (hfmono : MonotoneOn f s)
    (hwi : Integrable w μ) (hfi : Integrable f μ)
    (hwfi : Integrable (fun x ↦ w x * f x) μ)
    (hwpos : 0 < ∫ x, w x ∂μ) :
    (∫ x, f x ∂μ) ≤ ∫ x, f x ∂normalizedWeight μ w := by
  have h := integral_mul_le_of_lintegral_mul_le μ w f hw0 hf0 hwi hfi hwfi
    (hassoc w f hwm hfm hw0 hf0 hwmn hfmono)
  rw [normalizedWeight_integral μ w f hwm hw0 hwi]
  exact (le_div_iff₀ hwpos).mpr (by simpa only [mul_comm] using h)

/-- Increasing tilts raise every bounded increasing real expectation, including
signed tests. Positivity and finiteness of the actual normalizer are explicit. -/
theorem increasingExpectationLE_normalizedWeight_of_association
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω)
    (hassoc : ∀ f g : Ω → ℝ, Measurable f → Measurable g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → MonotoneOn f s → MonotoneOn g s →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ)
    (w : Ω → ℝ) (hwm : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwmn : MonotoneOn w s) (hwi : Integrable w μ)
    (hwpos : 0 < ∫ x, w x ∂μ) :
    IncreasingExpectationLE s μ (normalizedWeight μ w) := by
  intro f hfm hmono hbounded
  obtain ⟨M, hbound⟩ := hbounded
  let A := max M 0
  have hA : 0 ≤ A := le_max_right _ _
  have hboundA (x) : |f x| ≤ A := (hbound x).trans (le_max_left _ _)
  let F : Ω → ℝ := fun x ↦ f x + A
  have hFm : Measurable F := hfm.add_const A
  have hF0 (x) : 0 ≤ F x := by
    have h := (abs_le.mp (hboundA x)).1
    dsimp [F]
    linarith
  have hFb (x) : |F x| ≤ 2 * A := by
    rw [abs_of_nonneg (hF0 x)]
    have h := (abs_le.mp (hboundA x)).2
    dsimp [F]
    linarith
  have hFi := integrable_bounded_test μ F hFm (2 * A) hFb
  have hwFi : Integrable (fun x ↦ w x * F x) μ :=
    hwi.mul_bdd hFm.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hFb x)
  have h := integral_le_normalizedWeight_of_association μ s hassoc w F hwm hFm hw0 hF0
    hwmn (fun x hx y hy hxy ↦ by
      simpa only [F, add_comm] using add_le_add_right (hmono hx hy hxy) A)
    hwi hFi hwFi hwpos
  letI := normalizedWeight_probability_of_integrable_pos μ w hw0 hwi hwpos
  have hfi := integrable_bounded_test μ f hfm A hboundA
  have hfilt := integrable_bounded_test (normalizedWeight μ w) f hfm A hboundA
  simpa only [F, integral_add hfi (integrable_const A),
    integral_add hfilt (integrable_const A), integral_const,
    probReal_univ, one_smul, add_le_add_iff_right] using h

/-- Clearing a positive finite tilt normalizer in an association inequality.
All weighted integrability conditions are verified before real arithmetic is
used; no convention for divergent Bochner integrals can affect the result. -/
theorem weighted_integral_association
    (μ : Measure Ω) (h f g : Ω → ℝ)
    (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hhi : Integrable h μ) (hhpos : 0 < ∫ x, h x ∂μ)
    (hhfi : Integrable (fun x ↦ h x * f x) μ)
    (hhgi : Integrable (fun x ↦ h x * g x) μ)
    (hhfgi : Integrable (fun x ↦ h x * (f x * g x)) μ)
    (hassoc : (∫⁻ x, ENNReal.ofReal (f x) ∂normalizedWeight μ h) *
      (∫⁻ x, ENNReal.ofReal (g x) ∂normalizedWeight μ h) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂normalizedWeight μ h) :
    (∫ x, h x * f x ∂μ) * (∫ x, h x * g x ∂μ) ≤
      (∫ x, h x ∂μ) * ∫ x, h x * (f x * g x) ∂μ := by
  have hZ0 : (∫⁻ x, ENNReal.ofReal (h x) ∂μ) ≠ 0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)]
    exact (ENNReal.ofReal_pos.mpr hhpos).ne'
  have hfi := integrable_normalizedWeight μ h f hhm hh0 hZ0 hhfi
  have hgi := integrable_normalizedWeight μ h g hhm hh0 hZ0 hhgi
  have hfgi := integrable_normalizedWeight μ h (fun x ↦ f x * g x) hhm hh0 hZ0 hhfgi
  have hcov := integral_mul_le_of_lintegral_mul_le (normalizedWeight μ h) f g hf0 hg0
    hfi hgi hfgi hassoc
  rw [normalizedWeight_integral μ h f hhm hh0 hhi,
    normalizedWeight_integral μ h g hhm hh0 hhi,
    normalizedWeight_integral μ h (fun x ↦ f x * g x) hhm hh0 hhi,
    div_mul_div_comm] at hcov
  have hcross := (div_le_div_iff₀ (mul_pos hhpos hhpos) hhpos).mp hcov
  have hcross' :
      ((∫ x, h x * f x ∂μ) * (∫ x, h x * g x ∂μ)) * (∫ x, h x ∂μ) ≤
        ((∫ x, h x ∂μ) * (∫ x, h x * (f x * g x) ∂μ)) * (∫ x, h x ∂μ) := by
    convert hcross using 1 <;> ring
  exact le_of_mul_le_mul_right hcross' hhpos

end Association

end WishartVerification
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/ShiftedPrincipalDefinitions.lean -/



open scoped Classical
open MeasureTheory

/-!
# Proportional shifts and their genuine Wishart probability tilts

The shifted determinants are exactly `det (X_II + c_i Σ_II)`. The definitions
keep their ordinary real powers, with all identities proved on the actual
positive-definite support. No artificial positivity convention changes the
observables whose expectations appear in Section 4.1.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

def shiftedPrincipalMinor (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (I : Finset (Fin p)) (c : ℝ) (X : SymmetricMatrix p) : ℝ :=
  (((X : Matrix (Fin p) (Fin p) ℝ).submatrix (fun i : I ↦ (i : Fin p))
      (fun i : I ↦ (i : Fin p))) +
    c • Sigma.submatrix (fun i : I ↦ (i : Fin p)) (fun i : I ↦ (i : Fin p))).det

def shiftedMomentIntegrand (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (X : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i

def shiftedMoment (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) : ℝ :=
  ∫ X, shiftedMomentIntegrand Sigma P c ν J X
    ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma

def shiftedMomentRatio (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) : ℝ :=
  shiftedMoment α Sigma P c ν Finset.univ /
    ∏ i : Fin d, shiftedMoment α Sigma P c ν {i}

def shiftedTiltLaw (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) :
    Measure (SymmetricMatrix p) :=
  normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α Sigma)
    (shiftedMomentIntegrand Sigma P c ν J)

theorem shiftedPrincipalMinor_measurable
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p)) (c : ℝ) :
    Measurable (shiftedPrincipalMinor Sigma I c) := by
  apply Continuous.measurable
  unfold shiftedPrincipalMinor
  apply Continuous.matrix_det
  apply Continuous.add _ continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (j : Fin p)).comp
    ((continuous_apply (i : Fin p)).comp continuous_subtype_val)

theorem shiftedMomentIntegrand_measurable
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) :
    Measurable (shiftedMomentIntegrand Sigma P c ν J) :=
  Finset.measurable_prod _ fun i _ ↦
    (shiftedPrincipalMinor_measurable Sigma (P.block i) (c i)).pow_const (ν i)

theorem shiftedPrincipalMinor_pos
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (I : Finset (Fin p)) {c : ℝ} (hc : 0 ≤ c) (X : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < shiftedPrincipalMinor Sigma I c X :=
  ((hX.submatrix Subtype.coe_injective).add_posSemidef
    ((hSigma.submatrix Subtype.coe_injective).posSemidef.smul hc)).det_pos

theorem shiftedPrincipalMinor_eq_det_enumeration
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (I : Finset (Fin p))
    (c : ℝ) (X : SymmetricMatrix p) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ I) :
    shiftedPrincipalMinor Sigma I c X =
      (((X : Matrix (Fin p) (Fin p) ℝ).submatrix (fun i ↦ (e i : Fin p))
        (fun i ↦ (e i : Fin p))) +
        c • Sigma.submatrix (fun i ↦ (e i : Fin p)) (fun i ↦ (e i : Fin p))).det := by
  let A : Matrix I I ℝ :=
    (X : Matrix (Fin p) (Fin p) ℝ).submatrix (fun i : I => (i : Fin p))
      (fun i : I => (i : Fin p)) +
      c • Sigma.submatrix (fun i : I => (i : Fin p)) (fun i : I => (i : Fin p))
  calc
    _ = (A.submatrix e e).det := (Matrix.det_submatrix_equiv_self e A).symm
    _ = _ := rfl

theorem allFiniteMoments_shiftedPrincipalMinor
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (I : Finset (Fin p)) (c : ℝ) :
    HasAllFiniteMoments (shiftedPrincipalMinor Sigma I c)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  apply HasAllFiniteMoments.det
  intro i j
  exact (allFiniteMoments_wishart_entry (α := α) (Sigma := Sigma)
    (i : Fin p) (j : Fin p)).add (HasAllFiniteMoments.const (c * Sigma i j))

theorem allFiniteMoments_shiftedMomentIntegrand
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) :
    HasAllFiniteMoments (shiftedMomentIntegrand Sigma P c ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact HasAllFiniteMoments.finset_prod J _ fun i _ ↦
    (allFiniteMoments_shiftedPrincipalMinor hSigma hα (P.block i) (c i)).rpow (hν i)

theorem ae_shiftedMomentIntegrand_pos
    (α : ℝ) {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) :
    ∀ᵐ X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma,
      0 < shiftedMomentIntegrand Sigma P c ν J X := by
  filter_upwards [TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma] with X hX
  exact Finset.prod_pos fun i _ ↦
    Real.rpow_pos_of_pos (shiftedPrincipalMinor_pos hSigma (P.block i) (hc i) X hX) _

theorem shiftedMoment_pos
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) :
    0 < shiftedMoment α Sigma P c ν J := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact integral_pos_of_pos_ae
    (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν J).integrable
    (ae_shiftedMomentIntegrand_pos α hSigma P c ν hc J)

theorem shiftedTiltLaw_probability
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) :
    IsProbabilityMeasure (shiftedTiltLaw α Sigma P c ν J) :=
  normalizedWeight_probability_of_integrable_pos_ae _ _
    ((ae_shiftedMomentIntegrand_pos α hSigma P c ν hc J).mono fun _ hx ↦ hx.le)
    (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν J).integrable
    (shiftedMoment_pos hSigma hα P c ν hc hν J)

end

end WishartVerification
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/ShiftedPrincipalNormalization.lean -/



open scoped Classical Matrix
open MeasureTheory

/-!
# Exact normalization of proportional principal shifts

Whitening transforms `X_II + c Σ_II` into `S + c I` and leaves every
complementary shifted principal matrix unchanged. The scale multiplier remains
exactly `det(Σ_II)^η`, as in the unshifted theorem.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

def shiftedMatrixDetPower {q : ℕ} (c η : ℝ) (S : SymmetricMatrix q) : ℝ :=
  ((S : Matrix (Fin q) (Fin q) ℝ) + c • (1 : Matrix (Fin q) (Fin q) ℝ)).det ^ η

theorem shiftedMatrixDetPower_measurable {q : ℕ} (c η : ℝ) :
    Measurable (shiftedMatrixDetPower (q := q) c η) :=
  (continuous_subtype_val.add continuous_const).matrix_det.measurable.pow_const _

theorem normalizedSelectedMatrix_add_smul
    (I : Finset (Fin p)) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (X Y : SymmetricMatrix p) (c : ℝ) :
    Wishart.normalizedSelectedMatrix I Sigma (X + c • Y) =
      Wishart.normalizedSelectedMatrix I Sigma X + c • Wishart.normalizedSelectedMatrix I Sigma Y := by
  unfold Wishart.normalizedSelectedMatrix
  simp only [Wishart.principalSymmetricBlock_eq_congruence, map_add, map_smul]

theorem regressionScale_leading_identity {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    (Wishart.regressionScale K C).submatrix (Fin.castAdd m) (Fin.castAdd m) = 1 := by
  ext i j
  simp [Wishart.regressionScale, Matrix.submatrix_apply]

theorem normalizedSelectedMatrix_scale_leading
    (I : Finset (Fin p)) {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) :
    (Wishart.principalSymmetricBlock (Fin.castAdd (Wishart.complementDimension I))
      (Wishart.normalizedSelectedMatrix I Sigma ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩) :
        Matrix (Fin (Wishart.selectedDimension I)) (Fin (Wishart.selectedDimension I)) ℝ) = 1 := by
  change (Wishart.normalizedSelectedMatrix I Sigma ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩ :
      Matrix (Fin (Wishart.selectedDimension I + Wishart.complementDimension I))
        (Fin (Wishart.selectedDimension I + Wishart.complementDimension I)) ℝ).submatrix
          (Fin.castAdd (Wishart.complementDimension I))
          (Fin.castAdd (Wishart.complementDimension I)) = 1
  unfold Wishart.normalizedSelectedMatrix
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply]
  change (Wishart.selectedWhitening _ _
      (Sigma.submatrix (Wishart.selectedCoordinatesEquiv I) (Wishart.selectedCoordinatesEquiv I)) *
        Sigma.submatrix (Wishart.selectedCoordinatesEquiv I) (Wishart.selectedCoordinatesEquiv I) *
          (Wishart.selectedWhitening _ _
            (Sigma.submatrix (Wishart.selectedCoordinatesEquiv I) (Wishart.selectedCoordinatesEquiv I)))ᵀ).submatrix
              (Fin.castAdd (Wishart.complementDimension I))
              (Fin.castAdd (Wishart.complementDimension I)) = 1
  rw [Wishart.selectedWhitening_scale (hSigma.submatrix (Wishart.selectedCoordinatesEquiv I).injective),
    regressionScale_leading_identity]

theorem normalizedSelectedMatrix_shiftedDeterminant
    (I : Finset (Fin p)) {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (c : ℝ) (X : SymmetricMatrix p) :
    ((Wishart.principalSymmetricBlock (Fin.castAdd (Wishart.complementDimension I))
      (Wishart.normalizedSelectedMatrix I Sigma X) :
        Matrix (Fin (Wishart.selectedDimension I)) (Fin (Wishart.selectedDimension I)) ℝ) +
          c • (1 : Matrix (Fin (Wishart.selectedDimension I)) (Fin (Wishart.selectedDimension I)) ℝ)).det =
      (Sigma.submatrix (fun a : I ↦ (a : Fin p)) (fun b : I ↦ (b : Fin p))).det⁻¹ *
        shiftedPrincipalMinor Sigma I c X := by
  let S : SymmetricMatrix p := ⟨Sigma, hSigma.isHermitian.isSelfAdjoint⟩
  have h := Wishart.normalizedSelectedMatrix_selectedDeterminant I hSigma (X + c • S)
  rw [normalizedSelectedMatrix_add_smul] at h
  have hadd : (Wishart.principalSymmetricBlock (Fin.castAdd (Wishart.complementDimension I))
      (Wishart.normalizedSelectedMatrix I Sigma X + c • Wishart.normalizedSelectedMatrix I Sigma S) :
        Matrix (Fin (Wishart.selectedDimension I)) (Fin (Wishart.selectedDimension I)) ℝ) =
      (Wishart.principalSymmetricBlock (Fin.castAdd (Wishart.complementDimension I))
        (Wishart.normalizedSelectedMatrix I Sigma X) :
          Matrix (Fin (Wishart.selectedDimension I)) (Fin (Wishart.selectedDimension I)) ℝ) + c • 1 := by
    have hscale := normalizedSelectedMatrix_scale_leading I hSigma
    ext a b
    have hab := congrArg (fun M : Matrix (Fin (Wishart.selectedDimension I))
      (Fin (Wishart.selectedDimension I)) ℝ ↦ M a b) hscale
    simpa only [Wishart.principalSymmetricBlock, Submodule.coe_add,
      Submodule.coe_smul, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, S] using
        congrArg (fun t : ℝ ↦
          (Wishart.normalizedSelectedMatrix I Sigma X :
            Matrix (Fin (Wishart.selectedDimension I + Wishart.complementDimension I))
              (Fin (Wishart.selectedDimension I + Wishart.complementDimension I)) ℝ)
                (Fin.castAdd (Wishart.complementDimension I) a)
                (Fin.castAdd (Wishart.complementDimension I) b) + c * t) hab
  rw [hadd] at h
  have hminor : principalMinor I (X + c • S) = shiftedPrincipalMinor Sigma I c X := by
    unfold principalMinor shiftedPrincipalMinor
    congr 1
  rw [hminor] at h
  exact h

def shiftedLeadingTest (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  shiftedMatrixDetPower (c j) (ν j)
    (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) Y)

def shiftedRemainingCompressionData (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) : CompressionData (remainingRank P j) where
  size := Fintype.card (P.block i)
  offset := c i • Sigma.submatrix
    (fun a ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
    (fun b ↦ ((Fintype.equivFin (P.block i)).symm b : Fin p))
  linear := (remainingCompressionData P ν J j i).linear
  exponent := ν i

def shiftedRemainingTest (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) : SymmetricMatrix (remainingRank P j) → ℝ :=
  compressionProduct (shiftedRemainingCompressionData Sigma P c ν J j)

def shiftedTrailingTest (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  shiftedRemainingTest Sigma P c ν J j
    (Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j)) Y)

def shiftedJointTest (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  shiftedLeadingTest P c ν j Y * shiftedTrailingTest Sigma P c ν J j Y

theorem shiftedLeadingTest_measurable (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (j : Fin d) : Measurable (shiftedLeadingTest P c ν j) :=
  (shiftedMatrixDetPower_measurable _ _).comp (Wishart.measurable_principalSymmetricBlock _)

theorem shiftedRemainingTest_measurable (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (shiftedRemainingTest Sigma P c ν J j) := compressionProduct_measurable _

theorem shiftedTrailingTest_measurable (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (shiftedTrailingTest Sigma P c ν J j) :=
  (shiftedRemainingTest_measurable Sigma P c ν J j).comp
    (Wishart.measurable_principalSymmetricBlock _)

theorem shiftedJointTest_measurable (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (shiftedJointTest Sigma P c ν J j) :=
  (shiftedLeadingTest_measurable P c ν j).mul
    (shiftedTrailingTest_measurable Sigma P c ν J j)

theorem shiftedRemainingCompressionData_offset_posSemidef
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) :
    (shiftedRemainingCompressionData Sigma P c ν J j i).offset.PosSemidef :=
  (hSigma.posSemidef.submatrix _).smul (hc i)

theorem shiftedCompression_det_normalized
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (i : J.erase j)
    (X : SymmetricMatrix p) :
    ((shiftedRemainingCompressionData Sigma P c ν J j i).offset +
      (shiftedRemainingCompressionData Sigma P c ν J j i).linearᵀ *
        (Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j))
          (normalizedPrincipalMatrix P Sigma j X) :
            Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
        (shiftedRemainingCompressionData Sigma P c ν J j i).linear).det =
      shiftedPrincipalMinor Sigma (P.block i) (c i) X := by
  change ((c i • Sigma.submatrix
      (fun a : Fin (Fintype.card (P.block i)) => ((Fintype.equivFin (P.block i)).symm a : Fin p))
      (fun a : Fin (Fintype.card (P.block i)) => ((Fintype.equivFin (P.block i)).symm a : Fin p))) +
    ((1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
      (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1))ᵀ *
      ((Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j))
        (normalizedPrincipalMatrix P Sigma j X) : SymmetricMatrix (remainingRank P j)) :
          Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
      (1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
        (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1)).det = _
  rw [Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]
  have h := Wishart.normalizedSelectedMatrix_complementarySubmatrix
    (P.block j) Sigma X
    (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
    (fun a haj ↦ Finset.disjoint_left.mp (P.disjoint (Finset.mem_erase.mp i.property).1)
      ((Fintype.equivFin (P.block i)).symm a).property haj)
  have hsub : ((Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j))
      (normalizedPrincipalMatrix P Sigma j X) : SymmetricMatrix (remainingRank P j)) :
        Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix
          (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1)
          (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1) =
      (X : Matrix (Fin p) (Fin p) ℝ).submatrix
        (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
        (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p)) := by
    simpa only [Wishart.principalSymmetricBlock, Matrix.submatrix_submatrix,
      Function.comp_def, remainingBlockCoordinates, normalizedPrincipalMatrix] using h
  rw [hsub, add_comm]
  exact (shiftedPrincipalMinor_eq_det_enumeration Sigma (P.block i) (c i) X
    (Fintype.equivFin (P.block i)).symm).symm

theorem shiftedTrailingTest_normalized
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (X : SymmetricMatrix p) :
    shiftedTrailingTest Sigma P c ν J j (normalizedPrincipalMatrix P Sigma j X) =
      shiftedMomentIntegrand Sigma P c ν (J.erase j) X := by
  calc
    _ = ∏ i : J.erase j, shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i := by
      unfold shiftedTrailingTest shiftedRemainingTest compressionProduct
      apply Finset.prod_congr rfl
      intro i hi
      rw [shiftedCompression_det_normalized]
      rfl
    _ = shiftedMomentIntegrand Sigma P c ν (J.erase j) X :=
      Finset.prod_coe_sort (J.erase j)
        (fun i => shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i)

theorem shiftedFactor_eq_scaled_leading
    (P : PrincipalPartition p d) {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (j : Fin d) (X : SymmetricMatrix p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    shiftedPrincipalMinor Sigma (P.block j) (c j) X ^ ν j =
      principalMomentScale P Sigma ν j *
        shiftedLeadingTest P c ν j (normalizedPrincipalMatrix P Sigma j X) := by
  have ha : 0 < (Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
      (fun b : P.block j ↦ (b : Fin p))).det :=
    (hSigma.submatrix Subtype.coe_injective).det_pos
  have hx := shiftedPrincipalMinor_pos hSigma (P.block j) (hc j) X hX
  unfold shiftedLeadingTest shiftedMatrixDetPower principalMomentScale
  rw [normalizedSelectedMatrix_shiftedDeterminant (P.block j) hSigma (c j) X,
    Real.mul_rpow (inv_nonneg.mpr ha.le) hx.le, Real.inv_rpow ha.le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos ha (ν j)).ne', one_mul]

theorem shiftedJointIntegrand_eq_scaled_normalized
    (P : PrincipalPartition p d) {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (X : SymmetricMatrix p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    shiftedMomentIntegrand Sigma P c ν J X = principalMomentScale P Sigma ν j *
      shiftedJointTest Sigma P c ν J j (normalizedPrincipalMatrix P Sigma j X) := by
  rw [shiftedJointTest, shiftedTrailingTest_normalized]
  have hprod := Finset.mul_prod_erase J
    (fun i ↦ shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i) hj
  change _ = _ * (_ * ∏ i ∈ J.erase j, shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i)
  rw [← mul_assoc, ← shiftedFactor_eq_scaled_leading P hSigma c ν hc j X hX]
  exact hprod.symm

theorem shifted_normalization_moments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    shiftedMoment α Sigma P c ν J = principalMomentScale P Sigma ν j *
      (∫ Y, shiftedJointTest Sigma P c ν J j Y ∂normalizedPrincipalMeasure α Sigma P j) ∧
    shiftedMoment α Sigma P c ν {j} = principalMomentScale P Sigma ν j *
      (∫ Y, shiftedLeadingTest P c ν j Y ∂normalizedPrincipalMeasure α Sigma P j) ∧
    shiftedMoment α Sigma P c ν (J.erase j) =
      (∫ Y, shiftedTrailingTest Sigma P c ν J j Y ∂normalizedPrincipalMeasure α Sigma P j) := by
  have hmp := normalizedPrincipalMatrix_measurePreserving P hSigma hα j
  have hpos := TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma
  refine ⟨?_, ?_, ?_⟩
  · exact integral_eq_scaled_of_pullback hmp _ _ _
      (shiftedJointTest_measurable Sigma P c ν J j)
      (hpos.mono fun X hX ↦ shiftedJointIntegrand_eq_scaled_normalized P hSigma c ν hc J j hj X hX)
  · apply integral_eq_scaled_of_pullback hmp _ _ _ (shiftedLeadingTest_measurable P c ν j)
    filter_upwards [hpos] with X hX
    simpa only [shiftedMomentIntegrand, Finset.prod_singleton] using
      shiftedFactor_eq_scaled_leading P hSigma c ν hc j X hX
  · have h := integral_eq_scaled_of_pullback hmp (shiftedMomentIntegrand Sigma P c ν (J.erase j))
      (shiftedTrailingTest Sigma P c ν J j) 1 (shiftedTrailingTest_measurable Sigma P c ν J j)
      (ae_of_all _ fun X ↦ by
        simpa only [one_mul] using
          (shiftedTrailingTest_normalized Sigma P c ν J j X).symm)
    simpa only [one_mul, shiftedMoment] using h

theorem shifted_normalization_allFiniteMoments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    HasAllFiniteMoments (shiftedLeadingTest P c ν j) (normalizedPrincipalMeasure α Sigma P j) ∧
    HasAllFiniteMoments (shiftedTrailingTest Sigma P c ν J j) (normalizedPrincipalMeasure α Sigma P j) ∧
    HasAllFiniteMoments (shiftedJointTest Sigma P c ν J j) (normalizedPrincipalMeasure α Sigma P j) := by
  have hmp := normalizedPrincipalMatrix_measurePreserving P hSigma hα j
  have hpos := TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma
  have hscale := (principalMomentScale_pos P hSigma ν j).ne'
  refine ⟨?_, ?_, ?_⟩
  · apply allFiniteMoments_of_scaled_pullback hmp
      (shiftedMomentIntegrand Sigma P c ν {j}) _ _ hscale
      (shiftedLeadingTest_measurable P c ν j)
      (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν {j})
    filter_upwards [hpos] with X hX
    simpa only [shiftedMomentIntegrand, Finset.prod_singleton] using
      shiftedFactor_eq_scaled_leading P hSigma c ν hc j X hX
  · exact allFiniteMoments_of_scaled_pullback hmp
      (shiftedMomentIntegrand Sigma P c ν (J.erase j)) _ 1 one_ne_zero
      (shiftedTrailingTest_measurable Sigma P c ν J j)
      (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν (J.erase j))
      (ae_of_all _ fun X ↦ by
        simpa only [one_mul] using
          (shiftedTrailingTest_normalized Sigma P c ν J j X).symm)
  · exact allFiniteMoments_of_scaled_pullback hmp
      (shiftedMomentIntegrand Sigma P c ν J) _ _ hscale
      (shiftedJointTest_measurable Sigma P c ν J j)
      (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν J)
      (hpos.mono fun X hX ↦ shiftedJointIntegrand_eq_scaled_normalized P hSigma c ν hc J j hj X hX)

end

end WishartVerification
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/TiltTransport.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Transport of actual probability tilts

A tilt by a function of a measurable statistic commutes with pushforward.
Tilting only the first coordinate of an independent product preserves the
second marginal and independence. These measure equalities justify the Haar
frame statement in the single-factor spectral tilt.
-/

namespace WishartVerification

variable {Ω Ψ Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace Θ]

theorem map_withDensity_comp_of_measurePreserving
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    (w : Ψ → ℝ≥0∞) (hwm : Measurable w) :
    (μ.withDensity (w ∘ T)).map T = ν.withDensity w := by
  apply Measure.ext_of_lintegral
  intro f hfm
  rw [lintegral_map hfm hT.measurable]
  change (∫⁻ a, (f ∘ T) a ∂μ.withDensity (w ∘ T)) = ∫⁻ a, f a ∂ν.withDensity w
  rw [lintegral_withDensity_eq_lintegral_mul _ (hwm.comp hT.measurable) (hfm.comp hT.measurable),
    lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
  simpa only [Function.comp_apply, Pi.mul_apply] using hT.lintegral_comp (hwm.mul hfm)

theorem map_normalizedWeight_of_measurePreserving
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    (u : Ω → ℝ) (v : Ψ → ℝ) (hvm : Measurable v)
    (huv : u =ᵐ[μ] v ∘ T) :
    (normalizedWeight μ u).map T = normalizedWeight ν v := by
  rw [normalizedWeight_congr_ae μ u (v ∘ T) huv]
  unfold normalizedWeight
  rw [Measure.map_smul _ hT.measurable.aemeasurable]
  have hwd : (μ.withDensity (fun x ↦ ENNReal.ofReal ((v ∘ T) x))).map T =
      ν.withDensity (fun x ↦ ENNReal.ofReal (v x)) := by
    simpa only [Function.comp_def] using
      map_withDensity_comp_of_measurePreserving hT _ hvm.ennreal_ofReal
  rw [hwd]
  have hZ := hT.lintegral_comp hvm.ennreal_ofReal
  simpa only [Function.comp_apply] using congrArg
    (fun z : ℝ≥0∞ ↦ z⁻¹ • ν.withDensity (fun x ↦ ENNReal.ofReal (v x))) hZ

theorem normalizedWeight_prod_fst
    (μ : Measure Ω) [SFinite μ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (w : Ω → ℝ) (hwm : Measurable w) :
    normalizedWeight (μ.prod ν) (fun x ↦ w x.1) = (normalizedWeight μ w).prod ν := by
  have hZ := (measurePreserving_fst (μ := μ) (ν := ν)).lintegral_comp hwm.ennreal_ofReal
  unfold normalizedWeight
  rw [hZ, Measure.prod_smul_left, prod_withDensity_left hwm.ennreal_ofReal]

theorem measurePreserving_normalizedWeight
    {μ : Measure Ω} {ν : Measure Ψ} {T : Ω → Ψ} (hT : MeasurePreserving T μ ν)
    (u : Ω → ℝ) (v : Ψ → ℝ) (hvm : Measurable v)
    (huv : u =ᵐ[μ] v ∘ T) :
    MeasurePreserving T (normalizedWeight μ u) (normalizedWeight ν v) :=
  ⟨hT.measurable, map_normalizedWeight_of_measurePreserving hT u v hvm huv⟩

end WishartVerification
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/SpectralTestMoments.lean -/



open scoped Classical
open MeasureTheory

/-!
# General selected spectral tests in the actual regression law

This extension of the determinant-only moment identities accepts a selected
matrix test whose equality to a spectral test is proved on the actual
Laguerre–Haar source. It is used for shifted determinants and bounded tests of
the entire ordered selected spectrum, as required for stochastic domination.
-/

namespace Wishart

open TauCeti TauCeti.Probability WishartVerification

variable {q m : ℕ} {n : ℝ}

theorem integrable_spectralTest_mul_haarRegressionIntegrand
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {H : (Fin q → ℝ) → ℝ}
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hH : (fun x ↦ h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))] (fun x ↦ H x.1))
    (hjoint : Integrable (fun X ↦ h (principalSymmetricBlock (Fin.castAdd m) X) *
      g (principalSymmetricBlock (Fin.natAdd q) X))
        (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun x ↦ H x.1 * haarRegressionIntegrand n C K g x)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hi := integrable_regression_selected_mul_conditional hn K hC hjoint
  apply ((measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable hi).congr
  filter_upwards [hH, ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
  exact congrArg₂ (· * ·) hx hy

theorem integral_regression_selected_spectralTest
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {H : (Fin q → ℝ) → ℝ}
    (hhm : Measurable h)
    (hH : (fun x ↦ h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))] (fun x ↦ H x.1)) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, H lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  rw [integral_regression_selected hn K hC hhm,
    integral_regressionSpectralMatrix hnq hhm.aestronglyMeasurable,
    integral_congr_ae hH, integral_fun_fst]
  simp only [probReal_univ, one_smul]

theorem integral_regression_joint_spectralTest
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {H : (Fin q → ℝ) → ℝ}
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hH : (fun x ↦ h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))] (fun x ↦ H x.1))
    (hjoint : Integrable (fun X ↦ h (principalSymmetricBlock (Fin.castAdd m) X) *
      g (principalSymmetricBlock (Fin.natAdd q) X))
        (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X) *
        g (principalSymmetricBlock (Fin.natAdd q) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, H lam * regressionSpectralAverage n C K g lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hcond := integrable_regression_selected_mul_conditional hn K hC hjoint
  rw [integral_regression_selected_mul_remaining hn K hC hjoint,
    integral_regressionSpectralMatrix hnq hcond.aestronglyMeasurable]
  have heq : (fun x ↦ h (regressionSpectralMatrix x) *
      regressionConditionalMoment n C K g (regressionSpectralMatrix x)) =ᵐ[
        (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      (fun x ↦ H x.1 * haarRegressionIntegrand n C K g x) := by
    filter_upwards [hH, ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
    exact congrArg₂ (· * ·) hx hy
  rw [integral_congr_ae heq]
  exact (integral_mul_parameterAverageOn _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_spectralTest_mul_haarRegressionIntegrand hn K hC hgm hH hjoint)).symm

theorem integrable_spectralTest_mul_regressionSpectralAverage
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {H : (Fin q → ℝ) → ℝ}
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hH : (fun x ↦ h (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))] (fun x ↦ H x.1))
    (hjoint : Integrable (fun X ↦ h (principalSymmetricBlock (Fin.castAdd m) X) *
      g (principalSymmetricBlock (Fin.natAdd q) X))
        (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun lam ↦ H lam * regressionSpectralAverage n C K g lam)
      (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  exact mul_parameterAverageOn_integrable _ _ _ (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_spectralTest_mul_haarRegressionIntegrand hn K hC hgm hH hjoint)

end Wishart
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/SeparateWeightTilts.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Separate-coordinate tilts preserve the actual chamber association law

Multiplying by a product of one-coordinate factors changes exactly the
individual weights. The statement includes the positive finite normalizer and
identifies the whole tilted probability measure before invoking association.
-/

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem chamberWeight_mul_separate (s : Set ℝ) (w v : ι → ℝ → ℝ)
    (β : ℝ) (x : ι → ℝ) :
    chamberWeight s (fun i t ↦ w i t * v i t) β x =
      chamberWeight s w β x * ∏ i, v i (x i) := by
  have hind (i : ι) : s.indicator (fun t ↦ w i t * v i t) (x i) =
      s.indicator (w i) (x i) * v i (x i) := by
    by_cases hx : x i ∈ s <;> simp [hx]
  simp only [chamberWeight, vandermondeWeight, hind, Finset.prod_mul_distrib]
  ring

theorem separateWeight_tilt_law
    (s : Set ℝ) (hs : MeasurableSet s) (w v : ι → ℝ → ℝ) (β : ℝ)
    (hwm : ∀ i, Measurable (w i)) (hvm : ∀ i, Measurable (v i))
    (hw0 : ∀ i t, 0 ≤ w i t) (hv0 : ∀ i t, 0 ≤ v i t)
    (hvi : Integrable (fun x : ι → ℝ ↦ ∏ i, v i (x i))
      (normalizedWeight volume (chamberWeight s w β)))
    (hvpos : 0 < ∫ x : ι → ℝ, (∏ i, v i (x i))
      ∂normalizedWeight volume (chamberWeight s w β)) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (chamberWeight s (fun i t ↦ w i t * v i t) β x)) ≠ 0 ∧
    (∫⁻ x : ι → ℝ, ENNReal.ofReal
      (chamberWeight s (fun i t ↦ w i t * v i t) β x)) ≠ ∞ ∧
    normalizedWeight (normalizedWeight volume (chamberWeight s w β))
      (fun x ↦ ∏ i, v i (x i)) =
        normalizedWeight volume (chamberWeight s (fun i t ↦ w i t * v i t) β) := by
  let V : (ι → ℝ) → ℝ := fun x ↦ ∏ i, v i (x i)
  have hVm : Measurable V := Finset.measurable_prod _ fun i _ ↦
    (hvm i).comp (measurable_pi_apply i)
  have hV0 (x) : 0 ≤ V x := Finset.prod_nonneg fun i _ ↦ hv0 i (x i)
  letI := normalizedWeight_probability_of_integrable_pos
    (normalizedWeight volume (chamberWeight s w β)) V hV0 hvi hvpos
  let c := (∫⁻ x, ENNReal.ofReal (V x)
      ∂normalizedWeight volume (chamberWeight s w β))⁻¹ *
    (∫⁻ x, ENNReal.ofReal (chamberWeight s w β x))⁻¹
  have hlaw : normalizedWeight (normalizedWeight volume (chamberWeight s w β)) V =
      c • volume.withDensity (fun x ↦ ENNReal.ofReal
        (chamberWeight s (fun i t ↦ w i t * v i t) β x)) := by
    unfold normalizedWeight
    rw [withDensity_smul_measure,
      ← withDensity_mul volume (chamberWeight_measurable s hs w β hwm).ennreal_ofReal
        hVm.ennreal_ofReal, smul_smul]
    congr 2
    funext x
    rw [chamberWeight_mul_separate, ENNReal.ofReal_mul (chamberWeight_nonneg s w β hw0 x)]
    rfl
  exact normalizedWeight_eq_of_probability_density _ volume _ c hlaw

/-- Association under the single-factor tilt, with the changed coordinate
weights and normalizer derived from the actual original chamber law. -/
theorem separateWeight_tilt_association
    (s : Set ℝ) (hs : MeasurableSet s) (w v : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hvm : ∀ i, Measurable (v i))
    (hw0 : ∀ i t, 0 ≤ w i t) (hv0 : ∀ i t, 0 ≤ v i t)
    (hvi : Integrable (fun x : ι → ℝ ↦ ∏ i, v i (x i))
      (normalizedWeight volume (chamberWeight s w β)))
    (hvpos : 0 < ∫ x : ι → ℝ, (∏ i, v i (x i))
      ∂normalizedWeight volume (chamberWeight s w β))
    (f g : (ι → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmono : MonotoneOn f (orderedChamber s))
    (hgmono : MonotoneOn g (orderedChamber s)) :
    (∫⁻ x, ENNReal.ofReal (f x)
      ∂normalizedWeight (normalizedWeight volume (chamberWeight s w β))
        (fun x ↦ ∏ i, v i (x i))) *
      (∫⁻ x, ENNReal.ofReal (g x)
        ∂normalizedWeight (normalizedWeight volume (chamberWeight s w β))
          (fun x ↦ ∏ i, v i (x i))) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x)
        ∂normalizedWeight (normalizedWeight volume (chamberWeight s w β))
          (fun x ↦ ∏ i, v i (x i)) := by
  obtain ⟨hZ0, hZtop, htilt⟩ := separateWeight_tilt_law s hs w v β hwm hvm hw0 hv0 hvi hvpos
  rw [htilt]
  exact lemma_2_1_association s hs (fun i t ↦ w i t * v i t) β hβ
    (fun i ↦ (hwm i).mul (hvm i))
    (fun i t ↦ mul_nonneg (hw0 i t) (hv0 i t)) hZ0 hZtop
    f g hfm hgm hf0 hg0 hfmono hgmono

end WishartVerification
end CanonicalSource5

section CanonicalSource6
/- Source: Wishart/ShiftedSpectralFunctions.lean -/



open scoped Classical Matrix
open MeasureTheory

/-!
# Shifted determinant powers on the actual positive spectrum

The nonnegative extension agrees with `det(S + c I)^η` on the proved
Laguerre–Haar source. It has all nonnegative moments. Its product form gives
the precise individual weights of the single-factor tilted eigenvalue law.
-/

namespace WishartVerification

noncomputable section

variable {ι : Type*} [Fintype ι]

def shiftedSpectralDetPower (c η : ℝ) (lam : ι → ℝ) : ℝ :=
  ∏ i, (max (lam i + c) 0) ^ η

theorem shiftedSpectralDetPower_nonneg (c η : ℝ) (lam : ι → ℝ) :
    0 ≤ shiftedSpectralDetPower c η lam :=
  Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (le_max_right _ _) _

theorem shiftedSpectralDetPower_measurable (c η : ℝ) :
    Measurable (shiftedSpectralDetPower (ι := ι) c η) := by
  unfold shiftedSpectralDetPower
  apply Finset.measurable_prod
  intro i hi
  have hadd : Measurable (fun lam : ι → ℝ ↦ lam i + c) := by fun_prop
  have hmax : Measurable (fun lam : ι → ℝ ↦ max (lam i + c) 0) :=
    hadd.max measurable_const
  exact hmax.pow_const η

theorem shiftedSpectralDetPower_monotone (c η : ℝ) (hη : 0 ≤ η) :
    Monotone (shiftedSpectralDetPower (ι := ι) c η) := by
  intro x y hxy
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Real.rpow_nonneg (le_max_right _ _) _
  · intro i hi
    have hadd : x i + c ≤ y i + c := by linarith [hxy i]
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max hadd le_rfl) hη

theorem shiftedSpectralDetPower_pos {c : ℝ} (hc : 0 ≤ c) (η : ℝ)
    (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) :
    0 < shiftedSpectralDetPower c η lam :=
  Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos
    ((add_pos_of_pos_of_nonneg (hlam i) hc).trans_le (le_max_left _ _)) _

theorem shiftedSpectralDetPower_add_exponent {c : ℝ} (hc : 0 ≤ c)
    (η t : ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) :
    shiftedSpectralDetPower c (η + t) lam =
      shiftedSpectralDetPower c η lam * shiftedSpectralDetPower c t lam := by
  unfold shiftedSpectralDetPower
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.rpow_add
    ((add_pos_of_pos_of_nonneg (hlam i) hc).trans_le (le_max_left _ _)) η t

theorem shiftedSpectralDetPower_eq_diagonal_det_rpow [DecidableEq ι]
    {c : ℝ} (hc : 0 ≤ c) (η : ℝ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) :
    shiftedSpectralDetPower c η lam =
      (Matrix.diagonal (fun i ↦ lam i + c)).det ^ η := by
  rw [Matrix.det_diagonal, nonnegative_prod_rpow _
    (fun i ↦ (add_pos_of_pos_of_nonneg (hlam i) hc).le) η]
  apply Finset.prod_congr rfl
  intro i hi
  rw [max_eq_left (add_pos_of_pos_of_nonneg (hlam i) hc).le]

theorem shiftedMatrixDetPower_conjugate_diagonal {q : ℕ}
    (O : Wishart.Spectral.Orth q) {c : ℝ} (hc : 0 ≤ c)
    (η : ℝ) (lam : Fin q → ℝ) (hlam : ∀ i, 0 < lam i) :
    shiftedMatrixDetPower c η (Wishart.Spectral.conjugate O (Wishart.Spectral.diagonalSym lam)) =
      shiftedSpectralDetPower c η lam := by
  have hdiag : Matrix.diagonal (fun i ↦ lam i + c) = Matrix.diagonal lam +
      c • (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  have hmat :
      (Wishart.Spectral.conjugate O (Wishart.Spectral.diagonalSym lam) :
        Matrix (Fin q) (Fin q) ℝ) + c • 1 =
      (Wishart.Spectral.conjugate O (Wishart.Spectral.diagonalSym (fun i ↦ lam i + c)) :
        Matrix (Fin q) (Fin q) ℝ) := by
    rw [show (Wishart.Spectral.conjugate O (Wishart.Spectral.diagonalSym (fun i ↦ lam i + c)) :
        Matrix (Fin q) (Fin q) ℝ) = (O : Matrix (Fin q) (Fin q) ℝ) *
          Matrix.diagonal (fun i ↦ lam i + c) * (O : Matrix (Fin q) (Fin q) ℝ)ᵀ from
            Matrix.coe_symmetricCongruenceLinearMap_apply _ _]
    rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Wishart.Spectral.orth_mul_transpose]
    exact congrArg (fun A : Matrix (Fin q) (Fin q) ℝ => A + c • 1)
      (Matrix.coe_symmetricCongruenceLinearMap_apply
        (O : Matrix (Fin q) (Fin q) ℝ) (Wishart.Spectral.diagonalSym lam))
  unfold shiftedMatrixDetPower
  rw [hmat, Wishart.Spectral.det_conjugate]
  exact (shiftedSpectralDetPower_eq_diagonal_det_rpow hc η lam hlam).symm

theorem ae_shiftedMatrixDetPower_spectral {q : ℕ} {α c : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (η : ℝ) :
    (fun x ↦ shiftedMatrixDetPower c η (Wishart.regressionSpectralMatrix x)) =ᵐ[
      (Wishart.regressionEigenLaw q α).prod (TauCeti.haarProb (Wishart.Spectral.Orth q))]
        (fun x ↦ shiftedSpectralDetPower c η x.1) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (Wishart.Spectral.ae_laguerreLaw_mem_chamber hα)] with x hx
  exact shiftedMatrixDetPower_conjugate_diagonal x.2 hc η x.1 hx.2

theorem allFiniteMoments_shiftedMatrixDetPower {q : ℕ} {α η : ℝ}
    (hα : (q : ℝ) - 1 < α) (c : ℝ) (hη : 0 ≤ η) :
    HasAllFiniteMoments (shiftedMatrixDetPower (q := q) c η)
      (TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure Matrix.PosDef.one hα
  have h := allFiniteMoments_wishart_affine_compression_det
    (Sigma := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hα
    (c • (1 : Matrix (Fin q) (Fin q) ℝ)) (1 : Matrix (Fin q) (Fin q) ℝ)
  apply (h.rpow hη).congr_ae
  filter_upwards [] with X
  change ((c • (1 : Matrix (Fin q) (Fin q) ℝ)) +
    (1 : Matrix (Fin q) (Fin q) ℝ)ᵀ * (X : Matrix (Fin q) (Fin q) ℝ) * 1).det ^ η =
      shiftedMatrixDetPower c η X
  simp only [shiftedMatrixDetPower, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, add_comm]

theorem allFiniteMoments_shiftedSpectralDetPower {q : ℕ} {α c η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (hη : 0 ≤ η) :
    HasAllFiniteMoments (shiftedSpectralDetPower (ι := Fin q) c η)
      (Wishart.regressionEigenLaw q α) := by
  letI := Wishart.Spectral.laguerreLaw_isProbability hα
  have hprod := ((allFiniteMoments_shiftedMatrixDetPower hα c hη).comp_measurePreserving
    (Wishart.measurePreserving_regressionSpectralMatrix hα)).congr_ae
      (ae_shiftedMatrixDetPower_spectral hα hc η)
  exact HasAllFiniteMoments.of_comp_measurePreserving measurePreserving_fst
    (shiftedSpectralDetPower_measurable c η) hprod

theorem integral_shiftedSpectralDetPower_pos {q : ℕ} {α c η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (hη : 0 ≤ η) :
    0 < ∫ lam, shiftedSpectralDetPower (ι := Fin q) c η lam ∂Wishart.regressionEigenLaw q α := by
  letI := Wishart.Spectral.laguerreLaw_isProbability hα
  exact integral_pos_of_pos_ae (allFiniteMoments_shiftedSpectralDetPower hα hc hη).integrable
    ((Wishart.Spectral.ae_laguerreLaw_mem_chamber hα).mono
      fun lam hlam ↦ shiftedSpectralDetPower_pos hc η lam hlam.2)

end

end WishartVerification
end CanonicalSource6

section CanonicalSource7
/- Source: Wishart/ShiftedSpectralMoments.lean -/



open scoped Classical
open MeasureTheory

/-!
# The actual spectral moment identities for proportional shifts
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

def shiftedSpectralAverage (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    (Fin (selectedRank P j) → ℝ) → ℝ :=
  Wishart.regressionSpectralAverage α (principalResidualScale P Sigma j)
    (principalCrossScale P Sigma j) (shiftedRemainingTest Sigma P c ν J j)

theorem shiftedSpectralAverage_measurable (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (shiftedSpectralAverage α Sigma P c ν J j) :=
  Wishart.measurable_regressionSpectralAverage _ _ _
    (shiftedRemainingTest_measurable Sigma P c ν J j)

def selectedEigenvalues (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (j : Fin d) (X : SymmetricMatrix p) :
    Fin (selectedRank P j) → ℝ :=
  Wishart.Spectral.ascendingSpectrum
    (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j))
      (normalizedPrincipalMatrix P Sigma j X))

theorem selectedEigenvalues_measurable (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (j : Fin d) :
    Measurable (selectedEigenvalues Sigma P j) :=
  (Wishart.Spectral.continuous_ascendingSpectrum _).measurable.comp
    ((Wishart.measurable_principalSymmetricBlock _).comp
      (Wishart.measurable_normalizedSelectedMatrix (P.block j) Sigma))

theorem shifted_spectral_moments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    shiftedMoment α Sigma P c ν J = principalMomentScale P Sigma ν j *
      (∫ lam, shiftedSpectralDetPower (c j) (ν j) lam *
        shiftedSpectralAverage α Sigma P c ν J j lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    shiftedMoment α Sigma P c ν {j} = principalMomentScale P Sigma ν j *
      (∫ lam, shiftedSpectralDetPower (c j) (ν j) lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    shiftedMoment α Sigma P c ν (J.erase j) =
      (∫ lam, shiftedSpectralAverage α Sigma P c ν J j lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) := by
  have hn := principal_regression_shape P hα j
  have hC := principalResidualScale_posDef P hSigma j
  have hgm := shiftedRemainingTest_measurable Sigma P c ν J j
  have hH := ae_shiftedMatrixDetPower_spectral (principal_spectral_shape P hα j) (hc j) (ν j)
  obtain ⟨_, hgi, hji⟩ := shifted_normalization_allFiniteMoments P hSigma hα c ν hc hν J j hj
  obtain ⟨hjoint, hselected, hremaining⟩ := shifted_normalization_moments P hSigma hα c ν hc J j hj
  have hjointSpec := Wishart.integral_regression_joint_spectralTest hn
    (principalCrossScale P Sigma j) hC hgm hH hji.integrable
  have hselectedSpec := Wishart.integral_regression_selected_spectralTest hn
    (principalCrossScale P Sigma j) hC (shiftedMatrixDetPower_measurable _ _) hH
  have hremainingSpec := Wishart.integral_regression_remaining_spectral hn
    (principalCrossScale P Sigma j) hC hgm hgi.integrable
  exact ⟨hjoint.trans (congrArg (fun r ↦ principalMomentScale P Sigma ν j * r) hjointSpec),
    hselected.trans (congrArg (fun r ↦ principalMomentScale P Sigma ν j * r) hselectedSpec),
    hremaining.trans hremainingSpec⟩

theorem shifted_spectral_integrability
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    Integrable (shiftedSpectralDetPower (c j) (ν j))
      (Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    Integrable (shiftedSpectralAverage α Sigma P c ν J j)
      (Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    Integrable (fun lam ↦ shiftedSpectralDetPower (c j) (ν j) lam *
      shiftedSpectralAverage α Sigma P c ν J j lam)
      (Wishart.regressionEigenLaw (selectedRank P j) α) := by
  have hn := principal_regression_shape P hα j
  have hC := principalResidualScale_posDef P hSigma j
  have hgm := shiftedRemainingTest_measurable Sigma P c ν J j
  have hH := ae_shiftedMatrixDetPower_spectral (principal_spectral_shape P hα j) (hc j) (ν j)
  obtain ⟨_, hgi, hji⟩ := shifted_normalization_allFiniteMoments P hSigma hα c ν hc hν J j hj
  exact ⟨(allFiniteMoments_shiftedSpectralDetPower
      (principal_spectral_shape P hα j) (hc j) (hν j)).integrable,
    Wishart.integrable_regressionSpectralAverage hn (principalCrossScale P Sigma j) hC hgm hgi.integrable,
    Wishart.integrable_spectralTest_mul_regressionSpectralAverage hn
      (principalCrossScale P Sigma j) hC hgm hH hji.integrable⟩

theorem shifted_identityWishart_tilt_haar_representation {q : ℕ} {α c η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) :
    ((normalizedWeight (Wishart.regressionEigenLaw q α)
      (shiftedSpectralDetPower c η)).prod (TauCeti.haarProb (Wishart.Spectral.Orth q))).map
        Wishart.regressionSpectralMatrix =
      normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α
        (1 : Matrix (Fin q) (Fin q) ℝ)) (shiftedMatrixDetPower c η) := by
  letI := Wishart.Spectral.laguerreLaw_isProbability hα
  rw [← normalizedWeight_prod_fst _ _ _ (shiftedSpectralDetPower_measurable c η)]
  exact map_normalizedWeight_of_measurePreserving
    (Wishart.measurePreserving_regressionSpectralMatrix hα) _ _
    (shiftedMatrixDetPower_measurable c η)
    (ae_shiftedMatrixDetPower_spectral hα hc η).symm

end

end WishartVerification
end CanonicalSource7

section CanonicalSource8
/- Source: Wishart/RegressionShiftedPrincipal.lean -/



/-!
# A fixed positive-semidefinite shift in a single principal determinant

Translating the residual matrix by the shift preserves its positive-definite
support and all moments. Consequently the unrestricted one-determinant strict
comparison remains valid before and after projection to a trailing principal
block. No additional degree inequality is introduced.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem strictMono_shiftedRowsGram_offset_moment
    {q m : ℕ} {ν : Measure (SymmetricMatrix m)} [IsProbabilityMeasure ν]
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (hν : ∀ i j : Fin m, HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) ν)
    (hνpd : ∀ᵐ W : SymmetricMatrix m ∂ν, (W : Matrix (Fin m) (Fin m) ℝ).PosDef)
    {E : Matrix (Fin m) (Fin m) ℝ} (hE : E.PosSemidef)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (a : Fin q) (hv : v a ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ x,
      (E + shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂gaussianResidualMeasure q C ν) (Set.Ici 0) := by
  let e : SymmetricMatrix m := ⟨E, Matrix.isHermitian_iff_isSelfAdjoint.mp hE.isHermitian⟩
  let σ := ν.map (fun W => e + W)
  have hm : Measurable (fun W : SymmetricMatrix m => e + W) := by fun_prop
  have hshift : MeasurePreserving (fun W : SymmetricMatrix m => e + W) ν σ := ⟨hm, rfl⟩
  have hσmom (i j : Fin m) : HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) σ := by
    apply HasAllFiniteMoments.of_comp_measurePreserving hshift (by fun_prop)
    exact (HasAllFiniteMoments.const (E i j)).add (hν i j)
  have hσpd : ∀ᵐ W : SymmetricMatrix m ∂σ, (W : Matrix (Fin m) (Fin m) ℝ).PosDef := by
    rw [ae_map_iff hm.aemeasurable (measurableSet_posDefMatrix m)]
    filter_upwards [hνpd] with W hW
    simpa only [Submodule.coe_add, e, add_comm] using hW.add_posSemidef hE
  have hp : MeasurePreserving (Prod.map id (fun W : SymmetricMatrix m => e + W))
      (gaussianResidualMeasure q C ν) (gaussianResidualMeasure q C σ) :=
    (MeasurePreserving.id
      (Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C))).prod hshift
  have heq (t : ℝ) :
      (∫ x, (shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂gaussianResidualMeasure q C σ) =
      ∫ x, (E + shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂gaussianResidualMeasure q C ν := by
    have hdetm : Measurable (fun x : RegressionNoise q m =>
        (shiftedRowsGram v (Function.update lam a t) x).det ^ η) :=
      (continuous_id.matrix_det.measurable.comp
        (measurable_shiftedRowsGram v (Function.update lam a t))).pow_const η
    rw [← hp.map_eq,
      integral_map hp.measurable.aemeasurable hdetm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    change ((E + (x.2 : Matrix (Fin m) (Fin m) ℝ)) + _) = E + (_ + _)
    abel
  have hstrict := strictMono_shiftedRowsGram_moment hC hσmom hσpd v lam a hv hη
  simpa only [heq] using hstrict

theorem strictMono_regressionRowMoment_offset {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {E : Matrix (Fin m) (Fin m) ℝ} (hE : E.PosSemidef)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (a : Fin q) (hv : v a ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ x,
      (E + shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂regressionNoiseMeasure n q m C) (Set.Ici 0) := by
  have hdegree : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hdegree
  exact strictMono_shiftedRowsGram_offset_moment hC.posSemidef
    (fun i j => allFiniteMoments_wishart_entry (α := n - q) (Sigma := C) i j)
    (ae_posDef_nonsingularWishartMeasure (n - q) C) hE v lam a hv hη

theorem strictMono_spectralConditionalMoment_principal_offset_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin k → Fin m) (hf : Function.Injective f)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (lam : Fin q → ℝ) (a : Fin q)
    (hrow : (fun i => (Oᵀ * K.submatrix id f) a i) ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t => spectralConditionalMoment n C K
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η)
        (Function.update lam a t) O) (Set.Ici 0) := by
  have hkm : k ≤ m := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hnk : ((q + k : ℕ) : ℝ) - 1 < n := by
    have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
    push_cast at hn ⊢
    linarith
  have hm : Measurable (fun T : SymmetricMatrix k =>
      (E + (T : Matrix (Fin k) (Fin k) ℝ)).det ^ η) := by fun_prop
  simp_rw [spectralConditionalMoment_principal hn hC K O _ f hf hm]
  have hv : (WithLp.toLp 2 (fun i => (Oᵀ * K.submatrix id f) a i) :
      EuclideanSpace ℝ (Fin k)) ≠ 0 := by
    intro h
    exact hrow (congrArg WithLp.ofLp h)
  simpa only [spectralConditionalMoment, regressionGramWithMean_spectral_eq_shiftedRowsGram] using
    strictMono_regressionRowMoment_offset hnk (hC.submatrix hf) hE
      (fun a => WithLp.toLp 2 (fun i => (Oᵀ * K.submatrix id f) a i)) lam a hv hη

theorem monotoneOn_spectralConditionalMoment_principal_offset_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin k → Fin m) (hf : Function.Injective f)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun lam => spectralConditionalMoment n C K
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  apply monotoneOn_nonnegative_pi_of_update
  intro lam a
  by_cases hη0 : η = 0
  · subst η
    intro s hs t ht hst
    simp only [spectralConditionalMoment, Real.rpow_zero]
    exact le_rfl
  have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
  by_cases hrow : (fun i => (Oᵀ * K.submatrix id f) a i) = 0
  · have hm : Measurable (fun T : SymmetricMatrix k =>
        (E + (T : Matrix (Fin k) (Fin k) ℝ)).det ^ η) := by fun_prop
    intro s hs t ht hst
    simp_rw [spectralConditionalMoment_principal hn hC K O _ f hf hm,
      spectralConditionalMoment,
      spectralRegressionMean_update_of_row_eq_zero _ _ _ _ hrow]
    exact le_rfl
  · exact (strictMono_spectralConditionalMoment_principal_offset_det
      hn hC K O f hf hE lam a hrow hηpos).monotoneOn

def principalOffsetDetCompressionData {m k : ℕ} (f : Fin k → Fin m)
    (E : Matrix (Fin k) (Fin k) ℝ) (η : ℝ) : Unit → CompressionData m :=
  fun _ => ⟨k, E, (1 : Matrix (Fin m) (Fin m) ℝ).submatrix id f, η⟩

set_option backward.isDefEq.respectTransparency false in
theorem compressionProduct_principalOffsetDet {m k : ℕ} (f : Fin k → Fin m)
    (E : Matrix (Fin k) (Fin k) ℝ) (η : ℝ) (T : SymmetricMatrix m) :
    compressionProduct (principalOffsetDetCompressionData f E η) T =
      (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η := by
  simp only [compressionProduct, Fintype.prod_unique, principalOffsetDetCompressionData,
    Matrix.transpose_submatrix, Matrix.transpose_one, Matrix.submatrix_one_mul_mul_submatrix_one]
  rfl

theorem integrable_haar_spectralConditionalMoment_principal_offset_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m)
    (E : Matrix (Fin k) (Fin k) ℝ) {η : ℝ} (hη : 0 ≤ η) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q => spectralConditionalMoment n C K
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η) lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  have heq : compressionProduct (principalOffsetDetCompressionData f E η) =
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η) :=
    funext (compressionProduct_principalOffsetDet f E η)
  rw [← heq]
  exact integrable_haar_spectralConditionalMoment_compressionProduct hn hC K
    (principalOffsetDetCompressionData f E η) (fun _ => hη) lam

theorem monotoneOn_regressionSpectralAverage_principal_offset_det
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m) (hf : Function.Injective f)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (regressionSpectralAverage n C K
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_spectralConditionalMoment_principal_offset_det hn hC K f E hη lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_spectralConditionalMoment_principal_offset_det hn hC K ↑O f hf hE hη
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem regressionSpectralAverage_principal_offset_det_strict_update
    {q m k : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (f : Fin k → Fin m) (hf : Function.Injective f)
    {E : Matrix (Fin k) (Fin k) ℝ} (hE : E.PosSemidef)
    (hK : K.submatrix id f ≠ 0) {η : ℝ} (hη : 0 < η)
    (lam : Fin q → ℝ) (a : Fin q) {s t : ℝ} (hst : s < t)
    (hs : Function.update lam a s ∈ Spectral.positiveChamber q)
    (ht : Function.update lam a t ∈ Spectral.positiveChamber q) :
    regressionSpectralAverage n C K
      (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η)
        (Function.update lam a s) <
      regressionSpectralAverage n C K
        (fun T => (E + (principalSymmetricBlock f T : Matrix (Fin k) (Fin k) ℝ)).det ^ η)
          (Function.update lam a t) := by
  apply parameterAverageOn_strict_compare _ _ _ hs ht
    (integrable_haar_spectralConditionalMoment_principal_offset_det hn hC K f E hη.le _)
    (integrable_haar_spectralConditionalMoment_principal_offset_det hn hC K f E hη.le _)
  filter_upwards [Spectral.haar_transpose_row_mul_ne_zero (K.submatrix id f) hK a] with O hO
  have hs0 : 0 ≤ s := by simpa only [Function.update_self] using (hs.2 a).le
  have ht0 : 0 ≤ t := by simpa only [Function.update_self] using (ht.2 a).le
  exact strictMono_spectralConditionalMoment_principal_offset_det hn hC K ↑O f hf hE lam a hO hη
    hs0 ht0 hst

end Wishart
end
end CanonicalSource8

section CanonicalSource9
/- Source: Wishart/ShiftedPrincipalComparison.lean -/



open scoped Classical Matrix
open MeasureTheory

/-!
# Both product inequalities with every proportional nonnegative shift

The full admissible real-shape range is retained. Small remaining products use
the unrestricted offset-determinant comparison; larger original partitions
satisfy the generator threshold automatically.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

theorem shiftedSpectralAverage_nonneg
    (α : ℝ) {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) (j : Fin d) (lam : Fin (selectedRank P j) → ℝ) :
    0 ≤ shiftedSpectralAverage α Sigma P c ν J j lam :=
  Wishart.regressionSpectralAverage_compressionProduct_nonneg α
    (principalResidualScale P Sigma j) (principalCrossScale P Sigma j)
    (shiftedRemainingCompressionData Sigma P c ν J j)
    (shiftedRemainingCompressionData_offset_posSemidef hSigma P c ν hc J j) lam

theorem shiftedRemainingTest_eq_one
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (hJ : J.erase j = ∅) :
    shiftedRemainingTest Sigma P c ν J j = fun _ ↦ 1 := by
  funext T
  apply Finset.prod_eq_one
  intro i hi
  have hmem : ((i : Fin d) ∈ J.erase j) = ((i : Fin d) ∈ (∅ : Finset (Fin d))) :=
    congrArg (fun S : Finset (Fin d) ↦ (i : Fin d) ∈ S) hJ
  exact (Finset.notMem_empty _ (hmem.mp i.property)).elim

theorem shiftedRemainingTest_eq_principal_offset_det
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j i : Fin d) (hij : i ≠ j)
    (hJ : J.erase j = {i}) :
    shiftedRemainingTest Sigma P c ν J j = fun T ↦
      (c i • Sigma.submatrix
        (fun a ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
        (fun b ↦ ((Fintype.equivFin (P.block i)).symm b : Fin p)) +
        (Wishart.principalSymmetricBlock (remainingBlockCoordinates P j i hij) T :
          Matrix (Fin (Fintype.card (P.block i))) (Fin (Fintype.card (P.block i))) ℝ)).det ^ ν i := by
  funext T
  let k : J.erase j := ⟨i, by rw [hJ]; exact Finset.mem_singleton_self i⟩
  have huniq (a : J.erase j) : a = k := by
    apply Subtype.ext
    have hmem : ((a : Fin d) ∈ J.erase j) = ((a : Fin d) ∈ ({i} : Finset (Fin d))) :=
      congrArg (fun S : Finset (Fin d) ↦ (a : Fin d) ∈ S) hJ
    exact Finset.mem_singleton.mp (hmem.mp a.property)
  unfold shiftedRemainingTest compressionProduct
  rw [Finset.prod_eq_single k]
  · change (c i • Sigma.submatrix
        (fun a ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
        (fun b ↦ ((Fintype.equivFin (P.block i)).symm b : Fin p)) +
      ((1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix
        id (remainingBlockCoordinates P j i hij))ᵀ *
        (T : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
        (1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix
          id (remainingBlockCoordinates P j i hij)).det ^ ν i = _
    rw [Matrix.transpose_submatrix, Matrix.transpose_one,
      Matrix.submatrix_one_mul_mul_submatrix_one]
    rfl
  · intro a ha hne
    exact (hne (huniq a)).elim
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem shiftedSpectralAverage_monotone_of_empty
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (hJ : J.erase j = ∅) :
    MonotoneOn (shiftedSpectralAverage α Sigma P c ν J j)
      (orderedChamber (Set.Ioi 0)) := by
  unfold shiftedSpectralAverage
  rw [shiftedRemainingTest_eq_one Sigma P c ν J j hJ]
  intro lam hlam lam' hlam' hle
  rw [Wishart.regressionSpectralAverage_eq _ _ _ _ hlam,
    Wishart.regressionSpectralAverage_eq _ _ _ _ hlam']
  exact le_rfl

theorem shiftedSpectralAverage_monotone_of_single
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j i : Fin d) (hij : i ≠ j) (hJ : J.erase j = {i}) :
    MonotoneOn (shiftedSpectralAverage α Sigma P c ν J j)
      (orderedChamber (Set.Ioi 0)) := by
  unfold shiftedSpectralAverage
  rw [shiftedRemainingTest_eq_principal_offset_det Sigma P c ν J j i hij hJ]
  exact Wishart.monotoneOn_regressionSpectralAverage_principal_offset_det
    (principal_regression_shape P hα j) (principalResidualScale_posDef P hSigma j)
    (principalCrossScale P Sigma j) (remainingBlockCoordinates P j i hij)
    (remainingBlockCoordinates_injective P j i hij)
    ((hSigma.posSemidef.submatrix _).smul (hc i)) (hν i)

theorem shiftedSpectralAverage_monotone
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) :
    MonotoneOn (shiftedSpectralAverage α Sigma P c ν J j)
      (orderedChamber (Set.Ioi 0)) := by
  by_cases hd : 3 ≤ d
  · apply Wishart.monotoneOn_regressionSpectralAverage_compressionProduct
      (principal_regression_shape P hα j) (principalResidualScale_posDef P hSigma j)
      (principalCrossScale P Sigma j) (shiftedRemainingCompressionData Sigma P c ν J j)
      (shiftedRemainingCompressionData_offset_posSemidef hSigma P c ν hc J j)
      (fun i ↦ hν i)
    intro i
    exact remainingCompressionData_radial_rank_bound P hd hα ν J j i
  have hcard : (J.erase j).card ≤ 1 := by
    have h := Finset.card_le_card (Finset.erase_subset_erase j (Finset.subset_univ J))
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] at h
    omega
  by_cases hzero : (J.erase j).card = 0
  · exact shiftedSpectralAverage_monotone_of_empty α Sigma P c ν J j (Finset.card_eq_zero.mp hzero)
  · have hone : (J.erase j).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    have himem : i ∈ J.erase j := by rw [hi]; exact Finset.mem_singleton_self i
    exact shiftedSpectralAverage_monotone_of_single P hSigma hα c ν hc hν J j i
      (Finset.mem_erase.mp himem).1 hi

theorem shifted_selected_subproduct_split
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (J.erase j) ≤
      shiftedMoment α Sigma P c ν J := by
  have hnormal := Wishart.Spectral.identityEigenLaw_normalized_density
    (principal_spectral_shape P hα j)
  obtain ⟨hHi, hFi, hHFi⟩ := shifted_spectral_integrability P hSigma hα c ν hc hν J j hj
  have hassoc := lemma_2_1_association (Set.Ioi 0) measurableSet_Ioi
    (fun _ ↦ Wishart.Spectral.laguerreWeight (selectedRank P j) α) 1 (by norm_num)
    (fun _ ↦ Wishart.Spectral.measurable_laguerreWeight _ _)
    (fun _ ↦ Wishart.Spectral.laguerreWeight_nonneg _ _)
    hnormal.1 hnormal.2.1
    (shiftedSpectralDetPower (c j) (ν j)) (shiftedSpectralAverage α Sigma P c ν J j)
    (shiftedSpectralDetPower_measurable _ _) (shiftedSpectralAverage_measurable _ _ _ _ _ _ _)
    (shiftedSpectralDetPower_nonneg _ _) (shiftedSpectralAverage_nonneg α hSigma P c ν hc J j)
    ((shiftedSpectralDetPower_monotone _ _ (hν j)).monotoneOn _)
    (shiftedSpectralAverage_monotone P hSigma hα c ν hc hν J j)
  have hreal := integral_mul_le_of_lintegral_mul_le
    (Wishart.regressionEigenLaw (selectedRank P j) α) _ _
    (shiftedSpectralDetPower_nonneg _ _) (shiftedSpectralAverage_nonneg α hSigma P c ν hc J j)
    hHi hFi hHFi hassoc
  obtain ⟨hjoint, hselected, hremaining⟩ := shifted_spectral_moments P hSigma hα c ν hc hν J j hj
  rw [hselected, hremaining, hjoint, mul_assoc]
  exact mul_le_mul_of_nonneg_left hreal (principalMomentScale_pos P hSigma ν j).le

theorem shiftedMoment_empty
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (P : PrincipalPartition p d) (c ν : Fin d → ℝ) :
    shiftedMoment α Sigma P c ν ∅ = 1 := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  simp [shiftedMoment, shiftedMomentIntegrand]

/-- Section 4.1: both inequalities with arbitrary proportional nonnegative
shifts, with the original real shape and all nonnegative real powers. -/
theorem proportional_shift_product_inequalities
    (P : PrincipalPartition p d)
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) :
    (∀ J, Integrable (shiftedMomentIntegrand Sigma P c ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧
    ∀ j : Fin d,
      shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) ≤
        shiftedMoment α Sigma P c ν Finset.univ ∧
      (∏ i : Fin d, shiftedMoment α Sigma P c ν {i}) ≤
        shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) := by
  refine ⟨fun J ↦ (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν J).integrable, ?_⟩
  intro j
  refine ⟨shifted_selected_subproduct_split P hSigma hα c ν hc hν Finset.univ j (Finset.mem_univ j), ?_⟩
  have hrest := MomentAssembly.product_singletons_le (shiftedMoment α Sigma P c ν)
    (shiftedMoment_empty hSigma hα P c ν)
    (fun i ↦ (shiftedMoment_pos hSigma hα P c ν hc hν {i}).le)
    (shifted_selected_subproduct_split P hSigma hα c ν hc hν) (Finset.univ.erase j)
  calc
    (∏ i : Fin d, shiftedMoment α Sigma P c ν {i}) =
        shiftedMoment α Sigma P c ν {j} *
          ∏ i ∈ Finset.univ.erase j, shiftedMoment α Sigma P c ν {i} :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrest (shiftedMoment_pos hSigma hα P c ν hc hν {j}).le

end

end WishartVerification
end CanonicalSource9

section CanonicalSource10
/- Source: Wishart/ShiftedSpectralTests.lean -/



open scoped Classical
open MeasureTheory

/-!
# Full ordered-spectrum tests under shifted principal moments

The identities hold for every bounded Borel test of the whole selected ordered
spectrum. They identify the complete single- and full-tilted spectrum laws,
which is stronger than comparing a finite collection of determinant moments.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

def normalizedSelectedSpectrum (P : PrincipalPartition p d) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : Fin (selectedRank P j) → ℝ :=
  Wishart.Spectral.ascendingSpectrum
    (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) Y)

theorem normalizedSelectedSpectrum_measurable (P : PrincipalPartition p d) (j : Fin d) :
    Measurable (normalizedSelectedSpectrum P j) :=
  (Wishart.Spectral.continuous_ascendingSpectrum _).measurable.comp
    (Wishart.measurable_principalSymmetricBlock _)

theorem ae_shiftedMatrixDetPower_mul_spectralTest {q : ℕ} {α c : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (η : ℝ) (φ : (Fin q → ℝ) → ℝ) :
    (fun x ↦ shiftedMatrixDetPower c η (Wishart.regressionSpectralMatrix x) *
      φ (Wishart.Spectral.ascendingSpectrum (Wishart.regressionSpectralMatrix x))) =ᵐ[
        (Wishart.regressionEigenLaw q α).prod (TauCeti.haarProb (Wishart.Spectral.Orth q))]
      (fun x ↦ shiftedSpectralDetPower c η x.1 * φ x.1) := by
  filter_upwards [ae_shiftedMatrixDetPower_spectral hα hc η,
    Measure.quasiMeasurePreserving_fst.ae (Wishart.Spectral.ae_laguerreLaw_mem_chamber hα)] with x hx hch
  rw [hx, show Wishart.Spectral.ascendingSpectrum (Wishart.regressionSpectralMatrix x) = x.1 from
    Wishart.Spectral.ascendingSpectrum_conjugate_diagonal x.2 x.1 hch.1]

theorem shifted_spectral_test_integral
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (φ : (Fin (selectedRank P j) → ℝ) → ℝ) (hφm : Measurable φ)
    (hφb : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    (∫ X, shiftedMomentIntegrand Sigma P c ν J X * φ (selectedEigenvalues Sigma P j X)
      ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) =
      principalMomentScale P Sigma ν j *
        ∫ lam, (shiftedSpectralDetPower (c j) (ν j) lam *
          shiftedSpectralAverage α Sigma P c ν J j lam) * φ lam
          ∂Wishart.regressionEigenLaw (selectedRank P j) α := by
  obtain ⟨M, hM⟩ := hφb
  let h : SymmetricMatrix (selectedRank P j) → ℝ := fun S ↦
    shiftedMatrixDetPower (c j) (ν j) S * φ (Wishart.Spectral.ascendingSpectrum S)
  let k : SymmetricMatrix (selectedRank P j + remainingRank P j) → ℝ := fun Y ↦
    h (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) Y) *
      shiftedTrailingTest Sigma P c ν J j Y
  have hkm : Measurable k :=
    ((shiftedLeadingTest_measurable P c ν j).mul
      (hφm.comp (normalizedSelectedSpectrum_measurable P j))).mul
        (shiftedTrailingTest_measurable Sigma P c ν J j)
  have hji := (shifted_normalization_allFiniteMoments P hSigma hα c ν hc hν J j hj).2.2
  have hki : Integrable k (normalizedPrincipalMeasure α Sigma P j) := by
    have hb : ∀ᵐ Y ∂normalizedPrincipalMeasure α Sigma P j,
        ‖φ (normalizedSelectedSpectrum P j Y)‖ ≤ M :=
      ae_of_all _ fun Y => by
        simpa only [Real.norm_eq_abs] using hM (normalizedSelectedSpectrum P j Y)
    apply (hji.integrable.mul_bdd (c := M)
      (hφm.comp (normalizedSelectedSpectrum_measurable P j)).aestronglyMeasurable hb).congr
    exact ae_of_all _ fun Y ↦ by dsimp [k, h, shiftedJointTest, shiftedLeadingTest, normalizedSelectedSpectrum]; ring
  have hnorm := integral_eq_scaled_of_pullback
    (normalizedPrincipalMatrix_measurePreserving P hSigma hα j)
    (fun X ↦ shiftedMomentIntegrand Sigma P c ν J X * φ (selectedEigenvalues Sigma P j X))
    k (principalMomentScale P Sigma ν j) hkm
    ((TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma).mono fun X hX ↦ by
      dsimp only
      rw [shiftedJointIntegrand_eq_scaled_normalized P hSigma c ν hc J j hj X hX]
      dsimp [k, h, shiftedJointTest, shiftedLeadingTest, selectedEigenvalues]
      ring)
  have hspec := Wishart.integral_regression_joint_spectralTest
    (h := h) (H := fun lam ↦ shiftedSpectralDetPower (c j) (ν j) lam * φ lam)
    (principal_regression_shape P hα j) (principalCrossScale P Sigma j)
    (principalResidualScale_posDef P hSigma j)
    (shiftedRemainingTest_measurable Sigma P c ν J j)
    (by
      simpa only [h] using
        (ae_shiftedMatrixDetPower_mul_spectralTest
          (principal_spectral_shape P hα j) (hc j) (ν j) φ)) hki
  rw [hnorm]
  dsimp only [k, shiftedTrailingTest, normalizedPrincipalMeasure]
  rw [hspec]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun lam ↦ by
    dsimp only [shiftedSpectralAverage]
    ring

theorem shifted_selected_spectral_test_integral
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (j : Fin d)
    (φ : (Fin (selectedRank P j) → ℝ) → ℝ) (hφm : Measurable φ) :
    (∫ X, shiftedMomentIntegrand Sigma P c ν {j} X * φ (selectedEigenvalues Sigma P j X)
      ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) =
      principalMomentScale P Sigma ν j *
        ∫ lam, shiftedSpectralDetPower (c j) (ν j) lam * φ lam
          ∂Wishart.regressionEigenLaw (selectedRank P j) α := by
  let h : SymmetricMatrix (selectedRank P j) → ℝ := fun S ↦
    shiftedMatrixDetPower (c j) (ν j) S * φ (Wishart.Spectral.ascendingSpectrum S)
  have hhm : Measurable h := (shiftedMatrixDetPower_measurable _ _).mul
    (hφm.comp (Wishart.Spectral.continuous_ascendingSpectrum _).measurable)
  have hnorm := integral_eq_scaled_of_pullback
    (normalizedPrincipalMatrix_measurePreserving P hSigma hα j)
    (fun X ↦ shiftedMomentIntegrand Sigma P c ν {j} X * φ (selectedEigenvalues Sigma P j X))
    (fun Y ↦ h (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) Y))
    (principalMomentScale P Sigma ν j)
    (hhm.comp (Wishart.measurable_principalSymmetricBlock _))
    ((TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma).mono fun X hX ↦ by
      simp only [shiftedMomentIntegrand, Finset.prod_singleton]
      rw [shiftedFactor_eq_scaled_leading P hSigma c ν hc j X hX]
      dsimp [h, shiftedLeadingTest, selectedEigenvalues]
      ring)
  rw [hnorm]
  congr 1
  exact Wishart.integral_regression_selected_spectralTest (principal_regression_shape P hα j)
    (principalCrossScale P Sigma j) (principalResidualScale_posDef P hSigma j) hhm
    (ae_shiftedMatrixDetPower_mul_spectralTest (principal_spectral_shape P hα j) (hc j) (ν j) φ)

theorem integral_shiftedSpectralProduct_pos
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    0 < ∫ lam, shiftedSpectralDetPower (c j) (ν j) lam *
      shiftedSpectralAverage α Sigma P c ν J j lam
      ∂Wishart.regressionEigenLaw (selectedRank P j) α := by
  have hpos := shiftedMoment_pos hSigma hα P c ν hc hν J
  rw [(shifted_spectral_moments P hSigma hα c ν hc hν J j hj).1] at hpos
  exact (mul_pos_iff_of_pos_left (principalMomentScale_pos P hSigma ν j)).mp hpos

theorem map_selectedEigenvalues_single_shifted_tilt
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) (j : Fin d) :
    (shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j) =
      normalizedWeight (Wishart.regressionEigenLaw (selectedRank P j) α)
        (shiftedSpectralDetPower (c j) (ν j)) := by
  letI := shiftedTiltLaw_probability hSigma hα P c ν hc hν {j}
  have hHi := (allFiniteMoments_shiftedSpectralDetPower
    (principal_spectral_shape P hα j) (hc j) (hν j)).integrable
  have hHpos := integral_shiftedSpectralDetPower_pos (principal_spectral_shape P hα j) (hc j) (hν j)
  letI := normalizedWeight_probability_of_integrable_pos _ _ (shiftedSpectralDetPower_nonneg _ _) hHi hHpos
  apply measure_eq_of_bounded_measurable_integrals
  intro φ hφm hφb
  rw [integral_map_of_stronglyMeasurable (selectedEigenvalues_measurable Sigma P j) hφm.stronglyMeasurable]
  change (∫ X, φ (selectedEigenvalues Sigma P j X)
      ∂normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α Sigma)
        (shiftedMomentIntegrand Sigma P c ν {j})) = _
  have hden := (shifted_spectral_moments P hSigma hα c ν hc hν {j} j (by simp)).2.1
  unfold shiftedMoment at hden
  rw [normalizedWeight_integral_ae _ _ _ (shiftedMomentIntegrand_measurable Sigma P c ν {j})
    ((ae_shiftedMomentIntegrand_pos α hSigma P c ν hc {j}).mono fun _ hx ↦ hx.le)
    (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν {j}).integrable,
    shifted_selected_spectral_test_integral P hSigma hα c ν hc j φ hφm,
    hden,
    mul_div_mul_left _ _ (principalMomentScale_pos P hSigma ν j).ne',
    normalizedWeight_integral _ _ _ (shiftedSpectralDetPower_measurable _ _)
      (shiftedSpectralDetPower_nonneg _ _) hHi]

theorem map_selectedEigenvalues_shifted_tilt
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    (shiftedTiltLaw α Sigma P c ν J).map (selectedEigenvalues Sigma P j) =
      normalizedWeight (Wishart.regressionEigenLaw (selectedRank P j) α)
        (fun lam ↦ shiftedSpectralDetPower (c j) (ν j) lam *
          shiftedSpectralAverage α Sigma P c ν J j lam) := by
  letI := shiftedTiltLaw_probability hSigma hα P c ν hc hν J
  have hHFm : Measurable (fun lam => shiftedSpectralDetPower (c j) (ν j) lam *
      shiftedSpectralAverage α Sigma P c ν J j lam) :=
    (shiftedSpectralDetPower_measurable (ι := Fin (selectedRank P j)) (c j) (ν j)).mul
      (shiftedSpectralAverage_measurable α Sigma P c ν J j)
  have hHF0 (lam) := mul_nonneg (shiftedSpectralDetPower_nonneg (c j) (ν j) lam)
    (shiftedSpectralAverage_nonneg α hSigma P c ν hc J j lam)
  have hHFi := (shifted_spectral_integrability P hSigma hα c ν hc hν J j hj).2.2
  have hHFpos := integral_shiftedSpectralProduct_pos P hSigma hα c ν hc hν J j hj
  letI := normalizedWeight_probability_of_integrable_pos _ _ hHF0 hHFi hHFpos
  apply measure_eq_of_bounded_measurable_integrals
  intro φ hφm hφb
  rw [integral_map_of_stronglyMeasurable (selectedEigenvalues_measurable Sigma P j) hφm.stronglyMeasurable]
  change (∫ X, φ (selectedEigenvalues Sigma P j X)
      ∂normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α Sigma)
        (shiftedMomentIntegrand Sigma P c ν J)) = _
  have hden := (shifted_spectral_moments P hSigma hα c ν hc hν J j hj).1
  unfold shiftedMoment at hden
  rw [normalizedWeight_integral_ae _ _ _ (shiftedMomentIntegrand_measurable Sigma P c ν J)
    ((ae_shiftedMomentIntegrand_pos α hSigma P c ν hc J).mono fun _ hx ↦ hx.le)
    (allFiniteMoments_shiftedMomentIntegrand hSigma hα P c ν hν J).integrable,
    shifted_spectral_test_integral P hSigma hα c ν hc hν J j hj φ hφm hφb,
    hden,
    mul_div_mul_left _ _ (principalMomentScale_pos P hSigma ν j).ne',
    normalizedWeight_integral _ _ _ hHFm hHF0 hHFi]

end

end WishartVerification
end CanonicalSource10

section CanonicalSource11
/- Source: Wishart/ShiftedTiltDomination.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Proposition 4.1: domination of the entire ordered selected spectrum

The measures in the final statement are the pushforwards of the actual
Wishart law tilted by the specified determinant products. The single tilt is
identified with the separately tilted Laguerre weights, and the full tilt is
its increasing conditional-moment tilt. Signed bounded increasing tests are
covered, so the conclusion is the stated stochastic domination.
-/

namespace WishartVerification

noncomputable section

def shiftedEigenTilt (q : ℕ) (α c η : ℝ) : Measure (Fin q → ℝ) :=
  normalizedWeight (Wishart.regressionEigenLaw q α) (shiftedSpectralDetPower c η)

theorem shiftedEigenTilt_probability {q : ℕ} {α c η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (hη : 0 ≤ η) :
    IsProbabilityMeasure (shiftedEigenTilt q α c η) :=
  normalizedWeight_probability_of_integrable_pos _ _ (shiftedSpectralDetPower_nonneg _ _)
    (allFiniteMoments_shiftedSpectralDetPower hα hc hη).integrable
    (integral_shiftedSpectralDetPower_pos hα hc hη)

/-- The actual single-factor tilt retains association because each original
Laguerre weight is multiplied by `(max (t+c) 0)^η`. -/
theorem shiftedEigenTilt_association {q : ℕ} {α c η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hc : 0 ≤ c) (hη : 0 ≤ η)
    (f g : (Fin q → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmono : MonotoneOn f (orderedChamber (Set.Ioi 0)))
    (hgmono : MonotoneOn g (orderedChamber (Set.Ioi 0))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂shiftedEigenTilt q α c η) *
      (∫⁻ x, ENNReal.ofReal (g x) ∂shiftedEigenTilt q α c η) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂shiftedEigenTilt q α c η := by
  exact separateWeight_tilt_association (Set.Ioi 0) measurableSet_Ioi
    (fun _ ↦ Wishart.Spectral.laguerreWeight q α)
    (fun _ t ↦ max (t + c) 0 ^ η) 1 (by norm_num)
    (fun _ ↦ Wishart.Spectral.measurable_laguerreWeight q α)
    (fun _ ↦ ((measurable_id.add_const c).max measurable_const).pow_const η)
    (fun _ ↦ Wishart.Spectral.laguerreWeight_nonneg q α)
    (fun _ _ ↦ Real.rpow_nonneg (le_max_right _ _) _)
    (allFiniteMoments_shiftedSpectralDetPower hα hc hη).integrable
    (integral_shiftedSpectralDetPower_pos hα hc hη)
    f g hfm hgm hf0 hg0 hfmono hgmono

variable {p d : ℕ}

theorem shiftedSpectralAverage_integrable_singleTilt
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    Integrable (shiftedSpectralAverage α Sigma P c ν J j)
      (shiftedEigenTilt (selectedRank P j) α (c j) (ν j)) := by
  obtain ⟨hHi, _, hHFi⟩ := shifted_spectral_integrability P hSigma hα c ν hc hν J j hj
  have hHpos := integral_shiftedSpectralDetPower_pos (principal_spectral_shape P hα j) (hc j) (hν j)
  have hZ0 : (∫⁻ lam, ENNReal.ofReal (shiftedSpectralDetPower (c j) (ν j) lam)
      ∂Wishart.regressionEigenLaw (selectedRank P j) α) ≠ 0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hHi
      (ae_of_all _ (shiftedSpectralDetPower_nonneg _ _))]
    exact (ENNReal.ofReal_pos.mpr hHpos).ne'
  exact integrable_normalizedWeight _ _ _ (shiftedSpectralDetPower_measurable _ _)
    (shiftedSpectralDetPower_nonneg _ _) hZ0 hHFi

theorem integral_shiftedSpectralAverage_singleTilt_pos
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    0 < ∫ lam, shiftedSpectralAverage α Sigma P c ν J j lam
      ∂shiftedEigenTilt (selectedRank P j) α (c j) (ν j) := by
  unfold shiftedEigenTilt
  rw [normalizedWeight_integral _ _ _ (shiftedSpectralDetPower_measurable _ _)
    (shiftedSpectralDetPower_nonneg _ _)
    (allFiniteMoments_shiftedSpectralDetPower
      (principal_spectral_shape P hα j) (hc j) (hν j)).integrable]
  exact div_pos (integral_shiftedSpectralProduct_pos P hSigma hα c ν hc hν J j hj)
    (integral_shiftedSpectralDetPower_pos (principal_spectral_shape P hα j) (hc j) (hν j))

theorem shifted_tilt_spectral_domination
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    IncreasingExpectationLE (orderedChamber (Set.Ioi 0))
      ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j))
      ((shiftedTiltLaw α Sigma P c ν J).map (selectedEigenvalues Sigma P j)) := by
  letI := shiftedEigenTilt_probability (principal_spectral_shape P hα j) (hc j) (hν j)
  have hFi := shiftedSpectralAverage_integrable_singleTilt P hSigma hα c ν hc hν J j hj
  have hFpos := integral_shiftedSpectralAverage_singleTilt_pos P hSigma hα c ν hc hν J j hj
  have hF0 := shiftedSpectralAverage_nonneg α hSigma P c ν hc J j
  have hFm := shiftedSpectralAverage_measurable α Sigma P c ν J j
  letI : IsProbabilityMeasure
      (normalizedWeight
        (normalizedWeight (Wishart.regressionEigenLaw (selectedRank P j) α)
          (shiftedSpectralDetPower (c j) (ν j)))
        (shiftedSpectralAverage α Sigma P c ν J j)) := by
    simpa only [shiftedEigenTilt] using
      normalizedWeight_probability_of_integrable_pos
        (shiftedEigenTilt (selectedRank P j) α (c j) (ν j))
        (shiftedSpectralAverage α Sigma P c ν J j) hF0 hFi hFpos
  have hdom := increasingExpectationLE_normalizedWeight_of_association
    (shiftedEigenTilt (selectedRank P j) α (c j) (ν j)) (orderedChamber (Set.Ioi 0))
    (shiftedEigenTilt_association (principal_spectral_shape P hα j) (hc j) (hν j))
    (shiftedSpectralAverage α Sigma P c ν J j) hFm hF0
    (shiftedSpectralAverage_monotone P hSigma hα c ν hc hν J j) hFi hFpos
  have hiterate := normalizedWeight_iterate
    (Wishart.regressionEigenLaw (selectedRank P j) α)
    (shiftedSpectralDetPower (c j) (ν j)) (shiftedSpectralAverage α Sigma P c ν J j)
    (shiftedSpectralDetPower_measurable _ _) hFm (shiftedSpectralDetPower_nonneg _ _)
  rw [map_selectedEigenvalues_single_shifted_tilt P hSigma hα c ν hc hν j,
    map_selectedEigenvalues_shifted_tilt P hSigma hα c ν hc hν J j hj, ← hiterate]
  exact hdom

/-- Proposition 4.1's full stochastic-domination assertion, using the literal
full determinant-product tilt and literal single-factor tilt of the original
Wishart law. -/
theorem proposition_4_1_stochastic_domination
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) (j : Fin d) :
    IncreasingExpectationLE (orderedChamber (Set.Ioi 0))
      ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j))
      ((shiftedTiltLaw α Sigma P c ν Finset.univ).map (selectedEigenvalues Sigma P j)) :=
  shifted_tilt_spectral_domination P hSigma hα c ν hc hν Finset.univ j (Finset.mem_univ j)

end

end WishartVerification
end CanonicalSource11

section CanonicalSource12
/- Source: Wishart/CoordinateMonotonicity.lean -/



open scoped Classical

/-!
# From one-coordinate comparison to componentwise comparison

Intermediate points are mixed coordinate vectors in the full product domain.
For the Wishart application this is the positive orthant, so intermediate
eigenvalues need not remain ordered or distinct. The final monotonicity statement
is then restricted to the ordered chamber.
-/

namespace WishartVerification

theorem monotoneOn_of_monotone_updates
    {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Preorder (β i)]
    {γ : Type*} [Preorder γ] (allowed : ∀ i, Set (β i)) (F : (∀ i, β i) → γ)
    (hstep : ∀ x, (∀ i, x i ∈ allowed i) → ∀ i t,
      t ∈ allowed i → x i ≤ t → F x ≤ F (Function.update x i t)) :
    MonotoneOn F {x | ∀ i, x i ∈ allowed i} := by
  intro x hx y hy hxy
  have hmem (A : Finset ι) (i : ι) : A.piecewise y x i ∈ allowed i := by
    by_cases hi : i ∈ A
    · simpa only [Finset.piecewise_eq_of_mem A y x hi] using hy i
    · simpa only [Finset.piecewise_eq_of_notMem A y x hi] using hx i
  have hpartial (A : Finset ι) : F x ≤ F (A.piecewise y x) := by
    induction A using Finset.induction_on with
    | empty => simpa only [Finset.piecewise_empty] using (le_refl (F x))
    | @insert i A hi ih =>
        rw [Finset.piecewise_insert]
        apply ih.trans
        apply hstep _ (hmem A) i (y i) (hy i)
        simpa only [Finset.piecewise_eq_of_notMem A y x hi] using hxy i
  simpa only [Finset.piecewise_univ] using hpartial Finset.univ

/-- A rowwise mean-square comparison on every positive coordinate vector gives
the componentwise increasing spectral test required by Lemma 2.1. -/
theorem monotoneOn_positive_chamber_of_monotone_updates
    {ι : Type*} [Fintype ι] [LinearOrder ι] (F : (ι → ℝ) → ℝ)
    (hstep : ∀ x, (∀ i, 0 < x i) → ∀ i t,
      0 < t → x i ≤ t → F x ≤ F (Function.update x i t)) :
    MonotoneOn F (orderedChamber (Set.Ioi 0)) := by
  have hmono := monotoneOn_of_monotone_updates (fun _ : ι ↦ Set.Ioi (0 : ℝ)) F hstep
  intro x hx y hy hxy
  exact hmono hx.2 hy.2 hxy

end WishartVerification
end CanonicalSource12

section CanonicalSource13
/- Source: Wishart/ExponentMonotonicity.lean -/



open scoped Classical
open MeasureTheory

/-!
# Proposition 4.1: monotonicity in every nonnegative exponent

The selected exponent changes only its one-coordinate product weight. The
conditional moment of the other factors is unchanged. Association under the
actual single-factor tilt yields the cross-moment inequality, and positive
finite normalizers allow cancellation in the ratio. No boundedness restriction
is imposed on determinant powers.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

theorem update_exponent_nonneg (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (j : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, 0 ≤ Function.update ν j (ν j + t) i := by
  intro i
  by_cases hij : i = j
  · subst i
    simpa only [Function.update_self] using add_nonneg (hν j) ht
  · rw [Function.update_of_ne hij]
    exact hν i

theorem exponent_update_eq_add_single (ν : Fin d → ℝ) (j : Fin d) (t : ℝ) :
    Function.update ν j (ν j + t) = ν + Pi.single j t := by
  funext i
  by_cases hij : i = j <;> simp [hij, Function.update_of_ne]

theorem shiftedRemainingTest_update_selected
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (η : ℝ) :
    shiftedRemainingTest Sigma P c (Function.update ν j η) J j =
      shiftedRemainingTest Sigma P c ν J j := by
  funext T
  unfold shiftedRemainingTest compressionProduct
  apply Finset.prod_congr rfl
  intro i hi
  simp only [shiftedRemainingCompressionData, remainingCompressionData,
    Function.update_of_ne (Finset.mem_erase.mp i.property).1]
  rfl

theorem shiftedSpectralAverage_update_selected
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (η : ℝ) :
    shiftedSpectralAverage α Sigma P c (Function.update ν j η) J j =
      shiftedSpectralAverage α Sigma P c ν J j := by
  unfold shiftedSpectralAverage
  rw [shiftedRemainingTest_update_selected]

theorem shiftedMoment_singleton_update_of_ne
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (j i : Fin d) (hij : i ≠ j) (η : ℝ) :
    shiftedMoment α Sigma P c (Function.update ν j η) {i} =
      shiftedMoment α Sigma P c ν {i} := by
  unfold shiftedMoment
  apply integral_congr_ae
  exact ae_of_all _ fun X ↦ by
    simp only [shiftedMomentIntegrand, Finset.prod_singleton, Function.update_of_ne hij]

theorem shiftedMoment_other_product_update
    (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (P : PrincipalPartition p d)
    (c ν : Fin d → ℝ) (j : Fin d) (η : ℝ) :
    (∏ i ∈ Finset.univ.erase j, shiftedMoment α Sigma P c (Function.update ν j η) {i}) =
      ∏ i ∈ Finset.univ.erase j, shiftedMoment α Sigma P c ν {i} := by
  apply Finset.prod_congr rfl
  intro i hi
  exact shiftedMoment_singleton_update_of_ne α Sigma P c ν j i (Finset.mem_erase.mp hi).1 η

theorem shiftedMomentRatio_eq_spectral_quotient
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) (j : Fin d) :
    shiftedMomentRatio α Sigma P c ν =
      (∫ lam, shiftedSpectralDetPower (c j) (ν j) lam *
        shiftedSpectralAverage α Sigma P c ν Finset.univ j lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) /
      ((∫ lam, shiftedSpectralDetPower (c j) (ν j) lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) *
          ∏ i ∈ Finset.univ.erase j, shiftedMoment α Sigma P c ν {i}) := by
  obtain ⟨hjoint, hselected, _⟩ := shifted_spectral_moments P hSigma hα c ν hc hν
    Finset.univ j (Finset.mem_univ j)
  unfold shiftedMomentRatio
  rw [hjoint, ← Finset.mul_prod_erase Finset.univ
    (fun i ↦ shiftedMoment α Sigma P c ν {i}) (Finset.mem_univ j), hselected, mul_assoc,
    mul_div_mul_left _ _ (principalMomentScale_pos P hSigma ν j).ne']

theorem shiftedMomentRatio_increase_exponent
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (j : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    shiftedMomentRatio α Sigma P c ν ≤
      shiftedMomentRatio α Sigma P c (Function.update ν j (ν j + t)) := by
  let η := Function.update ν j (ν j + t)
  have hη := update_exponent_nonneg ν hν j ht
  let μ := Wishart.regressionEigenLaw (selectedRank P j) α
  let H := shiftedSpectralDetPower (ι := Fin (selectedRank P j)) (c j) (ν j)
  let T := shiftedSpectralDetPower (ι := Fin (selectedRank P j)) (c j) t
  let H' := shiftedSpectralDetPower (ι := Fin (selectedRank P j)) (c j) (ν j + t)
  let F := shiftedSpectralAverage α Sigma P c ν Finset.univ j
  have hn := principal_spectral_shape P hα j
  have hch := Wishart.Spectral.ae_laguerreLaw_mem_chamber hn
  have heq : (fun lam ↦ H lam * T lam) =ᵐ[μ] H' := hch.mono fun lam hlam ↦
    (shiftedSpectralDetPower_add_exponent (hc j) (ν j) t lam hlam.2).symm
  have hH'i : Integrable H' μ :=
    (allFiniteMoments_shiftedSpectralDetPower hn (hc j) (add_nonneg (hν j) ht)).integrable
  have hH'Fi : Integrable (fun lam ↦ H' lam * F lam) μ := by
    have h := (shifted_spectral_integrability P hSigma hα c η hc hη
      Finset.univ j (Finset.mem_univ j)).2.2
    simpa only [η, Function.update_self, shiftedSpectralAverage_update_selected, H', F, μ] using h
  have hHTi : Integrable (fun lam ↦ H lam * T lam) μ := hH'i.congr heq.symm
  have hHTFi : Integrable (fun lam ↦ H lam * (T lam * F lam)) μ := by
    apply hH'Fi.congr
    filter_upwards [heq] with lam hlam
    rw [← hlam, mul_assoc]
  have hHi : Integrable H μ := (allFiniteMoments_shiftedSpectralDetPower hn (hc j) (hν j)).integrable
  have hHpos : 0 < ∫ lam, H lam ∂μ := integral_shiftedSpectralDetPower_pos hn (hc j) (hν j)
  have hH'pos : 0 < ∫ lam, H' lam ∂μ :=
    integral_shiftedSpectralDetPower_pos hn (hc j) (add_nonneg (hν j) ht)
  have hHFi : Integrable (fun lam ↦ H lam * F lam) μ :=
    (shifted_spectral_integrability P hSigma hα c ν hc hν Finset.univ j (Finset.mem_univ j)).2.2
  have hassoc := shiftedEigenTilt_association hn (hc j) (hν j) T F
    (shiftedSpectralDetPower_measurable _ _) (shiftedSpectralAverage_measurable _ _ _ _ _ _ _)
    (shiftedSpectralDetPower_nonneg _ _) (shiftedSpectralAverage_nonneg α hSigma P c ν hc Finset.univ j)
    ((shiftedSpectralDetPower_monotone _ _ ht).monotoneOn _)
    (shiftedSpectralAverage_monotone P hSigma hα c ν hc hν Finset.univ j)
  have hcross := weighted_integral_association μ H T F (shiftedSpectralDetPower_measurable _ _)
    (shiftedSpectralDetPower_nonneg _ _) (shiftedSpectralDetPower_nonneg _ _)
    (shiftedSpectralAverage_nonneg α hSigma P c ν hc Finset.univ j)
    hHi hHpos hHTi hHFi hHTFi hassoc
  have heqF : (fun lam ↦ H lam * (T lam * F lam)) =ᵐ[μ]
      (fun lam ↦ H' lam * F lam) := heq.mono fun lam hlam ↦ by
        change H lam * (T lam * F lam) = H' lam * F lam
        change H lam * T lam = H' lam at hlam
        rw [← hlam, mul_assoc]
  rw [integral_congr_ae heq, integral_congr_ae heqF] at hcross
  have hother : 0 < ∏ i ∈ Finset.univ.erase j, shiftedMoment α Sigma P c ν {i} :=
    Finset.prod_pos fun i _ ↦ shiftedMoment_pos hSigma hα P c ν hc hν {i}
  rw [shiftedMomentRatio_eq_spectral_quotient P hSigma hα c ν hc hν j,
    shiftedMomentRatio_eq_spectral_quotient P hSigma hα c η hc hη j,
    shiftedSpectralAverage_update_selected, shiftedMoment_other_product_update]
  simp only [η, Function.update_self]
  apply (div_le_div_iff₀ (mul_pos hHpos hother) (mul_pos hH'pos hother)).mpr
  convert mul_le_mul_of_nonneg_right hcross hother.le using 1 <;> ring

/-- Coordinatewise monotonicity on the full closed nonnegative exponent
orthant, including zero exponents. -/
theorem proposition_4_1_exponent_monotonicity
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) :
    MonotoneOn (shiftedMomentRatio α Sigma P c) (Set.Ici (0 : Fin d → ℝ)) := by
  have hmono := monotoneOn_of_monotone_updates (fun _ : Fin d ↦ Set.Ici (0 : ℝ))
    (shiftedMomentRatio α Sigma P c) (fun ν hν j t ht hνt ↦ by
      have h := shiftedMomentRatio_increase_exponent P hSigma hα c ν hc hν j
        (t - ν j) (sub_nonneg.mpr hνt)
      have heq : ν j + (t - ν j) = t := by ring
      rwa [heq] at h)
  exact hmono

/-- Proposition 4.1 in full: the normalized determinant-product ratio is
increasing in every exponent, and the full determinant tilt stochastically
dominates the single-factor tilt on the entire ordered selected spectrum. -/
theorem proposition_4_1
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (c : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) :
    MonotoneOn (shiftedMomentRatio α Sigma P c) (Set.Ici (0 : Fin d → ℝ)) ∧
    ∀ (ν : Fin d → ℝ), (∀ i, 0 ≤ ν i) → ∀ j : Fin d,
      IncreasingExpectationLE (orderedChamber (Set.Ioi 0))
        ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j))
        ((shiftedTiltLaw α Sigma P c ν Finset.univ).map (selectedEigenvalues Sigma P j)) :=
  ⟨proposition_4_1_exponent_monotonicity P hSigma hα c hc,
    fun ν hν j ↦ proposition_4_1_stochastic_domination P hSigma hα c ν hc hν j⟩

end

end WishartVerification
end CanonicalSource13
