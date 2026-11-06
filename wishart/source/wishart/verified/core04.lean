module

public import wishart.verified.core03
public import tau_ceti.probability.distributions.gaussian.density
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.LHopital

/- Generated ordinary proof stage. See audit/staged_core/Core04/manifest.json. -/

@[expose] public section

section CanonicalSource75
/- Source: Wishart/VandermondeSupport.lean -/



open scoped Classical ENNReal
open MeasureTheory

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem orderedVandermonde_pos (β : ℝ) (x : ι → ℝ) (hx : StrictMono x) :
    0 < orderedVandermonde β x := by
  unfold orderedVandermonde
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  by_cases hij : i < j
  · simp only [hij, ite_true, max_eq_left (sub_nonneg.mpr (hx hij).le)]
    exact Real.rpow_pos_of_pos (sub_pos.mpr (hx hij)) β
  · simp [hij]

theorem vandermondeWeight_pos_iff (w : ι → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hw0 : ∀ i t, 0 ≤ w i t) (x : ι → ℝ) :
    0 < vandermondeWeight w β x ↔ StrictMono x ∧ ∀ i, 0 < w i (x i) := by
  constructor
  · intro hx
    constructor
    · by_contra hmono
      have hz : vandermondeWeight w β x = 0 := by
        unfold vandermondeWeight
        rw [orderedVandermonde_eq_zero_off_chamber β hβ x hmono, mul_zero]
      exact hx.ne' hz
    · intro i
      apply lt_of_le_of_ne (hw0 i _)
      intro hi
      have hp : (∏ j, w j (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi.symm
      have hz : vandermondeWeight w β x = 0 := by simp only [vandermondeWeight, hp, zero_mul]
      exact hx.ne' hz
  · rintro ⟨hx, hw⟩
    exact mul_pos (Finset.prod_pos fun i _ ↦ hw i) (orderedVandermonde_pos β x hx)

section LastCoordinate

variable {n : ℕ}

theorem appendLast_strictMono_of_le (x : Fin n → ℝ) (s t : ℝ)
    (hx : StrictMono (appendLast x s)) (hst : s ≤ t) : StrictMono (appendLast x t) := by
  intro i j hij
  cases j using Fin.lastCases with
  | last =>
      cases i using Fin.lastCases with
      | last => exact False.elim ((lt_irrefl _) hij)
      | cast i =>
          have hi := hx (Fin.castSucc_lt_last i)
          simp only [appendLast_castSucc, appendLast_last] at hi ⊢
          exact hi.trans_le hst
  | cast j =>
      cases i using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last j.castSucc)) hij)
      | cast i =>
          simpa only [appendLast_castSucc] using hx hij

theorem vandermondeWeight_appendLast_eq_zero_of_last
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (ht : w (Fin.last n) t = 0) : vandermondeWeight w β (appendLast x t) = 0 := by
  unfold vandermondeWeight
  have hp : (∏ i, w i (appendLast x t i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) (by simpa using ht)
  rw [hp, zero_mul]

/-- Any slice of positive mass has a positive last-coordinate weight. -/
theorem last_weight_pos_of_sliceNorm_pos
    (μ : Measure (Fin n → ℝ)) (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ)
    (hw0 : ∀ i t, 0 ≤ w i t) (t : ℝ)
    (hZ : 0 < ∫ x, vandermondeWeight w β (appendLast x t) ∂μ) :
    0 < w (Fin.last n) t := by
  apply lt_of_le_of_ne (hw0 _ _)
  intro ht
  have hzero (x : Fin n → ℝ) := vandermondeWeight_appendLast_eq_zero_of_last w β x t ht.symm
  simp_rw [hzero] at hZ
  simpa using hZ

/-- The positive supports of successive admissible slices are nested. -/
theorem vandermonde_slice_support_nested
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hw0 : ∀ i t, 0 ≤ w i t) (s t : ℝ) (hst : s ≤ t)
    (ht : 0 < w (Fin.last n) t) (x : Fin n → ℝ)
    (hx : 0 < vandermondeWeight w β (appendLast x s)) :
    0 < vandermondeWeight w β (appendLast x t) := by
  obtain ⟨hxmono, hxw⟩ := (vandermondeWeight_pos_iff w β hβ hw0 _).mp hx
  apply (vandermondeWeight_pos_iff w β hβ hw0 _).mpr
  refine ⟨appendLast_strictMono_of_le x s t hxmono hst, ?_⟩
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [appendLast_last] using ht
  | cast i => simpa only [appendLast_castSucc] using hxw i.castSucc

end LastCoordinate

end WishartVerification
end CanonicalSource75

section CanonicalSource76
/- Source: Wishart/SliceAssociation.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Strict association through the last coordinate

Every stochastic comparison below is proved from the explicit lattice
approximations. The a.e. good-fiber set retains all exceptional conditional
normalizers; no pointwise disintegration regularity is assumed.
-/

namespace WishartVerification

variable {n : ℕ}

def splitLastFun (f : (Fin (n + 1) → ℝ) → ℝ) : (Fin n → ℝ) × ℝ → ℝ :=
  fun p ↦ f (appendLast p.1 p.2)

theorem splitLastFun_measurable (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (splitLastFun f) := hf.comp snoc_uncurry_measurable

def StrictLastOnSupport (W f : (Fin (n + 1) → ℝ) → ℝ) : Prop :=
  ∀ x s t, s < t → 0 < W (appendLast x s) → 0 < W (appendLast x t) →
    f (appendLast x s) < f (appendLast x t)

theorem supportedMonotone_slice (W f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : SupportedMonotone W f) (t : ℝ) :
    SupportedMonotone (fun x ↦ W (appendLast x t)) (fun x ↦ f (appendLast x t)) :=
  fun x y hx hy hxy ↦ hf _ _ hx hy (appendLast_le hxy le_rfl)

theorem slice_lintegral_ofReal_ne_zero_top
    (μ : Measure (Fin n → ℝ)) (W : (Fin (n + 1) → ℝ) → ℝ)
    (hW0 : ∀ x, 0 ≤ W x) (t : ℝ)
    (hWt : Integrable (fun x ↦ W (appendLast x t)) μ)
    (hZpos : 0 < sliceNorm μ (splitLastFun W) t) :
    (∫⁻ x, ENNReal.ofReal (W (appendLast x t)) ∂μ) ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (W (appendLast x t)) ∂μ) ≠ ∞ := by
  have heq : (∫⁻ x, ENNReal.ofReal (W (appendLast x t)) ∂μ) =
      ENNReal.ofReal (sliceNorm μ (splitLastFun W) t) :=
    (ofReal_integral_eq_lintegral_ofReal hWt
      (ae_of_all _ fun x ↦ hW0 (appendLast x t))).symm
  rw [heq]
  exact ⟨(ENNReal.ofReal_pos.mpr hZpos).ne', ENNReal.ofReal_ne_top⟩

namespace MTP2Approximation

variable {W : (Fin (n + 1) → ℝ) → ℝ} (H : MTP2Approximation W)

include H

theorem sliceMean_association
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hWm : Measurable W) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone W f) (hgi : SupportedMonotone W g)
    (t : ℝ) (hWt : Integrable (fun x ↦ W (appendLast x t)) (Measure.pi μ))
    (hWft : Integrable (fun x ↦ W (appendLast x t) * f (appendLast x t)) (Measure.pi μ))
    (hWgt : Integrable (fun x ↦ W (appendLast x t) * g (appendLast x t)) (Measure.pi μ))
    (hWfgt : Integrable (fun x ↦ W (appendLast x t) *
      (f (appendLast x t) * g (appendLast x t))) (Measure.pi μ))
    (hZpos : 0 < sliceNorm (Measure.pi μ) (splitLastFun W) t) :
    sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun f) t *
        sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun g) t ≤
      sliceMean (Measure.pi μ) (splitLastFun W) (fun p ↦ splitLastFun f p * splitLastFun g p) t := by
  obtain ⟨hZ0, hZtop⟩ := slice_lintegral_ofReal_ne_zero_top
    (Measure.pi μ) W H.limit_nonneg t hWt hZpos
  have hwm : Measurable (fun x : Fin n → ℝ ↦ W (appendLast x t)) :=
    hWm.comp (snoc_measurable t)
  have hftm : Measurable (fun x : Fin n → ℝ ↦ f (appendLast x t)) :=
    hfm.comp (snoc_measurable t)
  have hgtm : Measurable (fun x : Fin n → ℝ ↦ g (appendLast x t)) :=
    hgm.comp (snoc_measurable t)
  have hext := normalizedWeight_association (Measure.pi μ)
    (fun x ↦ W (appendLast x t)) (fun x ↦ f (appendLast x t))
    (fun x ↦ g (appendLast x t)) hwm hftm hgtm
    (fun x ↦ H.limit_nonneg _) (fun x ↦ hg0 _) hZ0 hZtop
    ((H.slice t).association_lintegral_on μ _ _ hftm hgtm
      (fun x ↦ hf0 _) (fun x ↦ hg0 _)
      (supportedMonotone_slice W f hfi t) (supportedMonotone_slice W g hgi t))
  have hreal := integral_mul_le_of_lintegral_mul_le _ _ _
    (fun x ↦ hf0 (appendLast x t)) (fun x ↦ hg0 (appendLast x t))
    (integrable_normalizedWeight (Measure.pi μ) _ _ hwm
      (fun x ↦ H.limit_nonneg _) hZ0 hWft)
    (integrable_normalizedWeight (Measure.pi μ) _ _ hwm
      (fun x ↦ H.limit_nonneg _) hZ0 hWgt)
    (integrable_normalizedWeight (Measure.pi μ) _ _ hwm
      (fun x ↦ H.limit_nonneg _) hZ0 hWfgt) hext
  rw [sliceMean_eq_integral_normalizedWeight (Measure.pi μ) _ _
      (splitLastFun_measurable W hWm) (fun p ↦ H.limit_nonneg _) t hWt,
    sliceMean_eq_integral_normalizedWeight (Measure.pi μ) _ _
      (splitLastFun_measurable W hWm) (fun p ↦ H.limit_nonneg _) t hWt,
    sliceMean_eq_integral_normalizedWeight (Measure.pi μ) _ _
      (splitLastFun_measurable W hWm) (fun p ↦ H.limit_nonneg _) t hWt]
  exact hreal

/-- Strict increase in the last argument becomes strict increase of conditional
means after the proved Holley comparison between the two conditional laws. -/
theorem sliceMean_strict
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hWm : Measurable W) (f : (Fin (n + 1) → ℝ) → ℝ)
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : SupportedMonotone W f) (hfstrict : StrictLastOnSupport W f)
    (s t : ℝ) (hst : s < t)
    (hWs : Integrable (fun x ↦ W (appendLast x s)) (Measure.pi μ))
    (hWt : Integrable (fun x ↦ W (appendLast x t)) (Measure.pi μ))
    (hWfs : Integrable (fun x ↦ W (appendLast x s) * f (appendLast x s)) (Measure.pi μ))
    (hWft : Integrable (fun x ↦ W (appendLast x t) * f (appendLast x t)) (Measure.pi μ))
    (hZs : 0 < sliceNorm (Measure.pi μ) (splitLastFun W) s)
    (hZt : 0 < sliceNorm (Measure.pi μ) (splitLastFun W) t)
    (hnest : ∀ x, 0 < W (appendLast x s) → 0 < W (appendLast x t)) :
    sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun f) s <
      sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun f) t := by
  obtain ⟨hZs0, hZstop⟩ := slice_lintegral_ofReal_ne_zero_top
    (Measure.pi μ) W H.limit_nonneg s hWs hZs
  obtain ⟨hZt0, hZttop⟩ := slice_lintegral_ofReal_ne_zero_top
    (Measure.pi μ) W H.limit_nonneg t hWt hZt
  have hwsm : Measurable (fun x : Fin n → ℝ ↦ W (appendLast x s)) :=
    hWm.comp (snoc_measurable s)
  have hwtm : Measurable (fun x : Fin n → ℝ ↦ W (appendLast x t)) :=
    hWm.comp (snoc_measurable t)
  have hftm : Measurable (fun x : Fin n → ℝ ↦ f (appendLast x t)) :=
    hfm.comp (snoc_measurable t)
  have hholley := H.slice_holley μ s t hst.le (fun x ↦ f (appendLast x t))
    hftm (fun x ↦ hf0 _) (fun x y hx hy hxy ↦
      hfi _ _ (hnest x hx) hy (appendLast_le hxy le_rfl))
  have hext := normalizedWeight_lintegral_holley (Measure.pi μ)
    (fun x ↦ W (appendLast x s)) (fun x ↦ W (appendLast x t))
    (fun x ↦ f (appendLast x t)) hwsm hwtm hftm
    (fun x ↦ H.limit_nonneg _) (fun x ↦ H.limit_nonneg _)
    hZs0 hZstop hZt0 hZttop hholley
  have hstrict := normalizedWeight_integral_strict_of_holley (Measure.pi μ)
    (fun x ↦ W (appendLast x s)) (fun x ↦ W (appendLast x t))
    (fun x ↦ f (appendLast x s)) (fun x ↦ f (appendLast x t))
    hwsm hftm (fun x ↦ hf0 _) hZs0 hZstop
    (integrable_normalizedWeight (Measure.pi μ) _ _ hwsm
      (fun x ↦ H.limit_nonneg _) hZs0 hWfs)
    (integrable_normalizedWeight (Measure.pi μ) _ _ hwtm
      (fun x ↦ H.limit_nonneg _) hZt0 hWft)
    (fun x hx ↦ hfstrict x s t hst hx (hnest x hx)) hext
  rw [sliceMean_eq_integral_normalizedWeight (Measure.pi μ) _ _
      (splitLastFun_measurable W hWm) (fun p ↦ H.limit_nonneg _) s hWs,
    sliceMean_eq_integral_normalizedWeight (Measure.pi μ) _ _
      (splitLastFun_measurable W hWm) (fun p ↦ H.limit_nonneg _) t hWt]
  exact hstrict

/-- Strict association under a normalized product density with nested last
coordinate supports. Association and stochastic ordering are conclusions of
the lattice approximation data, not hypotheses of this theorem. -/
theorem strict_association_prod
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (hWm : Measurable W) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone W f) (hgi : SupportedMonotone W g)
    (hfstrict : StrictLastOnSupport W f) (hgstrict : StrictLastOnSupport W g)
    (hWi : Integrable (splitLastFun W) ((Measure.pi μ).prod ν))
    (hWone : ∫ p, splitLastFun W p ∂(Measure.pi μ).prod ν = 1)
    (hWfi : Integrable (fun p ↦ splitLastFun W p * splitLastFun f p)
      ((Measure.pi μ).prod ν))
    (hWgi : Integrable (fun p ↦ splitLastFun W p * splitLastFun g p)
      ((Measure.pi μ).prod ν))
    (hWfgi : Integrable (fun p ↦ splitLastFun W p * (splitLastFun f p * splitLastFun g p))
      ((Measure.pi μ).prod ν))
    (hWf2i : Integrable (fun p ↦ splitLastFun W p * (splitLastFun f p) ^ 2)
      ((Measure.pi μ).prod ν))
    (hWg2i : Integrable (fun p ↦ splitLastFun W p * (splitLastFun g p) ^ 2)
      ((Measure.pi μ).prod ν))
    (hnest : ∀ s t, s < t → 0 < sliceNorm (Measure.pi μ) (splitLastFun W) t →
      ∀ x, 0 < W (appendLast x s) → 0 < W (appendLast x t)) :
    (∫ p, splitLastFun W p * splitLastFun f p ∂(Measure.pi μ).prod ν) *
        (∫ p, splitLastFun W p * splitLastFun g p ∂(Measure.pi μ).prod ν) <
      ∫ p, splitLastFun W p * (splitLastFun f p * splitLastFun g p)
        ∂(Measure.pi μ).prod ν := by
  let good : Set ℝ := {t |
    Integrable (fun x ↦ W (appendLast x t)) (Measure.pi μ) ∧
    Integrable (fun x ↦ W (appendLast x t) * f (appendLast x t)) (Measure.pi μ) ∧
    Integrable (fun x ↦ W (appendLast x t) * g (appendLast x t)) (Measure.pi μ) ∧
    Integrable (fun x ↦ W (appendLast x t) *
      (f (appendLast x t) * g (appendLast x t))) (Measure.pi μ) ∧
    0 < sliceNorm (Measure.pi μ) (splitLastFun W) t}
  have hAC := densityMarginal_absolutelyContinuous (Measure.pi μ) ν (splitLastFun W)
  have hgood : ∀ᵐ t ∂densityMarginal (Measure.pi μ) ν (splitLastFun W), t ∈ good := by
    filter_upwards [hAC.ae_le hWi.prod_left_ae, hAC.ae_le hWfi.prod_left_ae,
      hAC.ae_le hWgi.prod_left_ae, hAC.ae_le hWfgi.prod_left_ae,
      densityMarginal_sliceNorm_pos_ae (Measure.pi μ) ν (splitLastFun W)
        (splitLastFun_measurable W hWm)] with t hWt hWft hWgt hWfgt hZt
    exact ⟨hWt, hWft, hWgt, hWfgt, hZt⟩
  have hfmeans : StrictMonoOn (sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun f))
      good := by
    intro s hs t ht hst
    exact H.sliceMean_strict μ hWm f hfm hf0 hfi hfstrict s t hst
      hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2.2.2 ht.2.2.2.2
      (hnest s t hst ht.2.2.2.2)
  have hgmeans : StrictMonoOn (sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun g))
      good := by
    intro s hs t ht hst
    exact H.sliceMean_strict μ hWm g hgm hg0 hgi hgstrict s t hst
      hs.1 ht.1 hs.2.2.1 ht.2.2.1 hs.2.2.2.2 ht.2.2.2.2
      (hnest s t hst ht.2.2.2.2)
  have hweak : ∀ᵐ t ∂densityMarginal (Measure.pi μ) ν (splitLastFun W),
      sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun f) t *
          sliceMean (Measure.pi μ) (splitLastFun W) (splitLastFun g) t ≤
        sliceMean (Measure.pi μ) (splitLastFun W)
          (fun p ↦ splitLastFun f p * splitLastFun g p) t := by
    filter_upwards [hgood] with t ht
    exact H.sliceMean_association μ hWm f g hfm hgm hf0 hg0 hfi hgi
      t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2
  exact strict_association_of_strict_sliceMeans (Measure.pi μ) ν
    (splitLastFun W) (splitLastFun f) (splitLastFun g)
    (splitLastFun_measurable W hWm) (splitLastFun_measurable f hfm)
    (splitLastFun_measurable g hgm) (fun p ↦ H.limit_nonneg _)
    hWi hWone hWfi hWgi hWfgi hWf2i hWg2i good hgood hfmeans hgmeans hweak

end MTP2Approximation

/-- The exact separate-weight Vandermonde density supplies the support nesting
used by the strict theorem. The last reference measure may be any atomless
sigma-finite measure, allowing normalization in that coordinate alone. -/
theorem vandermonde_strict_association_prod
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (Fin (n + 1) → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone (vandermondeWeight w β) f)
    (hgi : SupportedMonotone (vandermondeWeight w β) g)
    (hfstrict : StrictLastOnSupport (vandermondeWeight w β) f)
    (hgstrict : StrictLastOnSupport (vandermondeWeight w β) g)
    (hWi : Integrable (splitLastFun (vandermondeWeight w β)) ((Measure.pi μ).prod ν))
    (hWone : ∫ p, splitLastFun (vandermondeWeight w β) p ∂(Measure.pi μ).prod ν = 1)
    (hWfi : Integrable (fun p ↦ splitLastFun (vandermondeWeight w β) p * splitLastFun f p)
      ((Measure.pi μ).prod ν))
    (hWgi : Integrable (fun p ↦ splitLastFun (vandermondeWeight w β) p * splitLastFun g p)
      ((Measure.pi μ).prod ν))
    (hWfgi : Integrable (fun p ↦ splitLastFun (vandermondeWeight w β) p *
      (splitLastFun f p * splitLastFun g p)) ((Measure.pi μ).prod ν))
    (hWf2i : Integrable (fun p ↦ splitLastFun (vandermondeWeight w β) p *
      (splitLastFun f p) ^ 2) ((Measure.pi μ).prod ν))
    (hWg2i : Integrable (fun p ↦ splitLastFun (vandermondeWeight w β) p *
      (splitLastFun g p) ^ 2) ((Measure.pi μ).prod ν)) :
    (∫ p, splitLastFun (vandermondeWeight w β) p * splitLastFun f p ∂(Measure.pi μ).prod ν) *
        (∫ p, splitLastFun (vandermondeWeight w β) p * splitLastFun g p ∂(Measure.pi μ).prod ν) <
      ∫ p, splitLastFun (vandermondeWeight w β) p * (splitLastFun f p * splitLastFun g p)
        ∂(Measure.pi μ).prod ν := by
  apply (vandermondeApproximation w β hβ.le hwm hw0).strict_association_prod
    μ ν (vandermondeWeight_measurable w β hwm) f g hfm hgm hf0 hg0 hfi hgi
    hfstrict hgstrict hWi hWone hWfi hWgi hWfgi hWf2i hWg2i
  intro s t hst hZt x hx
  exact vandermonde_slice_support_nested w β hβ hw0 s t hst.le
    (last_weight_pos_of_sliceNorm_pos (Measure.pi μ) w β hw0 t hZt) x hx

end WishartVerification
end CanonicalSource76

section CanonicalSource77
/- Source: Wishart/ProbabilityStrictAssociation.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Strict Vandermonde association under product probability reference laws

The full density is normalized by rescaling the last reference measure only.
This preserves the actual Vandermonde support and all lower-coordinate product
probability laws, so the conditional comparison from `SliceAssociation` applies
without additional assumptions.
-/

namespace WishartVerification

section DensityTransport

variable {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]

theorem measurePreserving_withDensity_comp {μ : Measure Ω} {ν : Measure Ψ}
    {e : Ω → Ψ} (he : MeasurePreserving e μ ν) (w : Ψ → ℝ≥0∞)
    (hwm : Measurable w) :
    MeasurePreserving e (μ.withDensity (fun x ↦ w (e x))) (ν.withDensity w) := by
  refine ⟨he.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he.measurable hs,
    withDensity_apply _ (he.measurable hs), withDensity_apply _ hs]
  exact he.setLIntegral_comp_preimage hs hwm

end DensityTransport

variable {n : ℕ}

def appendLastEquiv : ((Fin n → ℝ) × ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun p := appendLast p.1 p.2
  invFun x := (fun i ↦ x i.castSucc, x (Fin.last n))
  left_inv p := by
    rcases p with ⟨x, t⟩
    simp
  right_inv x := by
    funext i
    cases i using Fin.lastCases <;> simp
  measurable_toFun := snoc_uncurry_measurable
  measurable_invFun := (Measurable.of_eval fun i ↦ measurable_pi_apply i.castSucc).prodMk
    (measurable_pi_apply (Fin.last n))

@[simp] theorem appendLastEquiv_apply (p : (Fin n → ℝ) × ℝ) :
    appendLastEquiv p = appendLast p.1 p.2 := rfl

theorem appendLast_measurePreserving (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving appendLastEquiv
      ((Measure.pi fun i : Fin n ↦ μ i.castSucc).prod (μ (Fin.last n))) (Measure.pi μ) := by
  have hi := MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))
    (measurePreserving_piFinSuccAbove μ (Fin.last n))
  simp only [Fin.succAbove_last] at hi
  have hc := hi.comp (Measure.measurePreserving_swap
    (μ := Measure.pi fun i : Fin n ↦ μ i.castSucc) (ν := μ (Fin.last n)))
  convert hc using 1
  ext p i
  simp [appendLastEquiv, appendLast, MeasurableEquiv.piFinSuccAbove,
    Fin.insertNthEquiv, Fin.insertNth_last']

theorem appendLast_normalized_measurePreserving
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (W : (Fin (n + 1) → ℝ) → ℝ) (hWm : Measurable W) :
    MeasurePreserving appendLastEquiv
      (((Measure.pi fun i : Fin n ↦ μ i.castSucc).prod
        ((∫⁻ x, ENNReal.ofReal (W x) ∂Measure.pi μ)⁻¹ • μ (Fin.last n))).withDensity
          (fun p ↦ ENNReal.ofReal (splitLastFun W p)))
      (normalizedWeight (Measure.pi μ) W) := by
  let c := (∫⁻ x, ENNReal.ofReal (W x) ∂Measure.pi μ)⁻¹
  have hbase : MeasurePreserving appendLastEquiv
      ((Measure.pi fun i : Fin n ↦ μ i.castSucc).prod (c • μ (Fin.last n)))
      (c • Measure.pi μ) := by
    rw [Measure.prod_smul_right]
    exact (appendLast_measurePreserving μ).smul_measure c
  have hd := measurePreserving_withDensity_comp hbase
    (fun x ↦ ENNReal.ofReal (W x)) hWm.ennreal_ofReal
  simpa only [withDensity_smul_measure, normalizedWeight, appendLastEquiv_apply,
    splitLastFun, c] using hd

/-- Strict association with the ordinary finite-second-moment hypotheses.
Every finite dimension at least one is covered, as is every positive real beta.
The separate weights need only be nonnegative; strictness is required on their
actual positive support. -/
theorem vandermonde_strict_association_probability
    (μ : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [NullSingletonClass (μ (Fin.last n))]
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (Fin (n + 1) → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone (vandermondeWeight w β) f)
    (hgi : SupportedMonotone (vandermondeWeight w β) g)
    (hfstrict : StrictLastOnSupport (vandermondeWeight w β) f)
    (hgstrict : StrictLastOnSupport (vandermondeWeight w β) g)
    (hZ0 : (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi μ) ≠ 0)
    (hZtop : (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi μ) ≠ ∞)
    (hf2 : MemLp f 2 (normalizedWeight (Measure.pi μ) (vandermondeWeight w β)))
    (hg2 : MemLp g 2 (normalizedWeight (Measure.pi μ) (vandermondeWeight w β))) :
    (∫ x, f x ∂normalizedWeight (Measure.pi μ) (vandermondeWeight w β)) *
        (∫ x, g x ∂normalizedWeight (Measure.pi μ) (vandermondeWeight w β)) <
      ∫ x, f x * g x ∂normalizedWeight (Measure.pi μ) (vandermondeWeight w β) := by
  let W := vandermondeWeight w β
  let κ := normalizedWeight (Measure.pi μ) W
  let c := (∫⁻ x, ENNReal.ofReal (W x) ∂Measure.pi μ)⁻¹
  let ν := c • μ (Fin.last n)
  let σ := (Measure.pi fun i : Fin n ↦ μ i.castSucc).prod ν
  letI : NullSingletonClass ν := ⟨fun x ↦ by
    simp only [ν, Measure.smul_apply, measure_singleton, smul_zero]⟩
  have hWm : Measurable W := vandermondeWeight_measurable w β hwm
  have hW0 (x) : 0 ≤ W x := vandermondeWeight_nonneg w β hw0 x
  have hWsm : Measurable (splitLastFun W) := splitLastFun_measurable W hWm
  letI : IsProbabilityMeasure κ := normalizedWeight_probability (Measure.pi μ) W hZ0 hZtop
  have hmp : MeasurePreserving appendLastEquiv
      (σ.withDensity (fun p ↦ ENNReal.ofReal (splitLastFun W p))) κ :=
    appendLast_normalized_measurePreserving μ W hWm
  have transport_integrable (a : (Fin (n + 1) → ℝ) → ℝ) (ha : Integrable a κ) :
      Integrable (fun p ↦ splitLastFun W p * splitLastFun a p) σ := by
    apply (integrable_withDensity_ofReal_iff σ (splitLastFun W) (splitLastFun a)
      hWsm (fun p ↦ hW0 _)).mp
    change Integrable (fun p ↦ a (appendLast p.1 p.2))
      (σ.withDensity (fun p ↦ ENNReal.ofReal (splitLastFun W p)))
    exact hmp.integrable_comp_of_integrable ha
  have transport_integral (a : (Fin (n + 1) → ℝ) → ℝ) :
      (∫ p, splitLastFun W p * splitLastFun a p ∂σ) = ∫ x, a x ∂κ := by
    rw [← integral_withDensity_ofReal σ (splitLastFun W) (splitLastFun a)
      hWsm (fun p ↦ hW0 _)]
    exact hmp.integral_comp appendLastEquiv.measurableEmbedding a
  have hWi : Integrable (splitLastFun W) σ := by
    change Integrable (fun p ↦ W (appendLast p.1 p.2)) σ
    simpa only [splitLastFun, mul_one] using
      transport_integrable (fun _ ↦ 1) (integrable_const 1)
  have hWone : ∫ p, splitLastFun W p ∂σ = 1 := by
    simpa only [splitLastFun, mul_one, integral_const, probReal_univ,
      one_smul] using transport_integral (fun _ ↦ 1)
  have hf2i : Integrable (fun x ↦ f x ^ 2) κ :=
    (memLp_two_iff_integrable_sq hf2.aestronglyMeasurable).mp hf2
  have hg2i : Integrable (fun x ↦ g x ^ 2) κ :=
    (memLp_two_iff_integrable_sq hg2.aestronglyMeasurable).mp hg2
  have hstrict := vandermonde_strict_association_prod
    (fun i : Fin n ↦ μ i.castSucc) ν w β hβ hwm hw0 f g hfm hgm hf0 hg0
    hfi hgi hfstrict hgstrict hWi hWone
    (transport_integrable f (hf2.integrable (by norm_num)))
    (transport_integrable g (hg2.integrable (by norm_num)))
    (transport_integrable (fun x ↦ f x * g x) (hf2.integrable_mul hg2))
    (transport_integrable (fun x ↦ f x ^ 2) hf2i)
    (transport_integrable (fun x ↦ g x ^ 2) hg2i)
  change (∫ p, splitLastFun W p * splitLastFun f p ∂σ) *
      (∫ p, splitLastFun W p * splitLastFun g p ∂σ) <
    ∫ p, splitLastFun W p * splitLastFun (fun x ↦ f x * g x) p ∂σ at hstrict
  rw [transport_integral f, transport_integral g, transport_integral (fun x ↦ f x * g x)] at hstrict
  exact hstrict

end WishartVerification
end CanonicalSource77

section CanonicalSource78
/- Source: Wishart/StrictChamberAssociation.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Strict association for the ordered Lebesgue chamber

The probability-reference result transfers through an equality of the entire
normalized measures. Thus second moments, expectations and strictness keep their
original meaning under the Lebesgue density.
-/

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem vandermonde_withDensity_reference_change
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    (w : ι → ℝ → ℝ) (β : ℝ)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t) :
    (Measure.pi ν).withDensity (fun x ↦ ENNReal.ofReal (vandermondeWeight w β x)) =
      (Measure.pi fun i ↦ (ν i).toFinite).withDensity
        (fun x ↦ ENNReal.ofReal (vandermondeWeight (referenceCorrectedWeight ν w) β x)) := by
  apply Measure.ext
  intro s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  have h := vandermonde_reference_change ν w β hwm hw0
    (s.indicator (fun _ ↦ 1)) (measurable_const.indicator hs)
    (fun x ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)
  have hind (W : (ι → ℝ) → ℝ) :
      (fun x ↦ ENNReal.ofReal (W x * s.indicator (fun _ ↦ 1) x)) =
        s.indicator (fun x ↦ ENNReal.ofReal (W x)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hind, hind, lintegral_indicator hs, lintegral_indicator hs] at h
  exact h

theorem vandermonde_normalized_reference_change
    (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    (w : ι → ℝ → ℝ) (β : ℝ)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t) :
    normalizedWeight (Measure.pi ν) (vandermondeWeight w β) =
      normalizedWeight (Measure.pi fun i ↦ (ν i).toFinite)
        (vandermondeWeight (referenceCorrectedWeight ν w) β) := by
  have hZ := vandermonde_reference_change ν w β hwm hw0
    (fun _ ↦ 1) measurable_const (fun _ ↦ zero_le_one)
  simp only [mul_one] at hZ
  unfold normalizedWeight
  rw [hZ, vandermonde_withDensity_reference_change ν w β hwm hw0]

variable {n : ℕ}

/-- Strict Vandermonde association over arbitrary nonzero sigma-finite
coordinate reference measures, with an atomless last coordinate. -/
theorem vandermonde_strict_association_sigmaFinite
    (ν : Fin (n + 1) → Measure ℝ) [∀ i, SigmaFinite (ν i)] [∀ i, NeZero (ν i)]
    [NullSingletonClass (ν (Fin.last n))]
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (f g : (Fin (n + 1) → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : SupportedMonotone (vandermondeWeight w β) f)
    (hgi : SupportedMonotone (vandermondeWeight w β) g)
    (hfstrict : StrictLastOnSupport (vandermondeWeight w β) f)
    (hgstrict : StrictLastOnSupport (vandermondeWeight w β) g)
    (hZ0 : (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi ν) ≠ 0)
    (hZtop : (∫⁻ x, ENNReal.ofReal (vandermondeWeight w β x) ∂Measure.pi ν) ≠ ∞)
    (hf2 : MemLp f 2 (normalizedWeight (Measure.pi ν) (vandermondeWeight w β)))
    (hg2 : MemLp g 2 (normalizedWeight (Measure.pi ν) (vandermondeWeight w β))) :
    (∫ x, f x ∂normalizedWeight (Measure.pi ν) (vandermondeWeight w β)) *
        (∫ x, g x ∂normalizedWeight (Measure.pi ν) (vandermondeWeight w β)) <
      ∫ x, f x * g x ∂normalizedWeight (Measure.pi ν) (vandermondeWeight w β) := by
  letI : NullSingletonClass ((ν (Fin.last n)).toFinite) :=
    ⟨fun x ↦ toFinite_absolutelyContinuous _ (measure_singleton x)⟩
  have hZ := vandermonde_reference_change ν w β hwm hw0
    (fun _ ↦ 1) measurable_const (fun _ ↦ zero_le_one)
  simp only [mul_one] at hZ
  have hmeasure := vandermonde_normalized_reference_change ν w β hwm hw0
  have hsupp := referenceCorrectedWeight_support ν w β
  rw [hmeasure] at hf2 hg2 ⊢
  apply vandermonde_strict_association_probability
    (fun i ↦ (ν i).toFinite) (referenceCorrectedWeight ν w) β hβ
    (referenceCorrectedWeight_measurable ν w hwm)
    (referenceCorrectedWeight_nonneg ν w hw0) f g hfm hgm hf0 hg0
    (fun x y hx hy hxy ↦ hfi x y (hsupp x hx) (hsupp y hy) hxy)
    (fun x y hx hy hxy ↦ hgi x y (hsupp x hx) (hsupp y hy) hxy)
    (fun x s t hst hs ht ↦ hfstrict x s t hst (hsupp _ hs) (hsupp _ ht))
    (fun x s t hst hs ht ↦ hgstrict x s t hst (hsupp _ hs) (hsupp _ ht))
    (by rwa [← hZ]) (by rwa [← hZ]) hf2 hg2

theorem mem_orderedChamber_of_chamberWeight_pos
    (s : Set ℝ) (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (x : Fin (n + 1) → ℝ) (hx : 0 < chamberWeight s w β x) :
    x ∈ orderedChamber s := by
  by_contra h
  rw [chamberWeight_eq_zero_off s w β hβ x h] at hx
  exact (lt_irrefl 0) hx

/-- The strict part of Lemma 2.1, retaining its exact finite-second-moment
condition and strict increase only in the last coordinate of the chamber. -/
theorem lemma_2_1_strict_association
    (s : Set ℝ) (hs : MeasurableSet s) (w : Fin (n + 1) → ℝ → ℝ)
    (β : ℝ) (hβ : 0 < β) (hwm : ∀ i, Measurable (w i))
    (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ 0)
    (hZtop : (∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (chamberWeight s w β x)) ≠ ∞)
    (f g : (Fin (n + 1) → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : MonotoneOn f (orderedChamber s)) (hgi : MonotoneOn g (orderedChamber s))
    (hfstrict : ∀ x a b, a < b → appendLast x a ∈ orderedChamber s →
      appendLast x b ∈ orderedChamber s → f (appendLast x a) < f (appendLast x b))
    (hgstrict : ∀ x a b, a < b → appendLast x a ∈ orderedChamber s →
      appendLast x b ∈ orderedChamber s → g (appendLast x a) < g (appendLast x b))
    (hf2 : MemLp f 2 (normalizedWeight volume (chamberWeight s w β)))
    (hg2 : MemLp g 2 (normalizedWeight volume (chamberWeight s w β))) :
    (∫ x, f x ∂normalizedWeight volume (chamberWeight s w β)) *
        (∫ x, g x ∂normalizedWeight volume (chamberWeight s w β)) <
      ∫ x, f x * g x ∂normalizedWeight volume (chamberWeight s w β) := by
  apply vandermonde_strict_association_sigmaFinite
    (fun _ : Fin (n + 1) ↦ volume) (fun i ↦ s.indicator (w i)) β hβ
    (fun i ↦ (hwm i).indicator hs)
    (fun i t ↦ Set.indicator_nonneg (fun t _ ↦ hw0 i t) t) f g hfm hgm hf0 hg0
    (supportedMonotone_chamberWeight s w β hβ f hfi)
    (supportedMonotone_chamberWeight s w β hβ g hgi)
    (fun x a b hab ha hb ↦ hfstrict x a b hab
      (mem_orderedChamber_of_chamberWeight_pos s w β hβ _ ha)
      (mem_orderedChamber_of_chamberWeight_pos s w β hβ _ hb))
    (fun x a b hab ha hb ↦ hgstrict x a b hab
      (mem_orderedChamber_of_chamberWeight_pos s w β hβ _ ha)
      (mem_orderedChamber_of_chamberWeight_pos s w β hβ _ hb))
    hZ0 hZtop hf2 hg2

end WishartVerification
end CanonicalSource78

section CanonicalSource79
/- Source: Wishart/SpectralAssociationBridge.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# From exact spectral moment identities to a principal-factor split

The selected spectral factor is the ordinary positive determinant power on the
positive chamber. The three expectation identities below are explicit inputs
to be established from regression and spectral disintegration of the actual
Wishart law. These bridge results do not assert that those inputs have already
been verified.
-/

namespace WishartVerification

variable {ι : Type*} [Fintype ι]

noncomputable def spectralDetPower (η : ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, (max (x i) 0) ^ η

theorem spectralDetPower_nonneg (η : ℝ) (x : ι → ℝ) :
    0 ≤ spectralDetPower η x :=
  Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (le_max_right _ _) _

theorem spectralDetPower_measurable (η : ℝ) : Measurable (spectralDetPower (ι := ι) η) := by
  unfold spectralDetPower
  exact Finset.measurable_prod _ fun i _ ↦
    ((measurable_pi_apply i).max measurable_const).pow_const η

theorem spectralDetPower_monotone (η : ℝ) (hη : 0 ≤ η) :
    Monotone (spectralDetPower (ι := ι) η) := by
  intro x y hxy
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Real.rpow_nonneg (le_max_right _ _) _
  · intro i hi
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le_max (hxy i) le_rfl) hη

theorem nonnegative_prod_rpow (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (η : ℝ)
    (J : Finset ι) : (∏ i ∈ J, x i) ^ η = ∏ i ∈ J, x i ^ η := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
      simp only [Finset.prod_insert hi]
      rw [Real.mul_rpow (hx i) (Finset.prod_nonneg fun j _ ↦ hx j), ih]

/-- On the positive chamber, the extension is exactly the power of the
diagonal determinant appearing in the whitened selected principal minor. -/
theorem spectralDetPower_eq_diagonal_det_rpow [DecidableEq ι]
    (η : ℝ) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    spectralDetPower η x = (Matrix.diagonal x).det ^ η := by
  rw [Matrix.det_diagonal, nonnegative_prod_rpow x (fun i ↦ (hx i).le) η]
  apply Finset.prod_congr rfl
  intro i hi
  rw [max_eq_left (hx i).le]

theorem spectralDetPower_appendLast {n : ℕ} (η : ℝ) (x : Fin n → ℝ) (t : ℝ) :
    spectralDetPower η (appendLast x t) = spectralDetPower η x * (max t 0) ^ η := by
  unfold spectralDetPower
  rw [Fin.prod_univ_castSucc]
  simp only [appendLast_castSucc, appendLast_last]

theorem spectralDetPower_strict_last {n : ℕ} (η : ℝ) (hη : 0 < η)
    (x : Fin n → ℝ) (a b : ℝ) (hab : a < b)
    (ha : appendLast x a ∈ orderedChamber (Set.Ioi 0))
    (hb : appendLast x b ∈ orderedChamber (Set.Ioi 0)) :
    spectralDetPower η (appendLast x a) < spectralDetPower η (appendLast x b) := by
  have hapos : 0 < a := by simpa only [appendLast_last, Set.mem_Ioi] using ha.2 (Fin.last n)
  have hbpos : 0 < b := by simpa only [appendLast_last, Set.mem_Ioi] using hb.2 (Fin.last n)
  have hxpos (i : Fin n) : 0 < x i := by
    simpa only [appendLast_castSucc, Set.mem_Ioi] using ha.2 i.castSucc
  have hprod : 0 < spectralDetPower η x := by
    apply Finset.prod_pos
    intro i hi
    exact Real.rpow_pos_of_pos ((hxpos i).trans_le (le_max_left _ _)) _
  rw [spectralDetPower_appendLast, spectralDetPower_appendLast,
    max_eq_left hapos.le, max_eq_left hbpos.le]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hapos.le hab hη) hprod

section PrincipalSplit

variable {p d q : ℕ} (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
variable (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d)

theorem principal_split_of_spectral_representation
    (hj : j ∈ J) (hνj : 0 ≤ ν j)
    (w : Fin q → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : Fin q → ℝ, ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ 0)
    (hZtop : (∫⁻ x : Fin q → ℝ, ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ ∞)
    (F : (Fin q → ℝ) → ℝ) (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFmono : MonotoneOn F (orderedChamber (Set.Ioi 0)))
    (hhint : Integrable (spectralDetPower (ν j))
      (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (hFint : Integrable F (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (hhFint : Integrable (fun x ↦ spectralDetPower (ν j) x * F x)
      (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (c : ℝ) (hc : 0 ≤ c)
    (hjoint : principalMoment α Sigma P ν J = c *
      ∫ x, spectralDetPower (ν j) x * F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β))
    (hselected : principalMoment α Sigma P ν {j} = c *
      ∫ x, spectralDetPower (ν j) x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β))
    (hremaining : principalMoment α Sigma P ν (J.erase j) =
      ∫ x, F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
      principalMoment α Sigma P ν J := by
  have hext := lemma_2_1_association (Set.Ioi 0) measurableSet_Ioi w β hβ hwm hw0 hZ0 hZtop
    (spectralDetPower (ν j)) F (spectralDetPower_measurable _) hFm
    (spectralDetPower_nonneg _) hF0
    ((spectralDetPower_monotone _ hνj).monotoneOn _) hFmono
  have hreal := integral_mul_le_of_lintegral_mul_le _ _ _
    (spectralDetPower_nonneg _) hF0 hhint hFint hhFint hext
  rw [hselected, hremaining, hjoint]
  calc
    (c * ∫ x, spectralDetPower (ν j) x ∂normalizedWeight volume
      (chamberWeight (Set.Ioi 0) w β)) *
        (∫ x, F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) =
      c * ((∫ x, spectralDetPower (ν j) x ∂normalizedWeight volume
        (chamberWeight (Set.Ioi 0) w β)) *
          ∫ x, F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hreal hc

theorem principal_strict_split_of_spectral_representation {n : ℕ}
    (hj : j ∈ J) (hνj : 0 < ν j)
    (w : Fin (n + 1) → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : Fin (n + 1) → ℝ,
      ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ 0)
    (hZtop : (∫⁻ x : Fin (n + 1) → ℝ,
      ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ ∞)
    (F : (Fin (n + 1) → ℝ) → ℝ) (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFmono : MonotoneOn F (orderedChamber (Set.Ioi 0)))
    (hFstrict : ∀ x a b, a < b → appendLast x a ∈ orderedChamber (Set.Ioi 0) →
      appendLast x b ∈ orderedChamber (Set.Ioi 0) → F (appendLast x a) < F (appendLast x b))
    (hh2 : MemLp (spectralDetPower (ν j)) 2
      (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (hF2 : MemLp F 2 (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (c : ℝ) (hc : 0 < c)
    (hjoint : principalMoment α Sigma P ν J = c *
      ∫ x, spectralDetPower (ν j) x * F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β))
    (hselected : principalMoment α Sigma P ν {j} = c *
      ∫ x, spectralDetPower (ν j) x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β))
    (hremaining : principalMoment α Sigma P ν (J.erase j) =
      ∫ x, F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) <
      principalMoment α Sigma P ν J := by
  have hstrict := lemma_2_1_strict_association (Set.Ioi 0) measurableSet_Ioi w β hβ hwm hw0
    hZ0 hZtop (spectralDetPower (ν j)) F (spectralDetPower_measurable _) hFm
    (spectralDetPower_nonneg _) hF0
    ((spectralDetPower_monotone _ hνj.le).monotoneOn _) hFmono
    (spectralDetPower_strict_last _ hνj) hFstrict hh2 hF2
  rw [hselected, hremaining, hjoint, mul_assoc]
  exact mul_lt_mul_of_pos_left hstrict hc

end PrincipalSplit

end WishartVerification
end CanonicalSource79

section CanonicalSource80
/- Source: Wishart/ParameterAverage.lean -/



open scoped Classical ENNReal

/-!
# Averaging a conditional spectral test

This file supplies the analytic operations needed when a conditional regression
moment is averaged over an independent Haar frame. The averaging law is any
probability measure. Measurability, monotonicity, strictness, Fubini identities,
and square-integrability are proved from the actual integrand; none of those
properties is introduced as an unexplained property of the averaged function.

The chamber-restricted average is defined to be zero outside its stated domain.
That extension is measurable and has exactly the original expectations whenever
the parameter law is supported on the domain.
-/

open MeasureTheory

namespace WishartVerification

section Averages

variable {Λ Θ : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ]

noncomputable def parameterAverage (ν : Measure Θ) (H : Λ × Θ → ℝ) (x : Λ) : ℝ :=
  ∫ u, H (x, u) ∂ν

noncomputable def parameterAverageOn (ν : Measure Θ) (s : Set Λ) (H : Λ × Θ → ℝ) : Λ → ℝ :=
  s.indicator (parameterAverage ν H)

theorem parameterAverage_measurable (ν : Measure Θ) [SFinite ν]
    (H : Λ × Θ → ℝ) (hHm : Measurable H) : Measurable (parameterAverage ν H) :=
  hHm.stronglyMeasurable.integral_prod_right'.measurable

theorem parameterAverageOn_measurable (ν : Measure Θ) [SFinite ν]
    (s : Set Λ) (hs : MeasurableSet s) (H : Λ × Θ → ℝ) (hHm : Measurable H) :
    Measurable (parameterAverageOn ν s H) :=
  (parameterAverage_measurable ν H hHm).indicator hs

@[simp] theorem parameterAverageOn_of_mem (ν : Measure Θ) (s : Set Λ)
    (H : Λ × Θ → ℝ) {x : Λ} (hx : x ∈ s) :
    parameterAverageOn ν s H x = parameterAverage ν H x := Set.indicator_of_mem hx _

@[simp] theorem parameterAverageOn_of_not_mem (ν : Measure Θ) (s : Set Λ)
    (H : Λ × Θ → ℝ) {x : Λ} (hx : x ∉ s) : parameterAverageOn ν s H x = 0 :=
  Set.indicator_of_notMem hx _

theorem parameterAverageOn_nonneg (ν : Measure Θ) (s : Set Λ) (H : Λ × Θ → ℝ)
    (hH0 : ∀ x ∈ s, ∀ u, 0 ≤ H (x, u)) (x : Λ) :
    0 ≤ parameterAverageOn ν s H x := by
  by_cases hx : x ∈ s
  · rw [parameterAverageOn_of_mem ν s H hx]
    exact integral_nonneg (hH0 x hx)
  · simpa only [parameterAverageOn_of_not_mem ν s H hx] using (le_refl (0 : ℝ))

theorem parameterAverageOn_ae_eq (μ : Measure Λ) (ν : Measure Θ)
    (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s) (H : Λ × Θ → ℝ) :
    parameterAverageOn ν s H =ᵐ[μ] parameterAverage ν H :=
  hs.mono fun x hx ↦ parameterAverageOn_of_mem ν s H hx

theorem parameterAverage_integrable (μ : Measure Λ) (ν : Measure Θ) [SFinite ν]
    (H : Λ × Θ → ℝ) (hHi : Integrable H (μ.prod ν)) :
    Integrable (parameterAverage ν H) μ := hHi.integral_prod_left

theorem parameterAverageOn_integrable (μ : Measure Λ) (ν : Measure Θ) [SFinite ν]
    (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (H : Λ × Θ → ℝ) (hHi : Integrable H (μ.prod ν)) :
    Integrable (parameterAverageOn ν s H) μ :=
  (parameterAverage_integrable μ ν H hHi).congr
    (parameterAverageOn_ae_eq μ ν s hs H).symm

theorem integral_parameterAverageOn (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [SFinite ν] (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (H : Λ × Θ → ℝ) (hHi : Integrable H (μ.prod ν)) :
    (∫ x, parameterAverageOn ν s H x ∂μ) = ∫ p, H p ∂μ.prod ν := by
  rw [integral_congr_ae (parameterAverageOn_ae_eq μ ν s hs H)]
  exact (integral_prod H hHi).symm

/-- Multiplication by a parameter-only factor commutes with averaging. The
integrability hypothesis is on the actual joint integrand. -/
theorem integral_mul_parameterAverageOn (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [SFinite ν] (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (f : Λ → ℝ) (H : Λ × Θ → ℝ)
    (hfHi : Integrable (fun p ↦ f p.1 * H p) (μ.prod ν)) :
    (∫ x, f x * parameterAverageOn ν s H x ∂μ) =
      ∫ p, f p.1 * H p ∂μ.prod ν := by
  calc
    (∫ x, f x * parameterAverageOn ν s H x ∂μ) =
        ∫ x, f x * parameterAverage ν H x ∂μ := by
      apply integral_congr_ae
      filter_upwards [parameterAverageOn_ae_eq μ ν s hs H] with x hx
      rw [hx]
    _ = ∫ x, ∫ u, f x * H (x, u) ∂ν ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ (integral_const_mul (f x) (fun u ↦ H (x, u))).symm
    _ = ∫ p, f p.1 * H p ∂μ.prod ν := (integral_prod _ hfHi).symm

theorem mul_parameterAverageOn_integrable (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [SFinite ν] (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (f : Λ → ℝ) (H : Λ × Θ → ℝ)
    (hfHi : Integrable (fun p ↦ f p.1 * H p) (μ.prod ν)) :
    Integrable (fun x ↦ f x * parameterAverageOn ν s H x) μ := by
  apply hfHi.integral_prod_left.congr
  filter_upwards [hs] with x hx
  rw [integral_const_mul, parameterAverageOn_of_mem ν s H hx]
  rfl

variable [Preorder Λ]

theorem parameterAverageOn_monotoneOn (ν : Measure Θ) (s : Set Λ)
    (H : Λ × Θ → ℝ)
    (hHi : ∀ x ∈ s, Integrable (fun u ↦ H (x, u)) ν)
    (hmono : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → ∀ᵐ u ∂ν, H (x, u) ≤ H (y, u)) :
    MonotoneOn (parameterAverageOn ν s H) s := by
  intro x hx y hy hxy
  rw [parameterAverageOn_of_mem ν s H hx, parameterAverageOn_of_mem ν s H hy]
  exact integral_mono_ae (hHi x hx) (hHi y hy) (hmono x hx y hy hxy)

/-- If the two conditional moments are strictly ordered for almost every
frame, their averaged moments are strictly ordered. -/
theorem parameterAverageOn_strict_compare (ν : Measure Θ) [IsProbabilityMeasure ν]
    (s : Set Λ) (H : Λ × Θ → ℝ) {x y : Λ} (hx : x ∈ s) (hy : y ∈ s)
    (hxi : Integrable (fun u ↦ H (x, u)) ν)
    (hyi : Integrable (fun u ↦ H (y, u)) ν)
    (hstrict : ∀ᵐ u ∂ν, H (x, u) < H (y, u)) :
    parameterAverageOn ν s H x < parameterAverageOn ν s H y := by
  have hp := integral_pos_of_pos_ae (hyi.sub hxi)
    (hstrict.mono fun u hu ↦ sub_pos.mpr hu)
  change 0 < ∫ u, H (y, u) - H (x, u) ∂ν at hp
  rw [integral_sub hyi hxi] at hp
  rw [parameterAverageOn_of_mem ν s H hx, parameterAverageOn_of_mem ν s H hy]
  exact sub_pos.mp hp

end Averages

section SquareIntegrability

variable {Λ Θ : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ]

/-- Jensen's square inequality for one probability average. -/
theorem parameterAverage_sq_le (ν : Measure Θ) [IsProbabilityMeasure ν]
    (H : Λ × Θ → ℝ) (x : Λ)
    (hHi : Integrable (fun u ↦ H (x, u)) ν)
    (hH2i : Integrable (fun u ↦ H (x, u) ^ 2) ν) :
    parameterAverage ν H x ^ 2 ≤ ∫ u, H (x, u) ^ 2 ∂ν := by
  have hHHi : Integrable (fun u ↦ H (x, u) * H (x, u)) ν := by
    simpa only [pow_two] using hH2i
  have h := integral_mul_ge_mul_integral_of_comonotone hHi hHi hHHi
    (fun u v ↦ mul_self_nonneg (H (x, u) - H (x, v)))
  simpa only [parameterAverage, pow_two] using h

theorem parameterAverage_sq_integrable (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (H : Λ × Θ → ℝ) (hHm : Measurable H)
    (hHi : Integrable H (μ.prod ν))
    (hH2i : Integrable (fun p ↦ H p ^ 2) (μ.prod ν)) :
    Integrable (fun x ↦ parameterAverage ν H x ^ 2) μ := by
  apply hH2i.integral_prod_left.mono'
    ((parameterAverage_measurable ν H hHm).pow_const 2).aestronglyMeasurable
  filter_upwards [hHi.prod_right_ae, hH2i.prod_right_ae] with x hxi hx2i
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (parameterAverage ν H x))] using
    parameterAverage_sq_le ν H x hxi hx2i

theorem parameterAverage_memLp_two (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (H : Λ × Θ → ℝ) (hHm : Measurable H)
    (hHi : Integrable H (μ.prod ν))
    (hH2i : Integrable (fun p ↦ H p ^ 2) (μ.prod ν)) :
    MemLp (parameterAverage ν H) 2 μ :=
  (memLp_two_iff_integrable_sq
    (parameterAverage_measurable ν H hHm).aestronglyMeasurable).mpr
      (parameterAverage_sq_integrable μ ν H hHm hHi hH2i)

theorem parameterAverageOn_memLp_two (μ : Measure Λ) [SFinite μ]
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (s : Set Λ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (H : Λ × Θ → ℝ) (hHm : Measurable H)
    (hHi : Integrable H (μ.prod ν))
    (hH2i : Integrable (fun p ↦ H p ^ 2) (μ.prod ν)) :
    MemLp (parameterAverageOn ν s H) 2 μ :=
  (memLp_congr_ae (parameterAverageOn_ae_eq μ ν s hs H)).mpr
    (parameterAverage_memLp_two μ ν H hHm hHi hH2i)

end SquareIntegrability

/-- The strictly ordered coordinate chamber is a Borel set. This allows the
Haar-averaged test to be assigned zero outside the chamber measurably. -/
theorem orderedChamber_measurable {ι : Type*} [Fintype ι] [LinearOrder ι]
    (s : Set ℝ) (hs : MeasurableSet s) : MeasurableSet (orderedChamber (ι := ι) s) := by
  change MeasurableSet ({x : ι → ℝ | ∀ i j, i < j → x i < x j} ∩ {x | ∀ i, x i ∈ s})
  apply MeasurableSet.inter
  · simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun (_ : i < j) ↦
        measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  · simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i hs

end WishartVerification
end CanonicalSource80

section CanonicalSource81
/- Source: Wishart/SpectralRegressionMoments.lean -/



/-!
# Exact Wishart moments under the Laguerre–Haar regression source

The spectral law used here is the proved pushforward of the actual normalized
Laguerre density and normalized Haar measure.  The conditional integrand is
the explicit independent Gaussian/residual expectation from regression.  The
average is extended by zero outside the positive chamber; its equality to the
original expectation follows from the proved support of the eigenvalue law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

abbrev regressionEigenLaw (q : ℕ) (n : ℝ) : Measure (Fin q → ℝ) :=
  WishartVerification.normalizedWeight volume (Spectral.wishartEigenDensity q n)

def regressionSpectralMatrix {q : ℕ} (x : (Fin q → ℝ) × Spectral.Orth q) :
    SymmetricMatrix q :=
  Spectral.conjugate x.2 (Spectral.diagonalSym x.1)

@[fun_prop] theorem measurable_regressionSpectralMatrix (q : ℕ) :
    Measurable (@regressionSpectralMatrix q) :=
  (Spectral.continuous_conjugate q).measurable.comp
    (measurable_snd.prodMk ((Spectral.continuous_diagonalSym q).measurable.comp
      measurable_fst))

theorem measurePreserving_regressionSpectralMatrix {q : ℕ} {n : ℝ}
    (hn : (q : ℝ) - 1 < n) :
    MeasurePreserving regressionSpectralMatrix
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q)))
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) :=
  ⟨measurable_regressionSpectralMatrix q,
    Spectral.wishart_laguerre_haar_representation hn⟩

theorem integral_regressionSpectralMatrix {q : ℕ} {n : ℝ}
    (hn : (q : ℝ) - 1 < n) {f : SymmetricMatrix q → ℝ}
    (hf : AEStronglyMeasurable f
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ))) :
    (∫ S, f S ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) =
      ∫ x, f (regressionSpectralMatrix x)
        ∂(regressionEigenLaw q n).prod (haarProb (Spectral.Orth q)) := by
  have hmap := measurePreserving_regressionSpectralMatrix hn
  rw [← hmap.map_eq] at hf ⊢
  exact integral_map hmap.measurable.aemeasurable hf

def haarRegressionIntegrand {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix m → ℝ) (x : (Fin q → ℝ) × Spectral.Orth q) : ℝ :=
  spectralConditionalMoment n C K g x.1 (x.2 : Matrix (Fin q) (Fin q) ℝ)

set_option maxHeartbeats 800000 in
@[fun_prop] theorem measurable_haarRegressionIntegrand {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    Measurable (haarRegressionIntegrand n C K g) := by
  have hcoe : Measurable (fun O : Spectral.Orth q =>
      (O : Matrix (Fin q) (Fin q) ℝ)) := measurable_subtype_coe
  have hm : Measurable (fun x : (Fin q → ℝ) × Spectral.Orth q =>
      (x.1, (x.2 : Matrix (Fin q) (Fin q) ℝ))) :=
    measurable_fst.prodMk (hcoe.comp measurable_snd)
  have hf : Measurable (Function.uncurry (spectralConditionalMoment n C K g)) :=
    measurable_spectralConditionalMoment n C K hg
  change Measurable (Function.uncurry (spectralConditionalMoment n C K g) ∘
    (fun x : (Fin q → ℝ) × Spectral.Orth q =>
      (x.1, (x.2 : Matrix (Fin q) (Fin q) ℝ))))
  exact hf.comp hm

def regressionSpectralAverage {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix m → ℝ) : (Fin q → ℝ) → ℝ :=
  WishartVerification.parameterAverageOn (haarProb (Spectral.Orth q))
    (Spectral.positiveChamber q) (haarRegressionIntegrand n C K g)

@[fun_prop] theorem measurable_regressionSpectralAverage {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    Measurable (regressionSpectralAverage n C K g) :=
  WishartVerification.parameterAverageOn_measurable _ _
    (WishartVerification.orderedChamber_measurable _ measurableSet_Ioi) _
    (measurable_haarRegressionIntegrand n C K hg)

theorem regressionSpectralAverage_eq {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix m → ℝ) {lam : Fin q → ℝ}
    (hlam : lam ∈ Spectral.positiveChamber q) :
    regressionSpectralAverage n C K g lam =
      ∫ O : Spectral.Orth q, spectralConditionalMoment n C K g lam ↑O
        ∂haarProb (Spectral.Orth q) :=
  WishartVerification.parameterAverageOn_of_mem _ _ _ hlam

theorem ae_regressionConditionalMoment_spectral {q m : ℕ} {n : ℝ}
    (hn : (q : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    (fun x => regressionConditionalMoment n C K g (regressionSpectralMatrix x)) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      haarRegressionIntegrand n C K g := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
  exact regressionConditionalMoment_eq_spectral n hC K ↑x.2
    (Spectral.orth_mul_transpose x.2) x.1 (fun i => (hx.2 i).le)
    (regressionSpectralMatrix x)
    (Matrix.coe_symmetricCongruenceLinearMap_apply _ _) hg

theorem ae_regressionSpectralMatrix_det_rpow {q : ℕ} {n : ℝ}
    (hn : (q : ℝ) - 1 < n) (η : ℝ) :
    (fun x => (regressionSpectralMatrix x : Matrix (Fin q) (Fin q) ℝ).det ^ η) =ᵐ[
      (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      (fun x => WishartVerification.spectralDetPower η x.1) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (Spectral.ae_laguerreLaw_mem_chamber hn)] with x hx
  rw [regressionSpectralMatrix, Spectral.det_conjugate]
  exact (WishartVerification.spectralDetPower_eq_diagonal_det_rpow η x.1 hx.2).symm

theorem integrable_haarRegressionIntegrand {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hgi : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (haarRegressionIntegrand n C K g)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  exact ((measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    (integrable_regressionConditionalMoment hn K hC hgi)).congr
      (ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm)

theorem integrable_spectralDetPower_mul_haarRegressionIntegrand {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (η : ℝ) {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X =>
      (principalSymmetricBlock (Fin.castAdd m) X : Matrix (Fin q) (Fin q) ℝ).det ^ η *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun x => WishartVerification.spectralDetPower η x.1 *
      haarRegressionIntegrand n C K g x)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  have hcond := integrable_regression_selected_mul_conditional hn K hC
    (h := fun S : SymmetricMatrix q => (S : Matrix (Fin q) (Fin q) ℝ).det ^ η)
    (g := g) hjoint
  apply ((measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    hcond).congr
  filter_upwards [ae_regressionSpectralMatrix_det_rpow hnq η,
    ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
  exact congrArg₂ (· * ·) hx hy

theorem integral_regression_selected_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) (η : ℝ) :
    (∫ X, (principalSymmetricBlock (Fin.castAdd m) X :
      Matrix (Fin q) (Fin q) ℝ).det ^ η
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, WishartVerification.spectralDetPower η lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hd : Measurable (fun S : SymmetricMatrix q =>
      (S : Matrix (Fin q) (Fin q) ℝ).det ^ η) :=
    continuous_subtype_val.matrix_det.measurable.pow_const _
  rw [integral_regression_selected hn K hC hd,
    integral_regressionSpectralMatrix hnq hd.aestronglyMeasurable,
    integral_congr_ae (ae_regressionSpectralMatrix_det_rpow hnq η), integral_fun_fst]
  simp only [probReal_univ, one_smul]

theorem integral_regression_joint_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (η : ℝ) {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X =>
      (principalSymmetricBlock (Fin.castAdd m) X : Matrix (Fin q) (Fin q) ℝ).det ^ η *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, (principalSymmetricBlock (Fin.castAdd m) X :
      Matrix (Fin q) (Fin q) ℝ).det ^ η *
        g (principalSymmetricBlock (Fin.natAdd q) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, WishartVerification.spectralDetPower η lam * regressionSpectralAverage n C K g lam
        ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hcond := integrable_regression_selected_mul_conditional hn K hC
    (h := fun S : SymmetricMatrix q => (S : Matrix (Fin q) (Fin q) ℝ).det ^ η)
    (g := g) hjoint
  rw [integral_regression_selected_mul_remaining hn K hC
      (h := fun S : SymmetricMatrix q => (S : Matrix (Fin q) (Fin q) ℝ).det ^ η)
      (g := g) hjoint,
    integral_regressionSpectralMatrix hnq hcond.aestronglyMeasurable]
  have heq : (fun x =>
      (regressionSpectralMatrix x : Matrix (Fin q) (Fin q) ℝ).det ^ η *
        regressionConditionalMoment n C K g (regressionSpectralMatrix x)) =ᵐ[
        (regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))]
      (fun x => WishartVerification.spectralDetPower η x.1 *
        haarRegressionIntegrand n C K g x) := by
    filter_upwards [ae_regressionSpectralMatrix_det_rpow hnq η,
      ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm] with x hx hy
    exact congrArg₂ (· * ·) hx hy
  rw [integral_congr_ae heq]
  exact (WishartVerification.integral_mul_parameterAverageOn _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_spectralDetPower_mul_haarRegressionIntegrand hn K hC η hgm hjoint)).symm

theorem integral_regression_remaining_spectral {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hgi : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, g (principalSymmetricBlock (Fin.natAdd q) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ lam, regressionSpectralAverage n C K g lam ∂regressionEigenLaw q n := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  rw [integral_regression_remaining hn K hC hgi,
    integral_regressionSpectralMatrix hnq
      (integrable_regressionConditionalMoment hn K hC hgi).aestronglyMeasurable,
    integral_congr_ae (ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm)]
  exact (WishartVerification.integral_parameterAverageOn _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _
    (integrable_haarRegressionIntegrand hn K hC hgm hgi)).symm

theorem integrable_regressionSpectralAverage {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hgi : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (regressionSpectralAverage n C K g) (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  exact WishartVerification.parameterAverageOn_integrable _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _
    (integrable_haarRegressionIntegrand hn K hC hgm hgi)

theorem integrable_spectralDetPower_mul_regressionSpectralAverage {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (η : ℝ) {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hjoint : Integrable (fun X =>
      (principalSymmetricBlock (Fin.castAdd m) X : Matrix (Fin q) (Fin q) ℝ).det ^ η *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun lam => WishartVerification.spectralDetPower η lam *
      regressionSpectralAverage n C K g lam) (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  exact WishartVerification.mul_parameterAverageOn_integrable _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _ _
    (integrable_spectralDetPower_mul_haarRegressionIntegrand hn K hC η hgm hjoint)

theorem integrable_sq_regressionConditionalMoment {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hgi : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C)))
    (hg2i : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X) ^ 2)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun S => regressionConditionalMoment n C K g S ^ 2)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  have hsource := integrable_regression_joint_source hn K hC
    (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hgi)
  have hsource2 := integrable_regression_joint_source hn K hC
    (h := fun _ => 1) (g := fun S => g S ^ 2) (by simpa only [one_mul] using hg2i)
  exact WishartVerification.parameterAverage_sq_integrable _ _
    (fun x : RegressionData q m => g (regressionTailModel K x.1 x.2))
    (hgm.comp (measurable_regressionTailModel K))
    (by simpa only [one_mul] using hsource)
    (by simpa only [one_mul] using hsource2)

theorem memLp_regressionSpectralAverage_two {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ} (hgm : Measurable g)
    (hgi : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C)))
    (hg2i : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X) ^ 2)
      (nonsingularWishartMeasure n (regressionScale K C))) :
    MemLp (regressionSpectralAverage n C K g) 2 (regressionEigenLaw q n) := by
  have hnq : (q : ℝ) - 1 < n := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hn
    linarith
  letI := Spectral.laguerreLaw_isProbability hnq
  have hsq := (measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
    (integrable_sq_regressionConditionalMoment hn K hC hgm hgi hg2i)
  have hsq' : Integrable (fun x => haarRegressionIntegrand n C K g x ^ 2)
      ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) :=
    hsq.congr ((ae_regressionConditionalMoment_spectral hnq hC.posSemidef K hgm).fun_comp
      (fun r : ℝ => r ^ 2))
  exact WishartVerification.parameterAverageOn_memLp_two _ _ _
    (Spectral.ae_laguerreLaw_mem_chamber hnq) _
    (measurable_haarRegressionIntegrand n C K hgm)
    (integrable_haarRegressionIntegrand hn K hC hgm hgi) hsq'

end Wishart
end
end CanonicalSource81

section CanonicalSource82
/- Source: Wishart/PrincipalSpectralMoments.lean -/



open scoped Classical ENNReal
open MeasureTheory

/-!
# Exact spectral moment identities for arbitrary principal partitions

The remaining spectral function is the actual Haar average of the independent
regression-source moment. All three moment identities and their integrability
are obtained from the concrete normalization and spectral law. The only missing
input to the subsequent FKG split is the analytic monotonicity of this explicitly
defined remaining spectral function.
-/

namespace WishartVerification

noncomputable section

theorem allFiniteMoments_spectralDetPower {q : ℕ} {α η : ℝ}
    (hα : (q : ℝ) - 1 < α) (hη : 0 ≤ η) :
    HasAllFiniteMoments (spectralDetPower (ι := Fin q) η) (Wishart.regressionEigenLaw q α) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin q) (Fin q) ℝ)) Matrix.PosDef.one hα
  letI := Wishart.Spectral.laguerreLaw_isProbability hα
  have hdet : HasAllFiniteMoments (matrixDetPower (q := q) η)
      (TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin q) (Fin q) ℝ)) :=
    (HasAllFiniteMoments.det
      (fun X : SymmetricMatrix q ↦ (X : Matrix (Fin q) (Fin q) ℝ))
      (fun i j ↦ allFiniteMoments_wishart_entry i j)).rpow hη
  have hprod := (hdet.comp_measurePreserving
    (Wishart.measurePreserving_regressionSpectralMatrix hα)).congr_ae
      (Wishart.ae_regressionSpectralMatrix_det_rpow hα η)
  exact HasAllFiniteMoments.of_comp_measurePreserving measurePreserving_fst
    (spectralDetPower_measurable η) hprod

variable {p d : ℕ}

def principalSpectralAverage (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    (Fin (selectedRank P j) → ℝ) → ℝ :=
  Wishart.regressionSpectralAverage α (principalResidualScale P Sigma j)
    (principalCrossScale P Sigma j) (remainingPrincipalTest P ν J j)

theorem principalSpectralAverage_measurable (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (principalSpectralAverage α Sigma P ν J j) :=
  Wishart.measurable_regressionSpectralAverage _ _ _ (remainingPrincipalTest_measurable P ν J j)

/-- The three expectations in a selected principal split are exactly the
three expectations of the explicit selected and remaining spectral tests. -/
theorem principal_spectral_moments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    principalMoment α Sigma P ν J = principalMomentScale P Sigma ν j *
      (∫ lam, spectralDetPower (ν j) lam * principalSpectralAverage α Sigma P ν J j lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    principalMoment α Sigma P ν {j} = principalMomentScale P Sigma ν j *
      (∫ lam, spectralDetPower (ν j) lam ∂Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    principalMoment α Sigma P ν (J.erase j) =
      (∫ lam, principalSpectralAverage α Sigma P ν J j lam
        ∂Wishart.regressionEigenLaw (selectedRank P j) α) := by
  have hn := principal_regression_shape P hα j
  have hC := principalResidualScale_posDef P hSigma j
  have hgm := remainingPrincipalTest_measurable P ν J j
  obtain ⟨_, hgi, hji⟩ := principal_normalization_allFiniteMoments P hSigma hα ν hν J j hj
  obtain ⟨hjoint, hselected, hremaining⟩ := principal_normalization_moments P hSigma hα ν J j hj
  have hjointSpec := Wishart.integral_regression_joint_spectral hn
    (principalCrossScale P Sigma j) hC (ν j) hgm hji.integrable
  have hselectedSpec := Wishart.integral_regression_selected_spectral hn
    (principalCrossScale P Sigma j) hC (ν j)
  have hremainingSpec := Wishart.integral_regression_remaining_spectral hn
    (principalCrossScale P Sigma j) hC hgm hgi.integrable
  exact ⟨hjoint.trans (congrArg (fun r ↦ principalMomentScale P Sigma ν j * r) hjointSpec),
    hselected.trans (congrArg (fun r ↦ principalMomentScale P Sigma ν j * r) hselectedSpec),
    hremaining.trans hremainingSpec⟩

theorem principal_spectral_integrability
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    Integrable (spectralDetPower (ν j)) (Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    Integrable (principalSpectralAverage α Sigma P ν J j)
      (Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    Integrable (fun lam ↦ spectralDetPower (ν j) lam * principalSpectralAverage α Sigma P ν J j lam)
      (Wishart.regressionEigenLaw (selectedRank P j) α) := by
  have hn := principal_regression_shape P hα j
  have hC := principalResidualScale_posDef P hSigma j
  have hgm := remainingPrincipalTest_measurable P ν J j
  obtain ⟨_, hgi, hji⟩ := principal_normalization_allFiniteMoments P hSigma hα ν hν J j hj
  exact ⟨(allFiniteMoments_spectralDetPower (principal_spectral_shape P hα j) (hν j)).integrable,
    Wishart.integrable_regressionSpectralAverage hn (principalCrossScale P Sigma j) hC hgm hgi.integrable,
    Wishart.integrable_spectralDetPower_mul_regressionSpectralAverage hn
      (principalCrossScale P Sigma j) hC (ν j) hgm hji.integrable⟩

theorem principal_spectral_memLp_two
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    MemLp (spectralDetPower (ν j)) 2 (Wishart.regressionEigenLaw (selectedRank P j) α) ∧
    MemLp (principalSpectralAverage α Sigma P ν J j) 2
      (Wishart.regressionEigenLaw (selectedRank P j) α) := by
  have hn := principal_regression_shape P hα j
  have hC := principalResidualScale_posDef P hSigma j
  have hgm := remainingPrincipalTest_measurable P ν J j
  have hgi := (principal_normalization_allFiniteMoments P hSigma hα ν hν J j hj).2.1
  have hg2 := hgi 2 (by norm_num)
  have hg2i := (memLp_two_iff_integrable_sq hg2.aestronglyMeasurable).mp hg2
  exact ⟨allFiniteMoments_spectralDetPower (principal_spectral_shape P hα j) (hν j) 2 (by norm_num),
    Wishart.memLp_regressionSpectralAverage_two hn (principalCrossScale P Sigma j) hC hgm
      hgi.integrable hg2i⟩

/-- This bridge now has only the remaining test's two analytic order premises.
The law, all three moment identities, scale factor, and integrability have been
derived from the original principal Wishart parameters. -/
theorem principal_split_of_actual_spectral_monotonicity
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (hF0 : ∀ lam, 0 ≤ principalSpectralAverage α Sigma P ν J j lam)
    (hFmono : MonotoneOn (principalSpectralAverage α Sigma P ν J j)
      (orderedChamber (Set.Ioi 0))) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
      principalMoment α Sigma P ν J := by
  have hnormal := Wishart.Spectral.identityEigenLaw_normalized_density
    (principal_spectral_shape P hα j)
  obtain ⟨hselectedInt, hremainingInt, hjointInt⟩ :=
    principal_spectral_integrability P hSigma hα ν hν J j hj
  obtain ⟨hjoint, hselected, hremaining⟩ := principal_spectral_moments P hSigma hα ν hν J j hj
  exact principal_split_of_spectral_representation α Sigma P ν J j hj (hν j)
    (fun _ ↦ Wishart.Spectral.laguerreWeight (selectedRank P j) α) 1 (by norm_num)
    (fun _ ↦ Wishart.Spectral.measurable_laguerreWeight _ _)
    (fun _ ↦ Wishart.Spectral.laguerreWeight_nonneg _ _)
    hnormal.1 hnormal.2.1 (principalSpectralAverage α Sigma P ν J j)
    (principalSpectralAverage_measurable α Sigma P ν J j) hF0 hFmono
    hselectedInt hremainingInt hjointInt (principalMomentScale P Sigma ν j)
    (principalMomentScale_pos P hSigma ν j).le hjoint hselected hremaining

/-- A dimension-generic strict association interface. Strict one-coordinate
updates give the last-coordinate condition of Lemma 2.1, without requiring
the caller to identify a positive dimension syntactically as a successor. -/
theorem spectral_association_strict_of_updates {q : ℕ} (hq : 0 < q)
    (w : Fin q → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hwm : ∀ i, Measurable (w i)) (hw0 : ∀ i t, 0 ≤ w i t)
    (hZ0 : (∫⁻ x : Fin q → ℝ, ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ 0)
    (hZtop : (∫⁻ x : Fin q → ℝ, ENNReal.ofReal (chamberWeight (Set.Ioi 0) w β x)) ≠ ∞)
    (η : ℝ) (hη : 0 < η) (F : (Fin q → ℝ) → ℝ)
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFmono : MonotoneOn F (orderedChamber (Set.Ioi 0)))
    (hFstrict : ∀ x i a b, a < b →
      Function.update x i a ∈ orderedChamber (Set.Ioi 0) →
      Function.update x i b ∈ orderedChamber (Set.Ioi 0) →
      F (Function.update x i a) < F (Function.update x i b))
    (hf2 : MemLp (spectralDetPower η) 2
      (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)))
    (hF2 : MemLp F 2 (normalizedWeight volume (chamberWeight (Set.Ioi 0) w β))) :
    (∫ x, spectralDetPower η x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) *
        (∫ x, F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β)) <
      ∫ x, spectralDetPower η x * F x ∂normalizedWeight volume (chamberWeight (Set.Ioi 0) w β) := by
  cases q with
  | zero => exact (Nat.not_lt_zero _ hq).elim
  | succ n =>
      apply lemma_2_1_strict_association (Set.Ioi 0) measurableSet_Ioi w β hβ hwm hw0
        hZ0 hZtop (spectralDetPower η) F (spectralDetPower_measurable η) hFm
        (spectralDetPower_nonneg η) hF0 ((spectralDetPower_monotone η hη.le).monotoneOn _) hFmono
        (spectralDetPower_strict_last η hη) _ hf2 hF2
      intro x a b hab ha hb
      have h := hFstrict (appendLast x a) (Fin.last n) a b hab
        (by simpa only [appendLast, Fin.update_snoc_last] using ha)
        (by simpa only [appendLast, Fin.update_snoc_last] using hb)
      simpa only [appendLast, Fin.update_snoc_last] using h

/-- Exact strict selected principal split from strict coordinate updates of
the actual averaged conditional moment. All measure and moment obligations are
discharged here; the remaining strict-order premise is the Haar/radial step. -/
theorem principal_strict_split_of_actual_spectral_updates
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) (hνj : 0 < ν j)
    (hF0 : ∀ lam, 0 ≤ principalSpectralAverage α Sigma P ν J j lam)
    (hFmono : MonotoneOn (principalSpectralAverage α Sigma P ν J j)
      (orderedChamber (Set.Ioi 0)))
    (hFstrict : ∀ x i a b, a < b →
      Function.update x i a ∈ orderedChamber (Set.Ioi 0) →
      Function.update x i b ∈ orderedChamber (Set.Ioi 0) →
      principalSpectralAverage α Sigma P ν J j (Function.update x i a) <
        principalSpectralAverage α Sigma P ν J j (Function.update x i b)) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) <
      principalMoment α Sigma P ν J := by
  have hnormal := Wishart.Spectral.identityEigenLaw_normalized_density
    (principal_spectral_shape P hα j)
  obtain ⟨hf2, hF2⟩ := principal_spectral_memLp_two P hSigma hα ν hν J j hj
  have hstrict := spectral_association_strict_of_updates (selectedRank_pos P j)
    (fun _ ↦ Wishart.Spectral.laguerreWeight (selectedRank P j) α) 1 (by norm_num)
    (fun _ ↦ Wishart.Spectral.measurable_laguerreWeight _ _)
    (fun _ ↦ Wishart.Spectral.laguerreWeight_nonneg _ _)
    hnormal.1 hnormal.2.1 (ν j) hνj (principalSpectralAverage α Sigma P ν J j)
    (principalSpectralAverage_measurable α Sigma P ν J j) hF0 hFmono hFstrict hf2 hF2
  obtain ⟨hjoint, hselected, hremaining⟩ := principal_spectral_moments P hSigma hα ν hν J j hj
  rw [hselected, hremaining, hjoint, mul_assoc]
  exact mul_lt_mul_of_pos_left hstrict (principalMomentScale_pos P hSigma ν j)

end

end WishartVerification
end CanonicalSource82

section CanonicalSource83
/- Source: Wishart/GaussianStein.lean -/



/-!
# Gaussian integration by parts from translation of the actual Gaussian law

The covariance is arbitrary positive definite.  The proof uses the exact
density ratio and supplies both dominated differentiation witnesses for a
compactly supported `C¹` test function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Filter Topology Matrix
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianShiftDensityRatio (C : Matrix ι ι ℝ) (h : EuclideanSpace ℝ ι)
    (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (t * ⟪h, C⁻¹.toEuclideanLin x⟫ -
    t ^ 2 * ⟪h, C⁻¹.toEuclideanLin h⟫ / 2)

@[simp] theorem gaussianShiftDensityRatio_zero (C : Matrix ι ι ℝ)
    (h x : EuclideanSpace ℝ ι) : gaussianShiftDensityRatio C h 0 x = 1 := by
  simp [gaussianShiftDensityRatio]

@[fun_prop] theorem continuous_gaussianShiftDensityRatio (C : Matrix ι ι ℝ)
    (h : EuclideanSpace ℝ ι) :
    Continuous (Function.uncurry (gaussianShiftDensityRatio C h)) := by
  unfold gaussianShiftDensityRatio
  fun_prop

theorem gaussianShiftDensityRatio_pos (C : Matrix ι ι ℝ)
    (h : EuclideanSpace ℝ ι) (t : ℝ) (x : EuclideanSpace ℝ ι) :
    0 < gaussianShiftDensityRatio C h t x := Real.exp_pos _

theorem gaussian_quadratic_shift {C : Matrix ι ι ℝ} (hC : C.PosDef)
    (h x : EuclideanSpace ℝ ι) (t : ℝ) :
    ⟪x - t • h, C⁻¹.toEuclideanLin (x - t • h)⟫ =
      ⟪x, C⁻¹.toEuclideanLin x⟫ - 2 * t * ⟪h, C⁻¹.toEuclideanLin x⟫ +
        t ^ 2 * ⟪h, C⁻¹.toEuclideanLin h⟫ := by
  have hsymm := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC.inv.isHermitian
  have hcross : ⟪x, C⁻¹.toEuclideanLin h⟫ = ⟪h, C⁻¹.toEuclideanLin x⟫ :=
    (real_inner_comm _ _).trans (hsymm h x)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hcross]
  ring

theorem multivariateGaussianPDFReal_shift_ratio {C : Matrix ι ι ℝ}
    (hC : C.PosDef) (h x : EuclideanSpace ℝ ι) (t : ℝ) :
    multivariateGaussianPDFReal (t • h) C x =
      gaussianShiftDensityRatio C h t x * multivariateGaussianPDFReal 0 C x := by
  rw [multivariateGaussianPDFReal_def, multivariateGaussianPDFReal_def]
  simp only [sub_zero, gaussian_quadratic_shift hC]
  rw [show -(⟪x, C⁻¹.toEuclideanLin x⟫ - 2 * t * ⟪h, C⁻¹.toEuclideanLin x⟫ +
      t ^ 2 * ⟪h, C⁻¹.toEuclideanLin h⟫) / 2 =
      (t * ⟪h, C⁻¹.toEuclideanLin x⟫ - t ^ 2 * ⟪h, C⁻¹.toEuclideanLin h⟫ / 2) +
        -⟪x, C⁻¹.toEuclideanLin x⟫ / 2 by ring, Real.exp_add]
  unfold gaussianShiftDensityRatio
  ring

theorem multivariateGaussian_shift_ratio {C : Matrix ι ι ℝ}
    (hC : C.PosDef) (h : EuclideanSpace ℝ ι) (t : ℝ) :
    (multivariateGaussian 0 C).map (fun x => x + t • h) =
      (multivariateGaussian 0 C).withDensity
        (fun x => ENNReal.ofReal (gaussianShiftDensityRatio C h t x)) := by
  have hmap : (multivariateGaussian 0 C).map (fun x => x + t • h) =
      multivariateGaussian (t • h) C := by
    simpa [add_comm] using map_add_smul_multivariateGaussian
      (0 : EuclideanSpace ℝ ι) hC.posSemidef (t • h) 1
  rw [hmap, multivariateGaussian_eq_withDensity hC,
    multivariateGaussian_eq_withDensity hC,
    ← withDensity_mul _ (measurable_multivariateGaussianPDF 0 C) (by fun_prop)]
  congr 1
  funext x
  simp only [multivariateGaussianPDF_def, Pi.mul_apply]
  change ENNReal.ofReal (multivariateGaussianPDFReal (t • h) C x) =
    ENNReal.ofReal (multivariateGaussianPDFReal 0 C x) *
      ENNReal.ofReal (gaussianShiftDensityRatio C h t x)
  rw [multivariateGaussianPDFReal_shift_ratio hC]
  rw [ENNReal.ofReal_mul (gaussianShiftDensityRatio_pos C h t x).le, mul_comm]

theorem hasDerivAt_gaussianShiftDensityRatio (C : Matrix ι ι ℝ)
    (h x : EuclideanSpace ℝ ι) (t : ℝ) :
    HasDerivAt (fun r => gaussianShiftDensityRatio C h r x)
      ((⟪h, C⁻¹.toEuclideanLin x⟫ - t * ⟪h, C⁻¹.toEuclideanLin h⟫) *
        gaussianShiftDensityRatio C h t x) t := by
  have hd := (((hasDerivAt_id t).mul_const ⟪h, C⁻¹.toEuclideanLin x⟫).sub
    (((hasDerivAt_pow 2 t).mul_const ⟪h, C⁻¹.toEuclideanLin h⟫).div_const 2)).exp
  convert hd using 1 <;> dsimp [gaussianShiftDensityRatio] <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem gaussian_stein_compact {C : Matrix ι ι ℝ} (hC : C.PosDef)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : ContDiff ℝ 1 g) (hcpt : HasCompactSupport g)
    (h : EuclideanSpace ℝ ι) :
    (∫ x, ⟪h, C⁻¹.toEuclideanLin x⟫ * g x ∂multivariateGaussian 0 C) =
      ∫ x, fderiv ℝ g x h ∂multivariateGaussian 0 C := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) C
  let F : ℝ → EuclideanSpace ℝ ι → ℝ := fun t x => g (x + t • h)
  let F' : ℝ → EuclideanSpace ℝ ι → ℝ := fun t x => fderiv ℝ g (x + t • h) h
  let G : ℝ → EuclideanSpace ℝ ι → ℝ := fun t x => gaussianShiftDensityRatio C h t x * g x
  let G' : ℝ → EuclideanSpace ℝ ι → ℝ := fun t x =>
    ((⟪h, C⁻¹.toEuclideanLin x⟫ - t * ⟪h, C⁻¹.toEuclideanLin h⟫) *
      gaussianShiftDensityRatio C h t x) * g x
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hlin : Continuous (C⁻¹.toEuclideanLin) :=
    LinearMap.continuous_of_finiteDimensional _
  have hρ (t : ℝ) : Continuous (gaussianShiftDensityRatio C h t) := by
    simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using
      (continuous_gaussianShiftDensityRatio C h).comp
        (continuous_const.prodMk continuous_id)
  have hgD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := hgD.norm.bddAbove_range_of_hasCompactSupport (hcpt.fderiv ℝ).norm
  have hFderiv (x : EuclideanSpace ℝ ι) (t : ℝ) : HasDerivAt (fun r => F r x) (F' t x) t := by
    simpa only [F, F', Function.comp_def, one_smul, id_eq] using
      (hgdiff (x + t • h)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const h).const_add x)
  let dF : IntegralDerivativeData μ F F' 0 := {
    neighborhood := Set.univ
    neighborhood_mem := Filter.univ_mem
    bound := fun _ => max M 0 * ‖h‖
    measurable_near := Filter.Eventually.of_forall fun t => by
      dsimp [F]; exact (hg.continuous.comp (by fun_prop)).aestronglyMeasurable
    integrable_at := by simpa [F] using hg.continuous.integrable_of_hasCompactSupport hcpt
    derivative_measurable := by
      simpa [F'] using (hgD.clm_apply
        (show Continuous (fun _ : EuclideanSpace ℝ ι => h) from continuous_const)).aestronglyMeasurable
    derivative_bound := Filter.Eventually.of_forall fun x t _ =>
      ((fderiv ℝ g (x + t • h)).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right ((hM ⟨x + t • h, rfl⟩).trans (le_max_left _ _))
          (norm_nonneg h))
    integrable_bound := integrable_const _
    has_derivative := Filter.Eventually.of_forall fun x t _ => hFderiv x t }
  obtain ⟨dG⟩ : Nonempty (IntegralDerivativeData μ G G' 0) :=
    integralDerivativeData_of_compact_derivative_support (by norm_num : (0 : ℝ) < 1)
      hcpt
      (Filter.Eventually.of_forall fun t => (hρ t |>.mul hgc).aestronglyMeasurable)
      (by simpa [G] using hg.continuous.integrable_of_hasCompactSupport hcpt)
      (by
        have hc : Continuous (G' 0) := by
          dsimp only [G']
          simpa only [Pi.sub_def, Pi.mul_def] using
            (((continuous_const.inner hlin).sub
              (continuous_const.mul continuous_const)).mul (hρ 0)).mul hgc
        exact hc.aestronglyMeasurable)
      (by
        have hc : Continuous (Function.uncurry G') := by
          change Continuous (fun tx : ℝ × EuclideanSpace ℝ ι =>
            ((⟪h, C⁻¹.toEuclideanLin tx.2⟫ - tx.1 * ⟪h, C⁻¹.toEuclideanLin h⟫) *
              gaussianShiftDensityRatio C h tx.1 tx.2) * g tx.2)
          simpa only [Function.comp_def, Function.uncurry_def, Pi.sub_def, Pi.mul_def,
            id_eq] using
            (((continuous_const.inner (hlin.comp continuous_snd)).sub
              (continuous_fst.mul continuous_const)).mul
                (continuous_gaussianShiftDensityRatio C h)).mul
                  (hgc.comp continuous_snd)
        exact hc.continuousOn)
      (fun t _ x hx => by simp [G', image_eq_zero_of_notMem_tsupport hx])
      (fun x t _ => by
        simpa [G, G'] using (hasDerivAt_gaussianShiftDensityRatio C h x t).mul_const (g x))
  have hidentity := transport_derivative_identity hg.continuous.measurable
    (Filter.Eventually.of_forall fun t => ⟨by fun_prop, by fun_prop,
      Filter.Eventually.of_forall fun x => (gaussianShiftDensityRatio_pos C h t x).le,
      multivariateGaussian_shift_ratio hC h t⟩) dF dG
  simpa [F', G'] using hidentity.symm

end WishartVerification
end
end CanonicalSource83

section CanonicalSource84
/- Source: Wishart/WishartDensityRatio.lean -/



/-!
# Scale changes and the Wishart score

The ratio is the actual Radon--Nikodym density between two nonsingular Wishart
laws.  Its derivative is proved from the determinant and inverse Fréchet
derivatives.  Subsequent integration-by-parts applications still have to supply
the domination witnesses required by `transport_derivative_identity`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open scoped Matrix Matrix.Norms.Operator ENNReal

namespace WishartVerification

variable {p : ℕ}

def wishartScaleDensityRatio (ν : ℝ) (S T : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) : ℝ :=
  Real.exp ((ν / 2) * (Real.log S.det - Real.log T.det) -
    Matrix.trace ((T⁻¹ - S⁻¹) * (X : Matrix (Fin p) (Fin p) ℝ)) / 2)

theorem wishartScaleDensityRatio_pos (ν : ℝ) (S T : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) : 0 < wishartScaleDensityRatio ν S T X :=
  Real.exp_pos _

@[simp] theorem wishartScaleDensityRatio_self (ν : ℝ) (S : Matrix (Fin p) (Fin p) ℝ)
    (X : SymmetricMatrix p) : wishartScaleDensityRatio ν S S X = 1 := by
  simp [wishartScaleDensityRatio]

@[fun_prop] theorem measurable_wishartScaleDensityRatio (ν : ℝ)
    (S T : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (wishartScaleDensityRatio ν S T) := by
  unfold wishartScaleDensityRatio
  fun_prop

theorem wishartScaleDensityRatio_eq_quotient {S T : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hT : T.PosDef) (ν : ℝ) (X : SymmetricMatrix p) :
    wishartScaleDensityRatio ν S T X =
      (S.det ^ (ν / 2) / T.det ^ (ν / 2)) *
        (Real.exp (-Matrix.trace (T⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2) /
          Real.exp (-Matrix.trace (S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2)) := by
  rw [wishartScaleDensityRatio, Matrix.sub_mul, Matrix.trace_sub]
  have hexp : (ν / 2) * (Real.log S.det - Real.log T.det) -
      (Matrix.trace (T⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) -
        Matrix.trace (S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ))) / 2 =
      (Real.log S.det * (ν / 2) - Real.log T.det * (ν / 2)) +
        (-Matrix.trace (T⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2 -
          -Matrix.trace (S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2) := by ring
  rw [hexp, Real.exp_add, Real.exp_sub, Real.exp_sub,
    ← Real.rpow_def_of_pos hS.det_pos, ← Real.rpow_def_of_pos hT.det_pos]

theorem nonsingularWishartPDFReal_scale_ratio {ν : ℝ}
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosDef)
    (hν : (p : ℝ) - 1 < ν) (X : SymmetricMatrix p) :
    nonsingularWishartPDFReal ν T X =
      wishartScaleDensityRatio ν S T X * nonsingularWishartPDFReal ν S X := by
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef
  · rw [nonsingularWishartPDFReal_of_posDef ν T hX,
      nonsingularWishartPDFReal_of_posDef ν S hX,
      wishartScaleDensityRatio_eq_quotient hS hT]
    have h2 : (2 : ℝ) ^ (ν * (p : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    have hSd : S.det ^ (ν / 2) ≠ 0 := (Real.rpow_pos_of_pos hS.det_pos _).ne'
    have hTd : T.det ^ (ν / 2) ≠ 0 := (Real.rpow_pos_of_pos hT.det_pos _).ne'
    have hG : multivariateGamma p (ν / 2) ≠ 0 := multivariateGamma_ne_zero (by linarith)
    field_simp
  · simp [nonsingularWishartPDFReal_of_not_posDef ν T hX,
      nonsingularWishartPDFReal_of_not_posDef ν S hX]

theorem nonsingularWishartMeasure_scale_ratio {ν : ℝ}
    {S T : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hT : T.PosDef)
    (hν : (p : ℝ) - 1 < ν) :
    nonsingularWishartMeasure ν T =
      (nonsingularWishartMeasure ν S).withDensity
        (fun X => ENNReal.ofReal (wishartScaleDensityRatio ν S T X)) := by
  rw [nonsingularWishartMeasure_of_posDef hS hν,
    nonsingularWishartMeasure_of_posDef hT hν,
    ← withDensity_mul _ (measurable_nonsingularWishartPDF ν S)
      (by fun_prop)]
  congr 1
  funext X
  rw [nonsingularWishartPDF_def, Pi.mul_apply, nonsingularWishartPDF_def,
    nonsingularWishartPDFReal_scale_ratio hS hT hν]
  rw [ENNReal.ofReal_mul (wishartScaleDensityRatio_pos ν S T X).le, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_wishartScaleDensityRatio {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (ν : ℝ) (X : SymmetricMatrix p)
    {T : ℝ → Matrix (Fin p) (Fin p) ℝ} {H : Matrix (Fin p) (Fin p) ℝ}
    (hT : HasDerivAt T H 0) (hT0 : T 0 = S) :
    HasDerivAt (fun t => wishartScaleDensityRatio ν S (T t) X)
      (-(ν / 2) * Matrix.trace (S⁻¹ * H) +
        Matrix.trace (S⁻¹ * H * S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2) 0 := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hlog := (hasFDerivAt_logdet hunit).comp_hasDerivAt_of_eq 0 hT hT0.symm
  have hinv := (hasFDerivAt_trace_inverse_mul hunit
    (X : Matrix (Fin p) (Fin p) ℝ)).comp_hasDerivAt_of_eq 0 hT hT0.symm
  have hlog := hlog.congr_deriv (traceLeftCLM_apply S⁻¹ H)
  have hinv := hinv.congr_deriv (logdetSecondCLM_apply S (X : Matrix (Fin p) (Fin p) ℝ) H)
  have hd := (((hlog.const_sub (Real.log S.det)).const_mul (ν / 2)).sub
    ((hinv.sub_const (Matrix.trace (S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)))).div_const 2)).exp
  simp only [Function.comp_apply, Pi.sub_apply, traceLeftCLM_apply,
    logdetSecondCLM_apply] at hd
  convert hd using 1
  · funext t
    simp only [wishartScaleDensityRatio, Matrix.sub_mul, Matrix.trace_sub,
      Function.comp_apply, Pi.sub_apply]
  · simp [hT0, traceLeftCLM_apply, logdetSecondCLM_apply]
    ring

set_option backward.isDefEq.respectTransparency false in
/-- The density ratio along an arbitrary differentiable invertible scale path.
This form supplies the derivative throughout a neighbourhood, as required for
dominated differentiation, rather than only at its centre. -/
theorem hasDerivAt_wishartScaleDensityRatio_general
    (S : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (X : SymmetricMatrix p)
    {T : ℝ → Matrix (Fin p) (Fin p) ℝ} {H : Matrix (Fin p) (Fin p) ℝ} {t : ℝ}
    (hT : HasDerivAt T H t) (hunit : IsUnit (T t).det) :
    HasDerivAt (fun s => wishartScaleDensityRatio ν S (T s) X)
      ((-(ν / 2) * Matrix.trace ((T t)⁻¹ * H) +
          Matrix.trace ((T t)⁻¹ * H * (T t)⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2) *
        wishartScaleDensityRatio ν S (T t) X) t := by
  have hlog := (hasFDerivAt_logdet hunit).comp_hasDerivAt t hT
  have hinv := (hasFDerivAt_trace_inverse_mul hunit
    (X : Matrix (Fin p) (Fin p) ℝ)).comp_hasDerivAt t hT
  have hlog := hlog.congr_deriv (traceLeftCLM_apply (T t)⁻¹ H)
  have hinv := hinv.congr_deriv
    (logdetSecondCLM_apply (T t) (X : Matrix (Fin p) (Fin p) ℝ) H)
  have hd := (((hlog.const_sub (Real.log S.det)).const_mul (ν / 2)).sub
    ((hinv.sub_const (Matrix.trace (S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)))).div_const 2)).exp
  simp only [Function.comp_apply, Pi.sub_apply, traceLeftCLM_apply,
    logdetSecondCLM_apply] at hd
  convert hd using 1
  · funext s
    simp only [wishartScaleDensityRatio, Matrix.sub_mul, Matrix.trace_sub,
      Function.comp_apply, Pi.sub_apply]
  · simp only [wishartScaleDensityRatio, traceLeftCLM_apply,
      logdetSecondCLM_apply, Matrix.sub_mul, Matrix.trace_sub]
    ring

end WishartVerification
end
end CanonicalSource84

section CanonicalSource85
/- Source: Wishart/WishartStein.lean -/



/-!
# Wishart integration by parts through congruence of the actual law

No boundary integral on the positive cone is assumed.  Congruence by `I+tA`
preserves the cone for small `t`; differentiating its exact pushforward law
gives the score identity.  Both sides have explicit dominated differentiation
witnesses for compactly supported C¹ tests.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix Filter Topology
open scoped Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ}

def congruenceScale (A S : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Matrix (Fin p) (Fin p) ℝ := (1 + t • A) * S * (1 + t • A)ᵀ

def congruenceScaleDerivative (A S : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  A * S * (1 + t • A)ᵀ + (1 + t • A) * S * Aᵀ

@[simp] theorem congruenceScale_zero (A S : Matrix (Fin p) (Fin p) ℝ) :
    congruenceScale A S 0 = S := by simp [congruenceScale]

@[simp] theorem congruenceScaleDerivative_zero (A S : Matrix (Fin p) (Fin p) ℝ) :
    congruenceScaleDerivative A S 0 = A * S + S * Aᵀ := by
  simp [congruenceScaleDerivative]

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_congruenceScale (A S : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    HasDerivAt (congruenceScale A S) (congruenceScaleDerivative A S t) t := by
  have hpoly : HasDerivAt
      (fun s : ℝ => S + s • (A * S + S * Aᵀ) + s ^ 2 • (A * S * Aᵀ))
      (A * S + S * Aᵀ + (2 * t) • (A * S * Aᵀ)) t := by
    have hsquare : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      have hs := ((hasDerivAt_id t).pow 2).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s : ℝ => (rfl : s ^ 2 = (id ^ 2) s)))
      exact hs.congr_deriv (by norm_num)
    have hraw := ((hasDerivAt_const t S).add
      ((hasDerivAt_id t).smul_const (A * S + S * Aᵀ))).add
        (hsquare.smul_const (A * S * Aᵀ))
    have hpointwise := hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s : ℝ =>
        (rfl : S + s • (A * S + S * Aᵀ) + s ^ 2 • (A * S * Aᵀ) =
          (((fun _ : ℝ => S) + (fun y : ℝ => y • (A * S + S * Aᵀ))) +
            (fun y : ℝ => y ^ 2 • (A * S * Aᵀ))) s)))
    exact hpointwise.congr_deriv (by simp only [one_smul, zero_add])
  have hfun : congruenceScale A S =
      fun s : ℝ => S + s • (A * S + S * Aᵀ) + s ^ 2 • (A * S * Aᵀ) := by
    funext s
    simp only [congruenceScale, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, smul_smul, smul_add, pow_two]
    abel
  have hderiv : congruenceScaleDerivative A S t =
      A * S + S * Aᵀ + (2 * t) • (A * S * Aᵀ) := by
    simp only [congruenceScaleDerivative, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, ← smul_smul, two_smul]
    abel
  rw [hfun, hderiv]
  exact hpoly

theorem congruenceScale_posDef {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : (1 + t • A).det ≠ 0) :
    (congruenceScale A S t).PosDef := by
  have hunit : IsUnit (1 + t • A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht)
  simpa [congruenceScale, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hS.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hunit)

theorem congruence_score {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (ν : ℝ) (A : Matrix (Fin p) (Fin p) ℝ) (X : SymmetricMatrix p) :
    -(ν / 2) * Matrix.trace (S⁻¹ * (A * S + S * Aᵀ)) +
        Matrix.trace (S⁻¹ * (A * S + S * Aᵀ) * S⁻¹ *
          (X : Matrix (Fin p) (Fin p) ℝ)) / 2 =
      Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) - ν * Matrix.trace A := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hSi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hunit
  have hiS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hunit
  have hlinear : S⁻¹ * (A * S + S * Aᵀ) = S⁻¹ * A * S + Aᵀ := by
    rw [mul_add, ← mul_assoc S⁻¹ S, hSi, one_mul, ← mul_assoc]
  have hquadratic : S⁻¹ * (A * S + S * Aᵀ) * S⁻¹ *
      (X : Matrix (Fin p) (Fin p) ℝ) =
      S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ) +
        Aᵀ * S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ) := by
    rw [hlinear, add_mul, add_mul]
    congr 1
    rw [mul_assoc (S⁻¹ * A) S S⁻¹, hiS, mul_one]
  have htr : Matrix.trace (S⁻¹ * A * S) = Matrix.trace A := by
    rw [Matrix.trace_mul_cycle, hiS, one_mul]
  have htranspose : Matrix.trace (Aᵀ * S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) =
      Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) := by
    have hXsymm : (X : Matrix (Fin p) (Fin p) ℝ)ᵀ = X :=
      (selfAdjoint.isHermitian_coe X).isSymm.eq
    have hSsymm : (S⁻¹)ᵀ = S⁻¹ := hS.inv.isHermitian.isSymm.eq
    rw [← Matrix.trace_transpose (Aᵀ * S⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)),
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hXsymm, hSsymm]
    exact Matrix.trace_mul_comm _ _
  rw [hquadratic, hlinear, Matrix.trace_add, htr, Matrix.trace_transpose,
    Matrix.trace_add, htranspose]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem wishart_stein_compact {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : ContDiff ℝ 1 g) (hcpt : HasCompactSupport g)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (∫ X, fderiv ℝ g X (congruenceVelocity A X) ∂nonsingularWishartMeasure ν S) =
      ∫ X, (Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A) * g X ∂nonsingularWishartMeasure ν S := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS hν
  let μ := nonsingularWishartMeasure ν S
  let T := congruenceScale A S
  let K := congruenceScaleDerivative A S
  let ρ : ℝ → SymmetricMatrix p → ℝ := fun t X => wishartScaleDensityRatio ν S (T t) X
  let ρ' : ℝ → SymmetricMatrix p → ℝ := fun t X =>
    (-(ν / 2) * Matrix.trace ((T t)⁻¹ * K t) +
      Matrix.trace ((T t)⁻¹ * K t * (T t)⁻¹ * (X : Matrix (Fin p) (Fin p) ℝ)) / 2) * ρ t X
  have hgc : Continuous g := hg.continuous
  have hρm (t : ℝ) : Measurable (ρ t) :=
    measurable_wishartScaleDensityRatio ν S (T t)
  have hρzero (X : SymmetricMatrix p) : ρ 0 X = 1 := by
    simp only [ρ, T, congruenceScale_zero, wishartScaleDensityRatio_self]
  have hρ'zero (X : SymmetricMatrix p) :
      ρ' 0 X = Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A := by
    dsimp only [ρ']
    rw [hρzero, mul_one]
    dsimp only [T, K]
    rw [congruenceScale_zero, congruenceScaleDerivative_zero]
    exact congruence_score hS ν A X
  have hscorec : Continuous (fun X : SymmetricMatrix p =>
      Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) - ν * Matrix.trace A) := by
    let L : SymmetricMatrix p →ₗ[ℝ] ℝ :=
      (Matrix.traceLinearMap (Fin p) ℝ ℝ).comp
        ((LinearMap.mulLeft ℝ (S⁻¹ * A)).comp (SymmetricMatrix p).subtype)
    have hL (X : SymmetricMatrix p) :
        L X = Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) := rfl
    simpa only [Pi.sub_def, hL] using
      L.continuous_of_finiteDimensional.sub (continuous_const (y := ν * Matrix.trace A))
  have hnear := congruenceFlow_det_eventually_ne_zero A
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have hdet (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : (1 + t • A).det ≠ 0 := by
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr ht).trans_lt (by dsimp [ε]; linarith)
  have hTunit (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : IsUnit (T t).det :=
    isUnit_iff_ne_zero.mpr (congruenceScale_posDef hS A (hdet t ht)).det_pos.ne'
  have hρderiv (X : SymmetricMatrix p) (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) :
      HasDerivAt (fun s => ρ s X) (ρ' t X) t :=
    hasDerivAt_wishartScaleDensityRatio_general S ν X
      (hasDerivAt_congruenceScale A S t) (hTunit t ht)
  have hρ'cont : ContinuousOn (Function.uncurry ρ') (Set.Icc (-ε) ε ×ˢ tsupport g) := by
    intro z hz
    have hTc : Continuous (fun y : ℝ × SymmetricMatrix p => T y.1) := by
      dsimp [T, congruenceScale]; fun_prop
    have hTi : ContinuousAt (fun y : ℝ × SymmetricMatrix p => (T y.1)⁻¹) z :=
      (hasFDerivAt_matrix_inv (hTunit z.1 hz.1)).continuousAt.comp
        (f := fun y : ℝ × SymmetricMatrix p => T y.1) (x := z) hTc.continuousAt
    have hTd : ContinuousAt (fun y : ℝ × SymmetricMatrix p => Real.log (T y.1).det) z :=
      hTc.matrix_det.continuousAt.log (hTunit z.1 hz.1).ne_zero
    apply ContinuousAt.continuousWithinAt
    dsimp [Function.uncurry, ρ', ρ, wishartScaleDensityRatio, K, congruenceScaleDerivative]
    fun_prop
  obtain ⟨dF⟩ := integralDerivativeData_quadraticLinearTransport
    (integrable_id_nonsingularWishartMeasure S ν) hg hcpt
    (congruenceVelocity A) (congruenceCLM A)
  obtain ⟨dG⟩ : Nonempty (IntegralDerivativeData μ
      (fun t X => ρ t X * g X) (fun t X => ρ' t X * g X) 0) :=
    integralDerivativeData_of_compact_derivative_support hε hcpt
      (Filter.Eventually.of_forall fun t =>
        (hρm t |>.aestronglyMeasurable.mul hgc.aestronglyMeasurable))
      (by simpa [ρ, T] using hg.continuous.integrable_of_hasCompactSupport hcpt)
      (by simpa only [hρ'zero, Pi.mul_def] using (hscorec.mul hgc).aestronglyMeasurable)
      (by
        change ContinuousOn (fun z : ℝ × SymmetricMatrix p => ρ' z.1 z.2 * g z.2)
          (Set.Icc (0 - ε) (0 + ε) ×ˢ tsupport g)
        simpa only [Function.uncurry_def, Function.comp_def, Pi.mul_def,
          zero_sub, zero_add] using hρ'cont.mul (hgc.comp continuous_snd).continuousOn)
      (fun t _ X hX => by simp [image_eq_zero_of_notMem_tsupport hX])
      (fun X t ht => by
        apply (hρderiv X t _).mul_const
        simpa using ht)
  have hlaw : ∀ᶠ t in 𝓝 (0 : ℝ),
      Measurable (quadraticLinearTransport (congruenceVelocity A) (congruenceCLM A) t) ∧
      AEMeasurable (ρ t) μ ∧ (0 ≤ᵐ[μ] ρ t) ∧
      μ.map (quadraticLinearTransport (congruenceVelocity A) (congruenceCLM A) t) =
        μ.withDensity (fun X => ENNReal.ofReal (ρ t X)) := by
    filter_upwards [hnear] with t ht
    refine ⟨by unfold quadraticLinearTransport; fun_prop, (hρm t).aemeasurable,
      Filter.Eventually.of_forall fun X => (wishartScaleDensityRatio_pos ν S (T t) X).le, ?_⟩
    rw [show quadraticLinearTransport (congruenceVelocity A) (congruenceCLM A) t =
      Matrix.symmetricCongruenceLinearMap (1 + t • A) from
        funext (quadraticLinearTransport_eq_congruence A t)]
    exact (map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero ν S ht).trans
      (nonsingularWishartMeasure_scale_ratio hS (congruenceScale_posDef hS A ht) hν)
  have hid := transport_derivative_identity hg.continuous.measurable hlaw dF dG
  simpa only [quadraticLinearTransport_zero, mul_zero, zero_smul, add_zero, hρ'zero] using hid

end WishartVerification
end
end CanonicalSource85

section CanonicalSource86
/- Source: Wishart/SmoothCutoffs.lean -/



/-!
# Smooth cutoffs with a uniform first-derivative bound

The radius tends to infinity.  At each fixed point the cutoff and its first
derivative eventually equal `1` and `0`, respectively.  These are the concrete
cutoffs used to extend compact-test Stein identities.
-/

noncomputable section

open Filter Topology
open scoped ContDiff

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def unitSmoothCutoff : ContDiffBump (0 : E) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def expandingCutoff (n : ℕ) (x : E) : ℝ :=
  (unitSmoothCutoff (E := E) : E → ℝ) (((n : ℝ) + 1)⁻¹ • x)

theorem expandingCutoff_nonneg (n : ℕ) (x : E) : 0 ≤ expandingCutoff n x :=
  (unitSmoothCutoff (E := E)).nonneg

theorem expandingCutoff_le_one (n : ℕ) (x : E) : expandingCutoff n x ≤ 1 :=
  (unitSmoothCutoff (E := E)).le_one

theorem contDiff_expandingCutoff (n : ℕ) : ContDiff ℝ ∞ (expandingCutoff (E := E) n) :=
  (unitSmoothCutoff (E := E)).contDiff.comp (by fun_prop)

theorem hasCompactSupport_expandingCutoff (n : ℕ) :
    HasCompactSupport (expandingCutoff (E := E) n) := by
  have hn : ((n : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  exact (unitSmoothCutoff (E := E)).hasCompactSupport.comp_isClosedEmbedding
    (Homeomorph.smulOfNeZero ((n : ℝ) + 1)⁻¹ hn).isClosedEmbedding

theorem expandingCutoff_eventuallyEq_one (x : E) :
    ∀ᶠ n : ℕ in atTop, expandingCutoff n =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnorm : ‖((n : ℝ) + 1)⁻¹ • x‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← div_eq_inv_mul]
    apply (div_lt_one (by positivity)).mpr
    exact hN.trans ((by exact_mod_cast hn : (N : ℝ) ≤ n).trans_lt (by linarith))
  have hb : (((n : ℝ) + 1)⁻¹ • x) ∈ Metric.ball (0 : E) (unitSmoothCutoff (E := E)).rIn := by
    simpa [Metric.mem_ball, dist_zero_right, unitSmoothCutoff] using hnorm
  have he := (unitSmoothCutoff (E := E)).eventuallyEq_one_of_mem_ball hb
  exact he.comp_tendsto (by fun_prop :
    ContinuousAt (fun y : E => ((n : ℝ) + 1)⁻¹ • y) x)

theorem expandingCutoff_eventually_values (x : E) :
    ∀ᶠ n : ℕ in atTop, expandingCutoff n x = 1 ∧ fderiv ℝ (expandingCutoff n) x = 0 := by
  filter_upwards [expandingCutoff_eventuallyEq_one x] with n hn
  exact ⟨hn.eq_of_nhds, by simpa using hn.fderiv_eq (𝕜 := ℝ)⟩

theorem expandingCutoff_uniform_fderiv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x : E, ‖fderiv ℝ (expandingCutoff n) x‖ ≤ M := by
  let χ := unitSmoothCutoff (E := E)
  have hχ : ContDiff ℝ 1 (χ : E → ℝ) := χ.contDiff
  have hD : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := hD.norm.bddAbove_range_of_hasCompactSupport (χ.hasCompactSupport.fderiv ℝ).norm
  refine ⟨max M 0, le_max_right _ _, fun n x => ?_⟩
  have hlin : HasFDerivAt (fun y : E => ((n : ℝ) + 1)⁻¹ • y)
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E) x := by
    exact (hasFDerivAt_id x).const_smul ((n : ℝ) + 1)⁻¹
  have hd := (hχ.differentiable (by norm_num) _).hasFDerivAt.comp x hlin
  rw [show fderiv ℝ (expandingCutoff n) x =
      (fderiv ℝ χ (((n : ℝ) + 1)⁻¹ • x)).comp
        (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E) from hd.fderiv]
  calc
    _ ≤ ‖fderiv ℝ χ (((n : ℝ) + 1)⁻¹ • x)‖ *
        ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M 0 * 1 := by
      apply mul_le_mul ((hM ⟨_, rfl⟩).trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
      calc
        _ ≤ |((n : ℝ) + 1)⁻¹| * 1 := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ ≤ 1 := by
          rw [abs_of_pos (by positivity), mul_one]
          exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    _ = _ := mul_one _

end WishartVerification
end
end CanonicalSource86

section CanonicalSource87
/- Source: Wishart/SteinExtension.lean -/



/-!
# Extending a compact-test Stein identity

This extension theorem requires explicit integrability of the three terms
arising from the cutoff product rule.  It therefore cannot conceal a divergent
expectation behind a totalized integral.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem extend_compact_stein {μ : Measure E} [IsFiniteMeasure μ]
    {b : E → E} {s : E → ℝ} (hb : Continuous b) (hs : Continuous s)
    (hcompact : ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      (∫ x, fderiv ℝ g x (b x) ∂μ) = ∫ x, s x * g x ∂μ)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hscore : Integrable (fun x => s x * g x) μ)
    (hgradient : Integrable (fun x => fderiv ℝ g x (b x)) μ)
    (herror : Integrable (fun x => ‖b x‖ * ‖g x‖) μ) :
    (∫ x, fderiv ℝ g x (b x) ∂μ) = ∫ x, s x * g x ∂μ := by
  obtain ⟨M, hM, hMbound⟩ := expandingCutoff_uniform_fderiv_bound (E := E)
  let gn : ℕ → E → ℝ := fun n x => expandingCutoff n x * g x
  have hgn (n : ℕ) : ContDiff ℝ 1 (gn n) :=
    ((contDiff_expandingCutoff n).of_le (by simp)).mul hg
  have hgncpt (n : ℕ) : HasCompactSupport (gn n) :=
    (hasCompactSupport_expandingCutoff n).mul_right
  have hformula (n : ℕ) (x : E) :
      fderiv ℝ (gn n) x (b x) =
        expandingCutoff n x * fderiv ℝ g x (b x) +
          fderiv ℝ (expandingCutoff n) x (b x) * g x := by
    change fderiv ℝ (fun y => expandingCutoff n y * g y) x (b x) = _
    rw [fderiv_fun_mul ((contDiff_expandingCutoff n).differentiable (by simp) x)
      (hg.differentiable (by norm_num) x)]
    simp [gn, ContinuousLinearMap.add_apply, mul_comm, add_comm]
  have hleft : Tendsto (fun n => ∫ x, fderiv ℝ (gn n) x (b x) ∂μ) atTop
      (𝓝 (∫ x, fderiv ℝ g x (b x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖fderiv ℝ g x (b x)‖ + M * (‖b x‖ * ‖g x‖))
    · intro n
      exact ((hgn n).continuous_fderiv (by norm_num) |>.clm_apply hb).aestronglyMeasurable
    · exact hgradient.norm.add (herror.const_mul M)
    · intro n
      filter_upwards with x
      rw [hformula]
      calc
        _ ≤ ‖expandingCutoff n x * fderiv ℝ g x (b x)‖ +
            ‖fderiv ℝ (expandingCutoff n) x (b x) * g x‖ := norm_add_le _ _
        _ ≤ 1 * ‖fderiv ℝ g x (b x)‖ + (M * ‖b x‖) * ‖g x‖ := by
          simp only [norm_mul]
          gcongr
          · simpa [Real.norm_of_nonneg (expandingCutoff_nonneg n x)] using expandingCutoff_le_one n x
          · exact ((fderiv ℝ (expandingCutoff n) x).le_opNorm (b x)).trans
              (mul_le_mul_of_nonneg_right (hMbound n x) (norm_nonneg _))
        _ = _ := by ring
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [expandingCutoff_eventually_values x] with n hn
      simp [hformula, hn.1, hn.2]
  have hright : Tendsto (fun n => ∫ x, s x * gn n x ∂μ) atTop
      (𝓝 (∫ x, s x * g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖s x * g x‖)
    · intro n
      exact (hs.mul (hgn n).continuous).aestronglyMeasurable
    · exact hscore.norm
    · intro n
      filter_upwards with x
      change |s x * (expandingCutoff n x * g x)| ≤ |s x * g x|
      rw [show s x * (expandingCutoff n x * g x) = expandingCutoff n x * (s x * g x) by ring,
        abs_mul, abs_of_nonneg (expandingCutoff_nonneg n x)]
      exact (mul_le_mul_of_nonneg_right
        (expandingCutoff_le_one n x) (abs_nonneg _)).trans_eq (one_mul _)
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [expandingCutoff_eventually_values x] with n hn
      simp [gn, hn.1]
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (hcompact (gn n) (hgn n) (hgncpt n)).symm))

end WishartVerification
end
end CanonicalSource87

section CanonicalSource88
/- Source: Wishart/SteinTemperate.lean -/



/-!
# Stein identities for the polynomial-growth functions used in the paper

The compact-test identities are extended using explicit smooth cutoffs.  All
integrability obligations follow from full finite moments of the actual laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open scoped RealInnerProductSpace Matrix.Norms.Operator

namespace WishartVerification

theorem gaussian_stein_temperate {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) {g : EuclideanSpace ℝ (Fin p) → ℝ} (hg : g.HasTemperateGrowth)
    (h : EuclideanSpace ℝ (Fin p)) :
    (∫ x, ⟪h, C⁻¹.toEuclideanLin x⟫ * g x ∂multivariateGaussian 0 C) =
      ∫ x, fderiv ℝ g x h ∂multivariateGaussian 0 C := by
  have hμ := allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C)
  have hb : (fun _ : EuclideanSpace ℝ (Fin p) => h).HasTemperateGrowth := .const h
  have hs : (fun x : EuclideanSpace ℝ (Fin p) => ⟪h, C⁻¹.toEuclideanLin x⟫).HasTemperateGrowth := by
    exact (innerSL ℝ h).hasTemperateGrowth.comp C⁻¹.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth
  symm
  apply extend_compact_stein continuous_const hs.1.continuous
    (fun f hf hcpt => (gaussian_stein_compact hC hf hcpt h).symm)
    (hg.1.of_le (by simp))
  · exact integrable_temperate_of_allNormMoments hμ (hs.mul hg)
  · exact integrable_fderiv_apply_temperate hμ hg hb
  · exact ((allFiniteMoments_temperate_norm hμ hb).mul
      (allFiniteMoments_temperate_norm hμ hg)).integrable

theorem wishart_stein_temperate {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (∫ X, fderiv ℝ g X (congruenceVelocity A X) ∂nonsingularWishartMeasure ν S) =
      ∫ X, (Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A) * g X ∂nonsingularWishartMeasure ν S := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS hν
  have hμ := allFiniteMoments_wishart_norm ν S
  have hb := (congruenceVelocity A).hasTemperateGrowth
  let L : SymmetricMatrix p →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap (Fin p) ℝ ℝ).comp
      ((LinearMap.mulLeft ℝ (S⁻¹ * A)).comp
        (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype))
  have hs : (fun X : SymmetricMatrix p =>
      Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A).HasTemperateGrowth :=
    L.hasTemperateGrowth.sub (Function.HasTemperateGrowth.const _)
  apply extend_compact_stein (congruenceVelocity A).continuous hs.1.continuous
    (fun f hf hcpt => wishart_stein_compact hS hν hf hcpt A)
    (hg.1.of_le (by simp))
  · exact integrable_temperate_of_allNormMoments hμ (hs.mul hg)
  · exact integrable_fderiv_apply_temperate hμ hg hb
  · exact ((allFiniteMoments_temperate_norm hμ hb).mul
      (allFiniteMoments_temperate_norm hμ hg)).integrable

theorem wishart_stein_translate {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (A : Matrix (Fin p) (Fin p) ℝ) (Z : SymmetricMatrix p) :
    (∫ X, fderiv ℝ g (X + Z) (congruenceVelocity A X) ∂nonsingularWishartMeasure ν S) =
      ∫ X, (Matrix.trace (S⁻¹ * A * (X : Matrix (Fin p) (Fin p) ℝ)) -
        ν * Matrix.trace A) * g (X + Z) ∂nonsingularWishartMeasure ν S := by
  have htest : (fun X => g (X + Z)).HasTemperateGrowth :=
    hg.comp (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const Z))
  have hid := wishart_stein_temperate hS hν htest A
  have hd (X H : SymmetricMatrix p) :
      fderiv ℝ (fun Y => g (Y + Z)) X H = fderiv ℝ g (X + Z) H := by
    have hcomp := ((hg.1.differentiable (by simp) _).hasFDerivAt.comp X
      ((hasFDerivAt_id X).add_const Z)).fderiv
    have heq : fderiv ℝ (fun Y => g (Y + Z)) X = fderiv ℝ g (X + Z) := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hcomp
    exact congrArg (fun T : SymmetricMatrix p →L[ℝ] ℝ => T H) heq
  simpa only [hd] using hid

end WishartVerification
end
end CanonicalSource88

section CanonicalSource89
/- Source: Wishart/WeightedRadialStein.lean -/



/-!
# The weighted identity behind the real-shape radial equation

Wishart congruence and Gaussian translation produce the same directional
derivative. Subtracting their fully justified integral identities yields the
identity below for every real admissible shape and every smooth test of
polynomial derivative growth.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open scoped RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem weighted_radial_stein {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p,
      ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ *
        g (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) =
    ν * (∫ Y : RadialInputSpace p, ⟪u, Y.2 + r • v⟫ * g (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μW := nonsingularWishartMeasure ν C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  let w : RadialInputSpace p → EuclideanSpace ℝ (Fin p) := fun Y => Y.2 + r • v
  let V : RadialInputSpace p → SymmetricMatrix p := radialInput v r
  let L : RadialInputSpace p → ℝ := fun Y =>
    fderiv ℝ g (V Y) (symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u))
  let G : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin Y.2)⟫ * g (V Y)
  let Q : RadialInputSpace p → ℝ := fun Y =>
    ⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * g (V Y)
  let R : RadialInputSpace p → ℝ := fun Y => ⟪u, w Y⟫ * g (V Y)
  let S : RadialInputSpace p → ℝ := fun Y =>
    (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin (w Y))⟫ - ν * ⟪u, w Y⟫) * g (V Y)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hw : w.HasTemperateGrowth := hZ.add (Function.HasTemperateGrowth.const (r • v))
  have hV : V.HasTemperateGrowth := hW.add (hasTemperateGrowth_rankOneSymmetric.comp hw)
  have hgV := hg.comp hV
  have hCi := (LinearMap.toContinuousLinearMap C⁻¹.toEuclideanLin).hasTemperateGrowth
  have hinner := (innerSL ℝ u).hasTemperateGrowth
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW (Function.HasTemperateGrowth.const u)
  have hH : (fun Y : RadialInputSpace p =>
      symmetricRankDirection (w Y) (symmetricMatrixAction Y.1 u)).HasTemperateGrowth := by
    simpa only [symmetricRankDirection, ContinuousLinearMap.smul_apply,
      Pi.smul_def, Pi.smul_apply, ContinuousLinearMap.coe_fst', two_smul,
      ContinuousLinearMap.add_apply] using
      (Function.HasTemperateGrowth.const (2 : ℝ)).fun_smul
        (symmetricOuterCLM.bilinear_hasTemperateGrowth hw hWu)
  have hLt : L.HasTemperateGrowth :=
    (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hH
      ((hasTemperateGrowth_fderiv hg).comp hV)
  have hGt : G.HasTemperateGrowth :=
    (hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hZ))).mul hgV
  have hQt : Q.HasTemperateGrowth :=
    (hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
      (Function.HasTemperateGrowth.const _))).mul hgV
  have hRt : R.HasTemperateGrowth := (hinner.comp hw).mul hgV
  have hSt : S.HasTemperateGrowth :=
    ((hinner.comp (symmetricMatrixAction.bilinear_hasTemperateGrowth hW (hCi.comp hw))).sub
      ((Function.HasTemperateGrowth.const ν).mul (hinner.comp hw))).mul hgV
  have hLint : Integrable L μ := integrable_temperate_of_allNormMoments hμ hLt
  have hGint : Integrable G μ := integrable_temperate_of_allNormMoments hμ hGt
  have hQint : Integrable Q μ := integrable_temperate_of_allNormMoments hμ hQt
  have hRint : Integrable R μ := integrable_temperate_of_allNormMoments hμ hRt
  have hSint : Integrable S μ := integrable_temperate_of_allNormMoments hμ hSt
  have hWishart (z : EuclideanSpace ℝ (Fin p)) :
      (∫ W, L (W, z) ∂μW) = ∫ W, S (W, z) ∂μW := by
    let wz := z + r • v
    have htest : (fun W : SymmetricMatrix p => g (W + rankOneSymmetric wz)).HasTemperateGrowth :=
      hg.comp (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const _))
    have hid := wishart_stein_temperate hC hν htest (outerMatrix wz u)
    have hd (W : SymmetricMatrix p) (H : SymmetricMatrix p) :
        fderiv ℝ (fun W : SymmetricMatrix p => g (W + rankOneSymmetric wz)) W H =
          fderiv ℝ g (W + rankOneSymmetric wz) H := by
      have hderiv := ((hg.1.differentiable (by simp) _).hasFDerivAt.comp W
        ((hasFDerivAt_id W).add_const (rankOneSymmetric wz))).fderiv
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using congrArg (fun J => J H) hderiv
    simpa only [hd, congruenceVelocity_outerMatrix, trace_mul_outerMatrix_mul,
      trace_outerMatrix, L, S, w, V, radialInput, wz] using hid
  have hGaussian (W : SymmetricMatrix p) :
      (∫ z, G (W, z) ∂μZ) = ∫ z, L (W, z) ∂μZ := by
    have hshift : (fun z : EuclideanSpace ℝ (Fin p) => z + r • v).HasTemperateGrowth :=
      Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const _)
    have htest : (fun z : EuclideanSpace ℝ (Fin p) =>
        g (W + rankOneSymmetric (z + r • v))).HasTemperateGrowth :=
      hg.comp ((Function.HasTemperateGrowth.const W).add (hasTemperateGrowth_rankOneSymmetric.comp hshift))
    have hid := gaussian_stein_temperate hC htest (symmetricMatrixAction W u)
    have hd (z h : EuclideanSpace ℝ (Fin p)) :
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin p) => g (W + rankOneSymmetric (z + r • v))) z h =
          fderiv ℝ g (W + rankOneSymmetric (z + r • v))
            (symmetricRankDirection (z + r • v) h) := by
      have hin := (hasFDerivAt_rankOneSymmetric (z + r • v)).comp z
        ((hasFDerivAt_id z).add_const (r • v))
      have hderiv := ((hg.1.differentiable (by simp) _).hasFDerivAt.comp z (hin.const_add W)).fderiv
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using congrArg (fun J => J h) hderiv
    simpa only [hd, inner_symmetricMatrixAction, L, G, w, V, radialInput] using hid
  have hSG : (∫ Y, S Y ∂μ) = ∫ Y, G Y ∂μ := by
    rw [integral_prod_symm S hSint, integral_prod G hGint]
    calc
      (∫ z, ∫ W, S (W, z) ∂μW ∂μZ) = ∫ z, ∫ W, L (W, z) ∂μW ∂μZ :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (hWishart z).symm)
      _ = ∫ Y, L Y ∂μ := (integral_prod_symm L hLint).symm
      _ = ∫ W, ∫ z, L (W, z) ∂μZ ∂μW := integral_prod L hLint
      _ = ∫ W, ∫ z, G (W, z) ∂μZ ∂μW :=
        integral_congr_ae (Filter.Eventually.of_forall fun W => (hGaussian W).symm)
  have hsplit : S = fun Y => G Y + r * Q Y - ν * R Y := by
    funext Y
    simp only [S, G, Q, R, w, map_add, map_smul, inner_add_right, real_inner_smul_right]
    ring
  rw [hsplit] at hSG
  have hsumInt : Integrable (fun Y => G Y + r * Q Y) μ := by
    simpa only [Pi.add_def] using hGint.add (hQint.const_mul r)
  rw [integral_sub hsumInt (hRint.const_mul ν),
    integral_add hGint (hQint.const_mul r), integral_const_mul, integral_const_mul] at hSG
  change r * (∫ Y, Q Y ∂μ) = ν * (∫ Y, R Y ∂μ)
  linarith

end WishartVerification
end
end CanonicalSource89

section CanonicalSource90
/- Source: Wishart/RadialSteinIdentity.lean -/



/-!
# The radial mean identity for every admissible real shape

The identity is derived from the actual Wishart and Gaussian laws.  In
particular, neither an integer-dimensional Gaussian representation nor a
radial differential equation is an assumption of the result.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix
open scoped RealInnerProductSpace BigOperators

namespace WishartVerification

variable {p : ℕ}

theorem hasTemperateGrowth_radialInput_slice
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (radialInput v r).HasTemperateGrowth :=
  (hasTemperateGrowth_radialInput v).comp
    (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const r)
      Function.HasTemperateGrowth.id)

theorem hasTemperateGrowth_radialSecondIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p)) :
    (fun q : ℝ × RadialInputSpace p => radialSecondIntegrand f v q.1 q.2).HasTemperateGrowth := by
  have heq : (fun q : ℝ × RadialInputSpace p => radialSecondIntegrand f v q.1 q.2) =
      parameterDerivative (fun q : ℝ × RadialInputSpace p => radialFirstIntegrand f v q.1 q.2) := by
    funext q
    exact (hasDerivAt_radialFirstIntegrand hf v q.2 q.1).unique
      (hasDerivAt_parameter_slice (hasTemperateGrowth_radialFirstIntegrand hf v) q.2 q.1)
  rw [heq]
  exact hasTemperateGrowth_parameterDerivative (hasTemperateGrowth_radialFirstIntegrand hf v)

set_option backward.isDefEq.respectTransparency false in
theorem radial_wishart_stein {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {g : SymmetricMatrix p → ℝ} (hg : g.HasTemperateGrowth)
    (u v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p,
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p,
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - ν * ⟪u, v⟫) *
        g (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μW := nonsingularWishartMeasure ν C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hWu := symmetricMatrixAction.bilinear_hasTemperateGrowth hW
    (Function.HasTemperateGrowth.const u)
  have hH := (symmetricRankDirection v).hasTemperateGrowth.comp hWu
  have hL : Integrable (fun Y : RadialInputSpace p =>
      fderiv ℝ g (radialInput v r Y)
        (symmetricRankDirection v (symmetricMatrixAction Y.1 u))) μ := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.coe_fst'] using
      integrable_temperate_of_allNormMoments hμ
        ((ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth hH
          ((hasTemperateGrowth_fderiv hg).comp hV))
  have hscore := ((innerSL ℝ u).hasTemperateGrowth.comp
    (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
      (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))).sub
        (Function.HasTemperateGrowth.const (ν * ⟪u, v⟫))
  have hR : Integrable (fun Y : RadialInputSpace p =>
      (⟪u, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ - ν * ⟪u, v⟫) *
        g (radialInput v r Y)) μ := by
    simpa only [Function.comp_def, Pi.sub_def, Pi.mul_def,
      ContinuousLinearMap.coe_fst', innerSL_apply_apply] using
      integrable_temperate_of_allNormMoments hμ (hscore.mul (hg.comp hV))
  rw [integral_prod_symm _ hL, integral_prod_symm _ hR]
  apply integral_congr_ae
  filter_upwards with z
  simpa only [congruenceVelocity_outerMatrix, trace_mul_outerMatrix_mul,
    trace_outerMatrix, radialInput] using
      wishart_stein_translate hC hν hg (outerMatrix v u) (rankOneSymmetric (z + r • v))

def radialDerivativeTest (f : SymmetricMatrix p → ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (i : Fin p) (X : SymmetricMatrix p) : ℝ :=
  fderiv ℝ f X (symmetricRankDirection v (coordinateVector i))

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_radialDerivativeTest {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    (radialDerivativeTest f v i).HasTemperateGrowth := by
  unfold radialDerivativeTest
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
    (ContinuousLinearMap.apply ℝ ℝ (symmetricRankDirection v (coordinateVector i))).hasTemperateGrowth.comp
      (hasTemperateGrowth_fderiv hf)

theorem coordinate_inner (i : Fin p) (v : EuclideanSpace ℝ (Fin p)) :
    ⟪coordinateVector i, v⟫ = v i := by
  simp [coordinateVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Pi.single_apply]

theorem sum_radialDerivativeTest (f : SymmetricMatrix p → ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (X : SymmetricMatrix p) :
    (∑ i, v i * radialDerivativeTest f v i X) =
      2 * fderiv ℝ f X (rankOneSymmetric v) := by
  simp only [radialDerivativeTest, ← smul_eq_mul, ← map_smul, ← map_sum]
  rw [sum_coordinateVector, symmetricRankDirection_self]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The integrated radial generator identity.  The factor `r` is retained, so
the formula is valid at zero as well as at every nonzero real radius. -/
theorem radial_generator_identity {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    r * (∫ Y : RadialInputSpace p, symmetricRadialGenerator (ν + 1) v f (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) =
    r * (∫ Y : RadialInputSpace p, radialSecondIntegrand f v r Y
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) +
    ν * (∫ Y : RadialInputSpace p, radialFirstIntegrand f v r Y
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μ := (nonsingularWishartMeasure ν C).prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  let V := radialInput v r
  let gi := radialDerivativeTest f v
  let L : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    fderiv ℝ (gi i) (V Y)
      (symmetricRankDirection v (symmetricMatrixAction Y.1 (coordinateVector i)))
  let Q : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    ⟪coordinateVector i, symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)⟫ * gi i (V Y)
  let R : Fin p → RadialInputSpace p → ℝ := fun i Y =>
    (Y.2 + r • v) i * gi i (V Y)
  let B : RadialInputSpace p → ℝ := fun Y => fderiv ℝ f (V Y) (rankOneSymmetric v)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hV := hasTemperateGrowth_radialInput_slice v r
  have hW := (ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hZ := (ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).hasTemperateGrowth
  have hgi (i : Fin p) := hasTemperateGrowth_radialDerivativeTest hf v i
  have hgint (i : Fin p) : Integrable (fun Y => gi i (V Y)) μ :=
    integrable_temperate_of_allNormMoments hμ ((hgi i).comp hV)
  have hLint (i : Fin p) : Integrable (L i) μ := by
    exact integrable_temperate_of_allNormMoments hμ
      ((ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth
        ((symmetricRankDirection v).hasTemperateGrowth.comp
          (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
            (Function.HasTemperateGrowth.const (coordinateVector i))))
        ((hasTemperateGrowth_fderiv (hgi i)).comp hV))
  have hQint (i : Fin p) : Integrable (Q i) μ :=
    integrable_temperate_of_allNormMoments hμ
      (((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
        (symmetricMatrixAction.bilinear_hasTemperateGrowth hW
          (Function.HasTemperateGrowth.const (C⁻¹.toEuclideanLin v)))).mul ((hgi i).comp hV))
  have hRint (i : Fin p) : Integrable (R i) μ := by
    have ht := ((innerSL ℝ (coordinateVector i)).hasTemperateGrowth.comp
      (hZ.add (Function.HasTemperateGrowth.const (r • v)))).mul ((hgi i).comp hV)
    simpa only [Function.comp_def, Pi.add_def, Pi.mul_def,
      ContinuousLinearMap.coe_snd', innerSL_apply_apply, coordinate_inner, R, gi, V] using
      integrable_temperate_of_allNormMoments hμ ht
  have hBint : Integrable B μ := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, B, V] using
      integrable_temperate_of_allNormMoments hμ
        ((ContinuousLinearMap.apply ℝ ℝ (rankOneSymmetric v)).hasTemperateGrowth.comp
          ((hasTemperateGrowth_fderiv hf).comp hV))
  have hsecond : Integrable (radialSecondIntegrand f v r) μ :=
    integrable_temperate_of_allNormMoments hμ
      ((hasTemperateGrowth_radialSecondIntegrand hf v).comp
        (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const r)
          Function.HasTemperateGrowth.id))
  have hWi (i : Fin p) :
      (∫ Y, L i Y ∂μ) = (∫ Y, Q i Y ∂μ) - ν * v i * (∫ Y, gi i (V Y) ∂μ) := by
    have h := radial_wishart_stein hC hν (hgi i) (coordinateVector i) v r
    simp only [sub_mul, coordinate_inner] at h
    have hQint' : Integrable (fun Y : RadialInputSpace p =>
        (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y)) μ := by
      simpa only [Q, coordinate_inner] using hQint i
    change (∫ Y, L i Y ∂μ) = ∫ Y,
      (symmetricMatrixAction Y.1 (C⁻¹.toEuclideanLin v)) i * gi i (V Y) -
        ν * v i * gi i (V Y) ∂μ at h
    rw [integral_sub hQint' ((hgint i).const_mul (ν * v i)), integral_const_mul] at h
    simpa only [Q, coordinate_inner] using h
  have hRi (i : Fin p) : r * (∫ Y, Q i Y ∂μ) = ν * (∫ Y, R i Y ∂μ) := by
    simpa only [Q, R, gi, V, μ, coordinate_inner] using
      weighted_radial_stein hC hν (hgi i) (coordinateVector i) v r
  have hLi (i : Fin p) :
      r * (∫ Y, L i Y ∂μ) + r * ν * v i * (∫ Y, gi i (V Y) ∂μ) =
        ν * (∫ Y, R i Y ∂μ) := by
    rw [hWi]
    nlinarith [hRi i]
  have hsum := congrArg (fun a : Fin p → ℝ => ∑ i, a i) (funext hLi)
  have hLpoint (Y : RadialInputSpace p) :
      (∑ i, L i Y) = radialCovarianceContraction f (V Y) v
        (Y.1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [radialCovarianceContraction_eq_directional_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact (symmetricSecondDerivative_eq hf _ _ _).symm
  have hRpoint (Y : RadialInputSpace p) :
      (∑ i, R i Y) = radialFirstIntegrand f v r Y :=
    (radialFirstIntegrand_eq_coordinate_sum f v r Y).symm
  have hBpoint (Y : RadialInputSpace p) :
      (∑ i, v i * gi i (V Y)) = 2 * B Y := sum_radialDerivativeTest f v (V Y)
  have hLsum : (∑ i, ∫ Y, L i Y ∂μ) =
      ∫ Y, radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hLint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hLpoint)
  have hRsum : (∑ i, ∫ Y, R i Y ∂μ) = ∫ Y, radialFirstIntegrand f v r Y ∂μ := by
    rw [← integral_finsetSum _ (fun i _ => hRint i)]
    exact integral_congr_ae (Filter.Eventually.of_forall hRpoint)
  have hBsum : (∑ i, v i * (∫ Y, gi i (V Y) ∂μ)) = 2 * (∫ Y, B Y ∂μ) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hgint i).const_mul (v i))]
    rw [integral_congr_ae (Filter.Eventually.of_forall hBpoint), integral_const_mul]
  have hcovint : Integrable (fun Y =>
      radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ := by
    exact (integrable_finsetSum _ (fun i _ => hLint i)).congr
      (Filter.Eventually.of_forall hLpoint)
  have hgen :
      (∫ Y, symmetricRadialGenerator (ν + 1) v f (V Y) ∂μ) =
        (∫ Y, radialSecondIntegrand f v r Y ∂μ) +
        (∫ Y, radialCovarianceContraction f (V Y) v
          (Y.1 : Matrix (Fin p) (Fin p) ℝ) ∂μ) +
        2 * ν * (∫ Y, B Y ∂μ) := by
    simp_rw [V, symmetricRadialGenerator_decomposition]
    have hsumInt : Integrable (fun Y => radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) μ := by
      simpa only [Pi.add_def] using hsecond.add hcovint
    change (∫ Y, (radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (V Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ)) +
        2 * (ν + 1 - 1) * B Y ∂μ) = _
    rw [integral_add hsumInt (hBint.const_mul (2 * (ν + 1 - 1))),
      integral_add hsecond hcovint, integral_const_mul]
    ring
  change r * (∫ Y, symmetricRadialGenerator (ν + 1) v f (V Y) ∂μ) = _
  rw [hgen]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  rw [hLsum, hRsum] at hsum
  have hBsum' : (∑ i, v i * ∫ Y, gi i (V Y) ∂μ) = 2 * ∫ Y, B Y ∂μ := hBsum
  rw [hBsum'] at hsum
  nlinarith

end WishartVerification
end
end CanonicalSource90

section CanonicalSource91
/- Source: Wishart/RadialMonotonicity.lean -/



/-!
# The radial differential-inequality step

This file proves the ordinary differential-equation implication used at the end of
Lemma 3.1 of *The Wishart product inequality and spectral correlation*.  It does
not assume a Wishart law or the radial mean identity: those are separate
mathematical obligations.  The function and both derivatives below are ordinary
real functions, with derivative relations stated by `HasDerivAt`.
-/

open Set Filter
open scoped Topology

namespace Wishart

/-- The integrating factor for the radial operator
`4 * t * F'' + 2 * N * F'` has the displayed derivative on the positive ray. -/
theorem hasDerivAt_radialIntegratingFactor
    {D D₂ : ℝ → ℝ} {N t : ℝ} (ht : 0 < t)
    (hD : HasDerivAt D (D₂ t) t) :
    HasDerivAt (fun s : ℝ => s ^ (N / 2) * D s)
      ((1 / 4 : ℝ) * t ^ (N / 2 - 1) * (4 * t * D₂ t + 2 * N * D t)) t := by
  convert (Real.hasDerivAt_rpow_const (p := N / 2) (Or.inl ht.ne')).mul hD using 1
  have hp : t ^ (N / 2) = t ^ (N / 2 - 1) * t := by
    rw [Real.rpow_sub_one ht.ne']
    field_simp
  rw [hp]
  ring

/-- A monotone function on the positive ray with right limit zero is nonnegative.
The value assigned to the function at zero is irrelevant. -/
theorem nonneg_of_monotoneOn_pos_of_tendsto_zero
    {G : ℝ → ℝ} (hG : MonotoneOn G (Ioi 0))
    (hlim : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    0 ≤ G t := by
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs hst
  exact hG hs ht hst.le

/-- The radial differential inequality with the minimal zero-flux boundary
condition used by the integrating-factor argument.  No regularity at the origin
is required for the derivative function itself. -/
theorem monotoneOn_of_radial_operator_nonneg_of_zero_flux
    {F D D₂ : ℝ → ℝ} {N : ℝ}
    (hF : ContinuousOn F (Ici 0))
    (hFD : ∀ t : ℝ, 0 < t → HasDerivAt F (D t) t)
    (hDD₂ : ∀ t : ℝ, 0 < t → HasDerivAt D (D₂ t) t)
    (hflux : Tendsto (fun t : ℝ => t ^ (N / 2) * D t) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hoperator : ∀ t : ℝ, 0 < t → 0 ≤ 4 * t * D₂ t + 2 * N * D t) :
    MonotoneOn F (Ici 0) := by
  let G : ℝ → ℝ := fun t => t ^ (N / 2) * D t
  have hGderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt G
        ((1 / 4 : ℝ) * t ^ (N / 2 - 1) * (4 * t * D₂ t + 2 * N * D t)) t :=
    fun t ht => hasDerivAt_radialIntegratingFactor ht (hDD₂ t ht)
  have hGmono : MonotoneOn G (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun t ht => (hGderiv t ht).continuousAt.continuousWithinAt)
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
      exact (hGderiv t ht').hasDerivWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ht'.le _))
        (hoperator t ht')
  have hDnonneg : ∀ t : ℝ, 0 < t → 0 ≤ D t := by
    intro t ht
    have hGt : 0 ≤ G t := nonneg_of_monotoneOn_pos_of_tendsto_zero hGmono hflux ht
    exact nonneg_of_mul_nonneg_right hGt (Real.rpow_pos_of_pos ht _)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hF
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hFD t ht').hasDerivWithinAt
  · intro t ht
    exact hDnonneg t (by simpa only [interior_Ici, mem_Ioi] using ht)

/-- A finite right limit of the first derivative implies the required zero flux
for every positive real `N`. -/
theorem monotoneOn_of_radial_operator_nonneg_of_derivative_limit
    {F D D₂ : ℝ → ℝ} {N L : ℝ} (hN : 0 < N)
    (hF : ContinuousOn F (Ici 0))
    (hFD : ∀ t : ℝ, 0 < t → HasDerivAt F (D t) t)
    (hDD₂ : ∀ t : ℝ, 0 < t → HasDerivAt D (D₂ t) t)
    (hlim : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hoperator : ∀ t : ℝ, 0 < t → 0 ≤ 4 * t * D₂ t + 2 * N * D t) :
    MonotoneOn F (Ici 0) := by
  apply monotoneOn_of_radial_operator_nonneg_of_zero_flux hF hFD hDD₂
    (hoperator := hoperator)
  have hhalf : 0 < N / 2 := by positivity
  have hpow : Tendsto (fun t : ℝ => t ^ (N / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t ^ (N / 2)) 0 :=
      (Real.continuous_rpow_const hhalf.le).continuousAt
    simpa only [Real.zero_rpow hhalf.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul] using hpow.mul hlim

/-- A nonnegative radial differential operator forces monotonicity when the first
derivative extends continuously to the origin.  This includes every positive real
radial dimension `N`; integrality is not used. -/
theorem monotoneOn_of_radial_operator_nonneg
    {F D D₂ : ℝ → ℝ} {N : ℝ} (hN : 0 < N)
    (hF : ContinuousOn F (Ici 0))
    (hD : ContinuousOn D (Ici 0))
    (hFD : ∀ t : ℝ, 0 < t → HasDerivAt F (D t) t)
    (hDD₂ : ∀ t : ℝ, 0 < t → HasDerivAt D (D₂ t) t)
    (hoperator : ∀ t : ℝ, 0 < t → 0 ≤ 4 * t * D₂ t + 2 * N * D t) :
    MonotoneOn F (Ici 0) := by
  let G : ℝ → ℝ := fun t => t ^ (N / 2) * D t
  have hhalf : 0 < N / 2 := by positivity
  have hG : ContinuousOn G (Ici 0) :=
    (Real.continuous_rpow_const hhalf.le).continuousOn.mul hD
  have hGderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt G
        ((1 / 4 : ℝ) * t ^ (N / 2 - 1) * (4 * t * D₂ t + 2 * N * D t)) t :=
    fun t ht => hasDerivAt_radialIntegratingFactor ht (hDD₂ t ht)
  have hGmono : MonotoneOn G (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hG
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact (hGderiv t ht').hasDerivWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ht'.le _))
        (hoperator t ht')
  have hDnonneg : ∀ t : ℝ, 0 < t → 0 ≤ D t := by
    intro t ht
    have hGt := hGmono (show (0 : ℝ) ∈ Ici 0 from by simp) ht.le ht.le
    have hGzero : G 0 = 0 := by simp [G, Real.zero_rpow hhalf.ne']
    rw [hGzero] at hGt
    exact nonneg_of_mul_nonneg_right hGt (Real.rpow_pos_of_pos ht _)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hF
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hFD t ht').hasDerivWithinAt
  · intro t ht
    exact hDnonneg t (by simpa only [interior_Ici, mem_Ioi] using ht)

end Wishart
end CanonicalSource91

section CanonicalSource92
/- Source: Wishart/RadialOrigin.lean -/



/-!
# The origin of an even square-root profile

If J is even and twice differentiable at zero, then the first derivative of
F(t) = J(sqrt(t)) has right limit J''(0)/2.  This supplies the finite-limit
condition used by the radial integrating-factor argument.  The hypotheses
refer only to ordinary derivatives of J, and contain no radial identity or
probability-law assumption.
-/

open Filter Set
open scoped Topology

namespace Wishart

theorem hasDerivAt_even_zero {J : ℝ → ℝ} {a : ℝ}
    (heven : ∀ s, J (-s) = J s) (hJ : HasDerivAt J a 0) : a = 0 := by
  have hneg : HasDerivAt (fun s : ℝ => J (-s)) (-a) 0 := by
    simpa only [Function.comp_def, mul_neg_one] using
      hJ.comp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
  have heq : (fun s : ℝ => J (-s)) = J := funext heven
  rw [heq] at hneg
  have ha := hJ.unique hneg
  linarith

theorem tendsto_sqrt_pos_zero :
    Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.mpr ht

/-- The derivative quotient at the square-root origin has the required finite
right limit whenever the original derivative vanishes at zero. -/
theorem tendsto_sqrt_derivative_quotient {D : ℝ → ℝ} {L : ℝ}
    (hzero : D 0 = 0) (hD : HasDerivAt D L 0) :
    Tendsto (fun t : ℝ => D (Real.sqrt t) / (2 * Real.sqrt t))
      (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
  have hquot : Tendsto (fun s : ℝ => D s / s)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hD.tendsto_slope_zero_right
  have hlim := (hquot.comp tendsto_sqrt_pos_zero).mul
    (tendsto_const_nhds (x := (1 / 2 : ℝ)))
  convert hlim using 1
  · funext t
    simp only [Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  · ring

/-- The ordinary derivative away from zero of the square-root profile. -/
theorem hasDerivAt_sqrt_profile {J D : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hJ : HasDerivAt J (D (Real.sqrt t)) (Real.sqrt t)) :
    HasDerivAt (fun s : ℝ => J (Real.sqrt s))
      (D (Real.sqrt t) / (2 * Real.sqrt t)) t := by
  simpa only [Function.comp_def, mul_one_div] using
    hJ.comp t (Real.hasDerivAt_sqrt ht.ne')

/-- An even profile with a derivative differentiable at zero meets the exact
finite-right-limit hypothesis of `monotoneOn_of_radial_operator_nonneg_of_derivative_limit`.
No integer-dimensional assumption appears. -/
theorem tendsto_deriv_sqrt_profile_of_even {J D : ℝ → ℝ} {L : ℝ}
    (heven : ∀ s, J (-s) = J s)
    (hJzero : HasDerivAt J (D 0) 0)
    (hJ : ∀ s, 0 < s → HasDerivAt J (D s) s)
    (hD : HasDerivAt D L 0) :
    Tendsto (deriv (fun t : ℝ => J (Real.sqrt t)))
      (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
  apply (tendsto_sqrt_derivative_quotient
    (hasDerivAt_even_zero heven hJzero) hD).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hasDerivAt_sqrt_profile ht (hJ (Real.sqrt t) (Real.sqrt_pos.mpr ht))).deriv.symm

/-- The square-root profile has the corresponding right derivative at the
origin itself.  This justifies the boundary value as well as its finite limit. -/
theorem hasDerivWithinAt_sqrt_profile_zero_of_even {J D : ℝ → ℝ} {L : ℝ}
    (heven : ∀ s, J (-s) = J s)
    (hJzero : HasDerivAt J (D 0) 0)
    (hJ : ∀ s, 0 < s → HasDerivAt J (D s) s)
    (hD : HasDerivAt D L 0) :
    HasDerivWithinAt (fun t : ℝ => J (Real.sqrt t)) (L / 2) (Ici 0) 0 := by
  have hlim := tendsto_sqrt_derivative_quotient
    (hasDerivAt_even_zero heven hJzero) hD
  have hcont : ContinuousAt (fun t : ℝ => J (Real.sqrt t)) 0 := by
    have hJcont : ContinuousAt J (Real.sqrt (0 : ℝ)) := by
      simpa only [Real.sqrt_zero] using hJzero.continuousAt
    exact hJcont.comp Real.continuous_sqrt.continuousAt
  have hzero : Tendsto (fun t : ℝ => J (Real.sqrt t) - J 0)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero, sub_self] using
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds (x := J 0))
  have hquot : Tendsto (fun t : ℝ => (J (Real.sqrt t) - J 0) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (L / 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun t => D (Real.sqrt t) / (2 * Real.sqrt t))
      (g' := fun _ => (1 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hasDerivAt_sqrt_profile ht
        (hJ (Real.sqrt t) (Real.sqrt_pos.mpr ht))).sub_const (J 0)
    · exact Eventually.of_forall fun t => hasDerivAt_id t
    · exact Eventually.of_forall fun _ => one_ne_zero
    · exact hzero
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
    · simpa only [div_one] using hlim
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have hslope : slope (fun t : ℝ => J (Real.sqrt t)) 0 =
      (fun t : ℝ => (J (Real.sqrt t) - J 0) / t) := by
    funext t
    rw [slope_def_field]
    simp only [Real.sqrt_zero, sub_zero]
  rw [hslope]
  exact hquot

end Wishart
end CanonicalSource92

section CanonicalSource93
/- Source: Wishart/RadialMeanMonotonicity.lean -/



/-!
# Monotonicity of the actual radial expectation

The even signed-radius profile supplies the zero-flux condition at the origin.
The differential identity is the theorem proved from the two Stein formulas;
it is not a hypothesis of the monotonicity result below.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set Topology Matrix

namespace WishartVerification

variable {p : ℕ}

theorem rankOneSymmetric_neg (w : EuclideanSpace ℝ (Fin p)) :
    rankOneSymmetric (-w) = rankOneSymmetric w := by
  apply Subtype.ext
  ext i j
  simp [coe_rankOneSymmetric, Matrix.vecMulVec_apply]

theorem rankOneSymmetric_posSemidef (w : EuclideanSpace ℝ (Fin p)) :
    (rankOneSymmetric w : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  simpa only [coe_rankOneSymmetric, star_trivial] using
    Matrix.posSemidef_vecMulVec_self_star (fun i => w i)

theorem map_neg_centered_multivariateGaussian {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C).map (fun z => -z) =
      multivariateGaussian 0 C := by
  have h := map_affine_multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) hC
    (-(1 : Matrix (Fin p) (Fin p) ℝ)) 0
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.neg_mulVec,
    Matrix.transpose_neg] using h

theorem radialExpectation_even {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (∫ Y : RadialInputSpace p, f (radialInput v (-r) Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) =
    ∫ Y : RadialInputSpace p, f (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μW := nonsingularWishartMeasure ν C
  let μZ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C
  let μ := μW.prod μZ
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hint (s : ℝ) : Integrable (fun Y => f (radialInput v s Y)) μ :=
    integrable_temperate_of_allNormMoments hμ (hf.comp (hasTemperateGrowth_radialInput_slice v s))
  rw [integral_prod _ (hint (-r)), integral_prod _ (hint r)]
  apply integral_congr_ae
  filter_upwards with W
  have hneg : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin p) => -z) μZ μZ :=
    ⟨by fun_prop, map_neg_centered_multivariateGaussian hC.posSemidef⟩
  have h := hneg.integral_comp (MeasurableEquiv.neg _).measurableEmbedding
    (fun z => f (W + rankOneSymmetric (z + r • v)))
  change (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
    ∫ z, f (W + rankOneSymmetric (z + r • v)) ∂μZ
  calc
    (∫ z, f (W + rankOneSymmetric (z + (-r) • v)) ∂μZ) =
        ∫ z, f (W + rankOneSymmetric (-z + r • v)) ∂μZ := by
      apply integral_congr_ae
      filter_upwards with z
      have he : -z + r • v = -(z + (-r) • v) := by module
      rw [he, rankOneSymmetric_neg]
    _ = _ := h

theorem ae_radialInput_posSemidef (ν : ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    ∀ᵐ Y : RadialInputSpace p
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C),
      (radialInput v r Y : Matrix (Fin p) (Fin p) ℝ).PosSemidef := by
  have hW : ∀ᵐ Y : RadialInputSpace p
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C),
      (Y.1 : Matrix (Fin p) (Fin p) ℝ).PosDef :=
    Measure.quasiMeasurePreserving_fst.ae (ae_posDef_nonsingularWishartMeasure ν C)
  filter_upwards [hW] with Y hY
  exact hY.posSemidef.add (rankOneSymmetric_posSemidef (Y.2 + r • v))

/-- The derivative of the derivative of a square-root profile. -/
theorem hasDerivAt_sqrt_profile_derivative {D E : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hD : HasDerivAt D (E (Real.sqrt t)) (Real.sqrt t)) :
    HasDerivAt (fun s => D (Real.sqrt s) / (2 * Real.sqrt s))
      ((E (Real.sqrt t) - D (Real.sqrt t) / Real.sqrt t) / (4 * t)) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have h := (hD.comp t hs).div (hs.const_mul 2) (by positivity : 2 * Real.sqrt t ≠ 0)
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsquare := Real.sq_sqrt ht.le
  have heq :
      (E (Real.sqrt t) * (1 / (2 * Real.sqrt t)) * (2 * Real.sqrt t) -
        D (Real.sqrt t) * (2 * (1 / (2 * Real.sqrt t)))) / (2 * Real.sqrt t) ^ 2 =
      (E (Real.sqrt t) - D (Real.sqrt t) / Real.sqrt t) / (4 * t) := by
    generalize hrt : Real.sqrt t = r at hr hsquare ⊢
    rw [← hsquare]
    field_simp [hr.ne']
    <;> ring
  simpa only [Function.comp_def, Pi.div_def] using h.congr_deriv heq

/-- Polynomial-growth smooth tests with nonnegative radial generator have a
nondecreasing expectation under the genuine real-shape radial Wishart law. -/
theorem monotoneOn_radialExpectation_of_generator_nonneg
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p))
    (hgenerator : ∀ X : SymmetricMatrix p,
      (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
      0 ≤ symmetricRadialGenerator (ν + 1) v f X) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p, f (radialInput v (Real.sqrt t) Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μ := (nonsingularWishartMeasure ν C).prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  let J : ℝ → ℝ := fun r => ∫ Y, f (radialInput v r Y) ∂μ
  let J₁ : ℝ → ℝ := fun r => ∫ Y, radialFirstIntegrand f v r Y ∂μ
  let J₂ : ℝ → ℝ := fun r => ∫ Y, radialSecondIntegrand f v r Y ∂μ
  let F : ℝ → ℝ := fun t => J (Real.sqrt t)
  let D : ℝ → ℝ := fun t => J₁ (Real.sqrt t) / (2 * Real.sqrt t)
  let D₂ : ℝ → ℝ := fun t =>
    (J₂ (Real.sqrt t) - J₁ (Real.sqrt t) / Real.sqrt t) / (4 * t)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hJ (r : ℝ) : HasDerivAt J (J₁ r) r := hasDerivAt_radialExpectation hμ hf v r
  have hJ₁ (r : ℝ) : HasDerivAt J₁ (J₂ r) r := hasDerivAt_radialFirstExpectation hμ hf v r
  have heven (r : ℝ) : J (-r) = J r := radialExpectation_even hC hν hf v r
  have hN : 0 < ν + 1 := by have := Nat.cast_nonneg (α := ℝ) p; linarith
  apply Wishart.monotoneOn_of_radial_operator_nonneg_of_derivative_limit
    (N := ν + 1) (D := D) (D₂ := D₂) (L := J₂ 0 / 2) hN
  · exact ((continuous_iff_continuousAt.mpr fun r => (hJ r).continuousAt).comp
      Real.continuous_sqrt).continuousOn
  · intro t ht
    exact Wishart.hasDerivAt_sqrt_profile ht (hJ (Real.sqrt t))
  · intro t ht
    exact hasDerivAt_sqrt_profile_derivative ht (hJ₁ (Real.sqrt t))
  · exact Wishart.tendsto_sqrt_derivative_quotient
      (Wishart.hasDerivAt_even_zero heven (hJ 0)) (hJ₁ 0)
  · intro t ht
    have hrad := radial_generator_identity hC hν hf v (Real.sqrt t)
    have hnonneg : 0 ≤ ∫ Y, symmetricRadialGenerator (ν + 1) v f
        (radialInput v (Real.sqrt t) Y) ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_radialInput_posSemidef ν C v (Real.sqrt t)] with Y hY
      exact hgenerator _ hY
    have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hmain : 0 ≤ J₂ (Real.sqrt t) + ν * J₁ (Real.sqrt t) / Real.sqrt t := by
      apply nonneg_of_mul_nonneg_right (a := Real.sqrt t)
      · convert mul_nonneg hr.le hnonneg using 1
        rw [hrad]
        dsimp [J₁, J₂]
        field_simp
        ring
      · exact hr
    dsimp [D, D₂]
    convert hmain using 1
    field_simp
    ring

end WishartVerification
end
end CanonicalSource93

section CanonicalSource94
/- Source: Wishart/RadialCompressionMonotonicity.lean -/



/-!
# Removing the determinant regularization

Uniform polynomial envelopes are obtained before taking the limit.  The final
monotonicity theorem concerns ordinary, unregularized determinant powers.
-/

noncomputable section

open Matrix MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set Topology
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ}

def determinantRegularization (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem determinantRegularization_pos (n : ℕ) : 0 < determinantRegularization n := by
  unfold determinantRegularization
  positivity

theorem determinantRegularization_le_one (n : ℕ) : determinantRegularization n ≤ 1 := by
  unfold determinantRegularization
  exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem tendsto_determinantRegularization :
    Tendsto determinantRegularization atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem hasTemperateGrowth_radial_regularized_det {k : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    (fun q : ℝ × RadialInputSpace p =>
      (regularizedCompression q.1 B M (radialInput v r q.2)).det).HasTemperateGrowth := by
  have hV := (hasTemperateGrowth_radialInput_slice v r).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace p)).hasTemperateGrowth
  have ht := (ContinuousLinearMap.fst ℝ ℝ (RadialInputSpace p)).hasTemperateGrowth
  apply hasTemperateGrowth_matrix_det
  intro i j
  let L : SymmetricMatrix p →L[ℝ] ℝ :=
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)).comp (compressionCLM M)
  exact ((Function.HasTemperateGrowth.const (B i j)).add (L.hasTemperateGrowth.comp hV)).add
    (ht.mul (Function.HasTemperateGrowth.const ((1 : Matrix k k ℝ) i j)))

theorem tendsto_regularizedCompressionProduct {ι : Type*} [Fintype ι]
    (D : ι → CompressionData p) (hB : ∀ i, (D i).offset.PosSemidef)
    (hη : ∀ i, 0 ≤ (D i).exponent) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    Tendsto (fun n => regularizedCompressionProduct (determinantRegularization n) D X)
      atTop (𝓝 (compressionProduct D X)) := by
  unfold regularizedCompressionProduct compressionProduct
  apply tendsto_finsetProd
  intro i hi
  have hc : Continuous (fun ε : ℝ =>
      (regularizedCompression ε (D i).offset (D i).linear X).det ^ (D i).exponent) :=
    (Real.continuous_rpow_const (hη i)).comp (by
      unfold regularizedCompression
      fun_prop)
  have hlim := hc.continuousAt.tendsto.comp tendsto_determinantRegularization
  have heq (n : ℕ) := smoothRegularizedDetPower_eq (determinantRegularization_pos n)
    (D i).exponent (hB i) (D i).linear hX
  simpa only [heq, regularizedCompression, compressionCLM_apply, zero_smul, add_zero,
    Function.comp_def] using hlim

theorem radial_regularized_product_integral_tendsto {ι : Type*} [Fintype ι]
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    (D : ι → CompressionData p) (hB : ∀ i, (D i).offset.PosSemidef)
    (hη : ∀ i, 0 ≤ (D i).exponent)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    Tendsto (fun n => ∫ Y : RadialInputSpace p,
      regularizedCompressionProduct (determinantRegularization n) D (radialInput v r Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) atTop
      (𝓝 (∫ Y : RadialInputSpace p, compressionProduct D (radialInput v r Y)
        ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C))) := by
  classical
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  let μ := (nonsingularWishartMeasure ν C).prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C)
  have hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ :=
    allFiniteNormMoments_prod (allFiniteMoments_wishart_norm ν C) allFiniteMoments_gaussian_norm
  have hpoly (i : ι) := norm_temperate_uniform_parameter
    (hasTemperateGrowth_radial_regularized_det (D i).offset (D i).linear v r) 0
  choose k A hA hbound using hpoly
  let bound : RadialInputSpace p → ℝ := fun Y =>
    ∏ i, (A i * (1 + ‖Y‖) ^ k i) ^ (D i).exponent
  have hb : Integrable bound μ := by
    apply HasAllFiniteMoments.integrable
    apply HasAllFiniteMoments.finset_prod
    intro i hi
    have hpow := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (k i : ℝ) by positivity)
    have hAi : HasAllFiniteMoments (fun Y : RadialInputSpace p => A i * (1 + ‖Y‖) ^ k i) μ := by
      simpa only [Real.rpow_natCast] using hpow.const_mul (A i)
    exact hAi.rpow (hη i)
  refine tendsto_integral_of_dominated_convergence bound ?_ hb ?_ ?_
  · intro n
    exact ((hasTemperateGrowth_regularizedCompressionProduct (determinantRegularization_pos n) D).comp
      (hasTemperateGrowth_radialInput_slice v r)).1.continuous.aestronglyMeasurable
  · intro n
    filter_upwards [ae_radialInput_posSemidef ν C v r] with Y hY
    unfold regularizedCompressionProduct bound
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      rw [smoothRegularizedDetPower_eq (determinantRegularization_pos n)
        (D i).exponent (hB i) (D i).linear hY]
      have hdet : 0 ≤ (regularizedCompression (determinantRegularization n)
          (D i).offset (D i).linear (radialInput v r Y)).det :=
        (regularizedCompression_posDef (determinantRegularization_pos n)
          (hB i) (D i).linear hY).det_pos.le
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hdet _)]
      apply Real.rpow_le_rpow hdet _ (hη i)
      have heps : determinantRegularization n ∈ Icc ((0 : ℝ) - 1) (0 + 1) :=
        ⟨by linarith [determinantRegularization_pos n], by simpa using determinantRegularization_le_one n⟩
      simpa only [Real.norm_of_nonneg hdet] using hbound i _ heps Y
  · filter_upwards [ae_radialInput_posSemidef ν C v r] with Y hY
    exact tendsto_regularizedCompressionProduct D hB hη hY

/-- The full unregularized comparison needed for every multi-block split in
the real Wishart theorem.  Sizes, offsets, compressions, and nonnegative powers
may vary independently across the finite family. -/
theorem monotoneOn_radial_compressionProduct {ι : Type*} [Fintype ι]
    {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {ν : ℝ} (hν : (p : ℝ) - 1 < ν)
    (D : ι → CompressionData p) (hB : ∀ i, (D i).offset.PosSemidef)
    (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ ν + 1)
    (v : EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun t : ℝ => ∫ Y : RadialInputSpace p,
      compressionProduct D (radialInput v (Real.sqrt t) Y)
      ∂(nonsingularWishartMeasure ν C).prod (multivariateGaussian 0 C)) (Ici 0) := by
  intro s hs t ht hst
  have hm (n : ℕ) := monotoneOn_radialExpectation_of_generator_nonneg hC hν
    (hasTemperateGrowth_regularizedCompressionProduct (determinantRegularization_pos n) D) v
    (fun X hX => regularizedCompressionProduct_generator_nonneg
      (determinantRegularization_pos n) D hB hη hsize hX v)
  exact le_of_tendsto_of_tendsto
    (radial_regularized_product_integral_tendsto hC hν D hB hη v (Real.sqrt s))
    (radial_regularized_product_integral_tendsto hC hν D hB hη v (Real.sqrt t))
    (Filter.Eventually.of_forall fun n => hm n hs ht hst)

end WishartVerification
end
end CanonicalSource94

section CanonicalSource95
/- Source: Wishart/RegressionMonotonicity.lean -/



/-!
# Conditional spectral monotonicity from the actual one-row radial theorem

One Gaussian row is separated from the independent Bartlett regression source.
The other rows contribute a positive semidefinite offset to every compression.
The real-shape radial theorem therefore compares each coordinate, and finitely
many coordinate replacements give the full product order. Compactness of the
orthogonal group supplies the domination needed for every fixed-spectrum Haar
average; all noise moments come from the actual Gaussian and Wishart laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart

theorem monotoneOn_nonnegative_pi_of_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ)
    (hf : ∀ x i, MonotoneOn (fun t => f (Function.update x i t)) (Set.Ici 0)) :
    MonotoneOn f (Set.Ici (0 : ι → ℝ)) := by
  intro x hx y hy hxy
  have hchain (s : Finset ι) : f x ≤ f (fun i => if i ∈ s then y i else x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using (le_refl (f x))
    | @insert i s hi ih =>
      let z : ι → ℝ := fun j => if j ∈ s then y j else x j
      have hz : z i = x i := by simp [z, hi]
      have heq : Function.update z i (y i) =
          (fun j => if j ∈ insert i s then y j else x j) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [Function.update_of_ne hji, z, hji]
      have hstep := hf z i (hx i) (hy i) (hxy i)
      dsimp only at hstep
      rw [← hz, Function.update_eq_self, heq] at hstep
      exact ih.trans hstep
  simpa using hchain Finset.univ

def rowBackground {q m : ℕ} (v : Fin q → EuclideanSpace ℝ (Fin m))
    (lam : Fin q → ℝ) (z : Fin q → EuclideanSpace ℝ (Fin m)) : SymmetricMatrix m :=
  ∑ a, rankOneSymmetric (z a + Real.sqrt (lam a) • v a)

def shiftedRowsSym {q m : ℕ} (v : Fin q → EuclideanSpace ℝ (Fin m))
    (lam : Fin q → ℝ) (x : RegressionNoise q m) : SymmetricMatrix m :=
  x.2 + rowBackground v lam x.1

@[simp] theorem coe_rowBackground {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (z : Fin q → EuclideanSpace ℝ (Fin m)) :
    (rowBackground v lam z : Matrix (Fin m) (Fin m) ℝ) =
      ∑ a, Matrix.vecMulVec (fun i => z a i + Real.sqrt (lam a) * v a i)
        (fun i => z a i + Real.sqrt (lam a) * v a i) := by
  simp [rowBackground, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

@[simp] theorem coe_shiftedRowsSym {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (x : RegressionNoise q m) :
    (shiftedRowsSym v lam x : Matrix (Fin m) (Fin m) ℝ) = shiftedRowsGram v lam x := by
  simp only [shiftedRowsSym, Submodule.coe_add, coe_rowBackground, shiftedRowsGram]

@[fun_prop] theorem measurable_rowBackground {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ) :
    Measurable (rowBackground v lam) := by
  unfold rowBackground
  apply Finset.measurable_sum
  intro a _
  exact (hasTemperateGrowth_rankOneSymmetric (p := m)).1.continuous.measurable.comp
    ((measurable_pi_apply a).add measurable_const)

@[fun_prop] theorem measurable_shiftedRowsSym {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ) :
    Measurable (shiftedRowsSym v lam) := by
  exact measurable_snd.add ((measurable_rowBackground v lam).comp measurable_fst)

theorem rowBackground_posSemidef {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (z : Fin q → EuclideanSpace ℝ (Fin m)) :
    (rowBackground v lam z : Matrix (Fin m) (Fin m) ℝ).PosSemidef := by
  rw [coe_rowBackground]
  apply Matrix.posSemidef_sum
  intro a _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (fun i => z a i + Real.sqrt (lam a) * v a i)

def addCompressionOffset {m : ℕ} {ι : Type*}
    (D : ι → CompressionData m) (B : SymmetricMatrix m) : ι → CompressionData m :=
  fun i => { D i with offset := (D i).offset + (D i).linearᵀ *
    (B : Matrix (Fin m) (Fin m) ℝ) * (D i).linear }

theorem compressionProduct_add {m : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData m) (B X : SymmetricMatrix m) :
    compressionProduct D (B + X) = compressionProduct (addCompressionOffset D B) X := by
  apply Finset.prod_congr rfl
  intro i hi
  change (((D i).offset + (D i).linearᵀ *
      ((B : Matrix (Fin m) (Fin m) ℝ) + (X : Matrix (Fin m) (Fin m) ℝ)) *
        (D i).linear).det) ^ (D i).exponent =
    ((((D i).offset + (D i).linearᵀ * (B : Matrix (Fin m) (Fin m) ℝ) *
        (D i).linear) + (D i).linearᵀ * (X : Matrix (Fin m) (Fin m) ℝ) *
        (D i).linear).det) ^ (D i).exponent
  apply congrArg (fun A : Matrix (Fin (D i).size) (Fin (D i).size) ℝ =>
    A.det ^ (D i).exponent)
  simp only [Matrix.mul_add, Matrix.add_mul, add_assoc]

@[fun_prop] theorem measurable_compressionProduct {m : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData m) : Measurable (compressionProduct D) := by
  apply Finset.measurable_prod
  intro i hi
  exact (by fun_prop : Measurable (fun X : SymmetricMatrix m =>
    ((D i).offset + (D i).linearᵀ * (X : Matrix (Fin m) (Fin m) ℝ) *
      (D i).linear).det)).pow_const _

theorem compressionProduct_nonneg {m : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData m) (hB : ∀ i, (D i).offset.PosSemidef)
    {X : SymmetricMatrix m} (hX : (X : Matrix (Fin m) (Fin m) ℝ).PosSemidef) :
    0 ≤ compressionProduct D X := by
  apply Finset.prod_nonneg
  intro i hi
  apply Real.rpow_nonneg
  apply Matrix.PosSemidef.det_nonneg
  apply (hB i).add
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hX.conjTranspose_mul_mul_same (D i).linear

theorem allFiniteMoments_compressionProduct_of_entries {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData m) (hη : ∀ i, 0 ≤ (D i).exponent)
    (X : Ω → SymmetricMatrix m)
    (hX : ∀ i j, HasAllFiniteMoments
      (fun x => (X x : Matrix (Fin m) (Fin m) ℝ) i j) μ) :
    HasAllFiniteMoments (fun x => compressionProduct D (X x)) μ := by
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro a ha
  apply HasAllFiniteMoments.rpow _ (hη a)
  apply HasAllFiniteMoments.det
  intro i j
  apply (HasAllFiniteMoments.const ((D a).offset i j)).add
  exact HasAllFiniteMoments.matrix_right_mul_entry _ (D a).linear
    (fun i j => HasAllFiniteMoments.matrix_left_mul_entry _ (D a).linearᵀ hX i j) i j

def separateRegressionRow {q m : ℕ} (a : Fin (q + 1))
    (x : RegressionNoise (q + 1) m) :
    (Fin q → EuclideanSpace ℝ (Fin m)) × RadialInputSpace m :=
  (fun j => x.1 (a.succAbove j), (x.2, x.1 a))

theorem measurePreserving_separateRegressionRow {q m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) (ν : Measure (SymmetricMatrix m)) [SFinite ν]
    (a : Fin (q + 1)) :
    MeasurePreserving (separateRegressionRow (m := m) a)
      (gaussianResidualMeasure (q + 1) C ν)
      ((Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)).prod
        (ν.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C))) :=
  (measurePreserving_prodAssoc _ _ _).comp (measurePreserving_splitRegressionRow C ν a)

theorem shiftedRowsSym_separate {q m : ℕ}
    (v : Fin (q + 1) → EuclideanSpace ℝ (Fin m)) (lam : Fin (q + 1) → ℝ)
    (a : Fin (q + 1)) (t : ℝ) (x : RegressionNoise (q + 1) m) :
    shiftedRowsSym v (Function.update lam a t) x =
      rowBackground (v ∘ a.succAbove) (lam ∘ a.succAbove) (separateRegressionRow a x).1 +
        radialInput (v a) (Real.sqrt t) (separateRegressionRow a x).2 := by
  unfold shiftedRowsSym rowBackground
  rw [Fin.sum_univ_succAbove _ a]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne _ _),
    separateRegressionRow, Function.comp_apply, radialInput]
  abel

theorem monotoneOn_shiftedRows_compressionProduct_coordinate
    {q m : ℕ} {ν : ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) (hν : (m : ℝ) - 1 < ν)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ) (a : Fin q) :
    MonotoneOn (fun t : ℝ => ∫ x,
      compressionProduct D (shiftedRowsSym v (Function.update lam a t) x)
        ∂gaussianResidualMeasure q C (nonsingularWishartMeasure ν C)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C
    let μ := Measure.pi (fun _ : Fin q => γ)
    let ρ := (nonsingularWishartMeasure ν C).prod γ
    let B (z : Fin q → EuclideanSpace ℝ (Fin m)) :=
      rowBackground (v ∘ a.succAbove) (lam ∘ a.succAbove) z
    let F (t : ℝ) (y : (Fin q → EuclideanSpace ℝ (Fin m)) × RadialInputSpace m) :=
      compressionProduct D (B y.1 + radialInput (v a) (Real.sqrt t) y.2)
    have hsplit := measurePreserving_separateRegressionRow C (nonsingularWishartMeasure ν C) a
    have hFmeas (t : ℝ) : Measurable (F t) := by
      apply (measurable_compressionProduct D).comp
      apply ((measurable_rowBackground _ _).comp measurable_fst).add
      exact ((hasTemperateGrowth_radialInput_slice (v a) (Real.sqrt t)).1.continuous.measurable).comp
        measurable_snd
    have hFcomp (t : ℝ) : F t ∘ separateRegressionRow a =
        (fun x => compressionProduct D (shiftedRowsSym v (Function.update lam a t) x)) := by
      funext x
      dsimp only [F, B, Function.comp_apply]
      rw [shiftedRowsSym_separate]
    have hFi (t : ℝ) : Integrable (F t) (μ.prod ρ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      apply HasAllFiniteMoments.integrable
      apply allFiniteMoments_compressionProduct_of_entries D hη
      intro i j
      simpa only [coe_shiftedRowsSym] using
        allFiniteMoments_shiftedRowsGram_entry C
          (fun i j => allFiniteMoments_wishart_entry (α := ν) (Sigma := C) i j)
          v (Function.update lam a t) i j
    have heq (t : ℝ) :
        (∫ x, compressionProduct D (shiftedRowsSym v (Function.update lam a t) x)
          ∂gaussianResidualMeasure (q + 1) C (nonsingularWishartMeasure ν C)) =
        ∫ z, ∫ Y, F t (z, Y) ∂ρ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x
        ∂gaussianResidualMeasure (q + 1) C (nonsingularWishartMeasure ν C)) (hFcomp t).symm
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hFi s).integral_prod_left (hFi t).integral_prod_left
    apply Filter.Eventually.of_forall
    intro z
    have hBz : ∀ i, ((addCompressionOffset D (B z)) i).offset.PosSemidef := by
      intro i
      apply (hB i).add
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (rowBackground_posSemidef _ _ z).conjTranspose_mul_mul_same (D i).linear
    simpa only [F, compressionProduct_add] using
      monotoneOn_radial_compressionProduct hC hν (addCompressionOffset D (B z))
        hBz hη hsize (v a) hs ht hst

theorem monotoneOn_shiftedRows_compressionProduct
    {q m : ℕ} {ν : ℝ} {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosDef) (hν : (m : ℝ) - 1 < ν)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ ν + 1)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x, compressionProduct D (shiftedRowsSym v lam x)
      ∂gaussianResidualMeasure q C (nonsingularWishartMeasure ν C))
      (Set.Ici (0 : Fin q → ℝ)) :=
  monotoneOn_nonnegative_pi_of_update _ fun lam a =>
    monotoneOn_shiftedRows_compressionProduct_coordinate hC hν D hB hη hsize v lam a

theorem monotoneOn_spectralConditionalMoment_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ n - q + 1) :
    MonotoneOn (fun lam => spectralConditionalMoment n C K (compressionProduct D) lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  have heq (lam : Fin q → ℝ) (x : RegressionNoise q m) :
      regressionGramWithMean (spectralRegressionMean K O lam) x =
        shiftedRowsSym (fun a => WithLp.toLp 2 (fun i => (Oᵀ * K) a i)) lam x := by
    apply Subtype.ext
    rw [regressionGramWithMean_spectral_eq_shiftedRowsGram, coe_shiftedRowsSym]
  simpa only [spectralConditionalMoment, heq, regressionNoiseMeasure, gaussianResidualMeasure] using
    monotoneOn_shiftedRows_compressionProduct hC hν D hB hη hsize
      (fun a => WithLp.toLp 2 (fun i => (Oᵀ * K) a i))

theorem regressionGramWithMean_posSemidef {q m : ℕ}
    (M : Matrix (Fin m) (Fin q) ℝ) (x : RegressionNoise q m)
    (hW : (x.2 : Matrix (Fin m) (Fin m) ℝ).PosSemidef) :
    (regressionGramWithMean M x : Matrix (Fin m) (Fin m) ℝ).PosSemidef := by
  apply Matrix.PosSemidef.add _ hW
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (M + gaussianRowMatrix x.1)

theorem spectralConditionalMoment_compressionProduct_nonneg
    {q m : ℕ} (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (lam : Fin q → ℝ) :
    0 ≤ spectralConditionalMoment n C K (compressionProduct D) lam O := by
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
  exact compressionProduct_nonneg D hB
    (regressionGramWithMean_posSemidef _ x hx.posSemidef)

theorem regressionSpectralAverage_compressionProduct_nonneg
    {q m : ℕ} (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (lam : Fin q → ℝ) :
    0 ≤ regressionSpectralAverage n C K (compressionProduct D) lam := by
  unfold regressionSpectralAverage
  apply parameterAverageOn_nonneg
  intro lam' _ O
  exact spectralConditionalMoment_compressionProduct_nonneg n C K ↑O D hB lam' 

theorem allFiniteMoments_continuous_compact {Ω : Type*} [TopologicalSpace Ω]
    [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Continuous f) :
    HasAllFiniteMoments f μ := by
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  intro p hp
  exact MemLp.of_bound hf.aestronglyMeasurable R
    (Filter.Eventually.of_forall fun x => hR x (Set.mem_univ x))

set_option maxHeartbeats 1000000 in
theorem integrable_haar_spectralConditionalMoment_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hη : ∀ i, 0 ≤ (D i).exponent) (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q =>
      spectralConditionalMoment n C K (compressionProduct D) lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hν
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  let μ := (haarProb (Spectral.Orth q)).prod (regressionNoiseMeasure n q m C)
  have hmean (i : Fin m) (a : Fin q) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        spectralRegressionMean K ↑y.1 lam i a) μ := by
    have hm : HasAllFiniteMoments
        (fun O : Spectral.Orth q => spectralRegressionMean K ↑O lam i a)
        (haarProb (Spectral.Orth q)) := by
      apply allFiniteMoments_continuous_compact
      unfold spectralRegressionMean
      fun_prop
    exact hm.comp_measurePreserving
      (measurePreserving_fst (μ := haarProb (Spectral.Orth q))
        (ν := regressionNoiseMeasure n q m C))
  have hz (i : Fin m) (a : Fin q) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m => y.2.1 a i) μ :=
    (allFiniteMoments_gaussian_coordinate 0 C i).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C) a).comp
        (measurePreserving_fst.comp measurePreserving_snd))
  have hW (i j : Fin m) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (y.2.2 : Matrix (Fin m) (Fin m) ℝ) i j) μ :=
    (allFiniteMoments_wishart_entry (α := n - q) (Sigma := C) i j).comp_measurePreserving
      (measurePreserving_snd.comp measurePreserving_snd)
  have hentry (i j : Fin m) : HasAllFiniteMoments
      (fun y : Spectral.Orth q × RegressionNoise q m =>
        (regressionGramWithMean (spectralRegressionMean K ↑y.1 lam) y.2 :
          Matrix (Fin m) (Fin m) ℝ) i j) μ := by
    have hsum := HasAllFiniteMoments.finset_sum (μ := μ) Finset.univ
      (fun (a : Fin q) (y : Spectral.Orth q × RegressionNoise q m) => (spectralRegressionMean K ↑y.1 lam i a + y.2.1 a i) *
        (spectralRegressionMean K ↑y.1 lam j a + y.2.1 a j))
      (fun a _ => ((hmean i a).add (hz i a)).mul ((hmean j a).add (hz j a)))
    simpa only [regressionGramWithMean, gaussianRowMatrix, Matrix.add_apply,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] using hsum.add (hW i j)
  exact (allFiniteMoments_compressionProduct_of_entries D hη _ hentry).integrable.integral_prod_left

/-- The actual Haar-averaged conditional product used in the principal split
is increasing on the exact positive ordered chamber. -/
theorem monotoneOn_regressionSpectralAverage_compressionProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {ι : Type*} [Fintype ι] (D : ι → CompressionData m)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    (hsize : ∀ i, ((D i).size : ℝ) + 1 ≤ n - q + 1) :
    MonotoneOn (regressionSpectralAverage n C K (compressionProduct D))
      (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_spectralConditionalMoment_compressionProduct hn hC K D hη lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_spectralConditionalMoment_compressionProduct hn hC K ↑O D hB hη hsize
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

end Wishart
end
end CanonicalSource95

section CanonicalSource96
/- Source: Wishart/PartitionDimensions.lean -/



open scoped Classical

/-!
# Automatic dimension bounds for disjoint principal blocks

When at least two blocks remain after a selected block, each remaining block
omits at least one residual coordinate. These finite-set facts are the reason
the radial rank condition imposes no restriction beyond the nonsingular real
Wishart shape range in Theorem 1.1.
-/

namespace WishartVerification

variable {p d : ℕ}

theorem PrincipalPartition.block_card_pos (P : PrincipalPartition p d) (i : Fin d) :
    0 < (P.block i).card := Finset.card_pos.mpr (P.nonempty i)

theorem PrincipalPartition.two_block_cards_le (P : PrincipalPartition p d)
    (i j : Fin d) (hij : i ≠ j) : (P.block i).card + (P.block j).card ≤ p := by
  have h := Finset.card_le_card (Finset.subset_univ (P.block i ∪ P.block j))
  simpa only [Finset.card_union_of_disjoint (P.disjoint hij), Finset.card_univ,
    Fintype.card_fin] using h

theorem PrincipalPartition.two_block_cards_add_one_le (P : PrincipalPartition p d)
    (i j k : Fin d) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (P.block i).card + (P.block j).card + 1 ≤ p := by
  obtain ⟨a, hak⟩ := P.nonempty k
  have hai : a ∉ P.block i := fun hai ↦ Finset.disjoint_left.mp (P.disjoint hki) hak hai
  have haj : a ∉ P.block j := fun haj ↦ Finset.disjoint_left.mp (P.disjoint hkj) hak haj
  have ha : a ∉ P.block i ∪ P.block j := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hai, haj⟩
  have h := Finset.card_le_card (Finset.subset_univ (insert a (P.block i ∪ P.block j)))
  simpa only [Finset.card_insert_of_notMem ha,
    Finset.card_union_of_disjoint (P.disjoint hij), Finset.card_univ,
    Fintype.card_fin] using h

theorem exists_third_block_index (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    ∃ k : Fin d, k ≠ i ∧ k ≠ j := by
  have hcard : ({i, j} : Finset (Fin d)).card < (Finset.univ : Finset (Fin d)).card := by
    simpa only [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin] using
      (lt_of_lt_of_le (by decide : 2 < 3) hd)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨k, ?_, ?_⟩
  · intro h
    apply hk
    simp [h]
  · intro h
    apply hk
    simp [h]

theorem PrincipalPartition.two_block_cards_add_one_le_of_three
    (P : PrincipalPartition p d) (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    (P.block i).card + (P.block j).card + 1 ≤ p := by
  obtain ⟨k, hki, hkj⟩ := exists_third_block_index hd i j hij
  exact P.two_block_cards_add_one_le i j k hij hki hkj

/-- The rowwise radial parameter meets the determinant-generator threshold
throughout the full admissible real-shape range whenever at least two other
nonempty partition blocks remain. -/
theorem PrincipalPartition.radial_rank_bound
    (P : PrincipalPartition p d) (hd : 3 ≤ d) (α : ℝ) (hα : (p : ℝ) - 1 < α)
    (selected other : Fin d) (hne : selected ≠ other) :
    (1 : ℝ) + (P.block other).card ≤ α - (P.block selected).card + 1 := by
  have hnat := P.two_block_cards_add_one_le_of_three hd selected other hne
  have hreal : ((P.block selected).card : ℝ) + (P.block other).card + 1 ≤ p := by
    exact_mod_cast hnat
  linarith

end WishartVerification
end CanonicalSource96

section CanonicalSource97
/- Source: Wishart/MomentAssembly.lean -/



open scoped Classical
open MeasureTheory ProbabilityTheory

/-!
# Assembling selected splits and strict active pairs

This file proves the finite induction and equality implications used after the
analytic Wishart inputs have been supplied. Selected splits, strict correlated
pairs and independence under block-diagonal scale remain explicit premises of
the final bridge theorem. It is not a proof of `PrincipalTheorem` by itself.
-/

namespace WishartVerification

namespace MomentAssembly

variable {ι : Type*} [DecidableEq ι]

theorem product_singletons_le (m : Finset ι → ℝ)
    (hempty : m ∅ = 1) (hpos : ∀ i, 0 ≤ m {i})
    (hsplit : ∀ J i, i ∈ J → m {i} * m (J.erase i) ≤ m J) (J : Finset ι) :
    (∏ i ∈ J, m {i}) ≤ m J := by
  induction J using Finset.induction_on with
  | empty => simp [hempty]
  | @insert i J hi ih =>
      rw [Finset.prod_insert hi]
      have hs := hsplit (insert i J) i (Finset.mem_insert_self i J)
      rw [Finset.erase_insert hi] at hs
      exact (mul_le_mul_of_nonneg_left ih (hpos i)).trans hs

/-- Splitting off every factor outside a retained subproduct gives this lower
bound. The retained subproduct can contain a correlated active pair. -/
theorem retained_subproduct_le (m : Finset ι → ℝ)
    (hpos : ∀ i, 0 ≤ m {i})
    (hsplit : ∀ J i, i ∈ J → m {i} * m (J.erase i) ≤ m J)
    (A B : Finset ι) (hAB : Disjoint A B) :
    m A * (∏ i ∈ B, m {i}) ≤ m (A ∪ B) := by
  revert hAB
  induction B using Finset.induction_on with
  | empty => intro _; simp
  | @insert i B hi ih =>
      intro hAB
      have hiA : i ∉ A := fun h ↦
        (Finset.disjoint_left.mp hAB) h (Finset.mem_insert_self i B)
      have hAB' : Disjoint A B := hAB.mono_right (Finset.subset_insert i B)
      have hiAB : i ∉ A ∪ B := by simp only [Finset.mem_union, not_or]; exact ⟨hiA, hi⟩
      rw [Finset.prod_insert hi]
      calc
        m A * (m {i} * ∏ j ∈ B, m {j}) = m {i} * (m A * ∏ j ∈ B, m {j}) := by ring
        _ ≤ m {i} * m (A ∪ B) := mul_le_mul_of_nonneg_left (ih hAB') (hpos i)
        _ ≤ m (insert i (A ∪ B)) := by
          simpa only [Finset.erase_insert hiAB] using
            hsplit (insert i (A ∪ B)) i (Finset.mem_insert_self i _)
        _ = m (A ∪ insert i B) := by rw [Finset.union_insert]

/-- A strict inequality for any subproduct remains strict after all remaining
positive marginal moments are multiplied in. -/
theorem strict_subproduct_implies_strict (m : Finset ι → ℝ)
    (hpos : ∀ i, 0 < m {i})
    (hsplit : ∀ J i, i ∈ J → m {i} * m (J.erase i) ≤ m J)
    (A J : Finset ι) (hAJ : A ⊆ J)
    (hstrict : (∏ i ∈ A, m {i}) < m A) :
    (∏ i ∈ J, m {i}) < m J := by
  have hdisjoint : Disjoint A (J \ A) := Finset.disjoint_sdiff
  have hpositive : 0 < ∏ i ∈ J \ A, m {i} := Finset.prod_pos fun i _ ↦ hpos i
  calc
    (∏ i ∈ J, m {i}) = (∏ i ∈ A, m {i}) * ∏ i ∈ J \ A, m {i} := by
      rw [← Finset.prod_union hdisjoint, Finset.union_sdiff_of_subset hAJ]
    _ < m A * ∏ i ∈ J \ A, m {i} := mul_lt_mul_of_pos_right hstrict hpositive
    _ ≤ m J := by
      simpa only [Finset.union_sdiff_of_subset hAJ] using
        retained_subproduct_le m (fun i ↦ (hpos i).le) hsplit A (J \ A) hdisjoint

end MomentAssembly

section PrincipalMoments

variable {p d : ℕ} {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
variable (P : PrincipalPartition p d) (ν : Fin d → ℝ)

def restrictExponents (ν : Fin d → ℝ) (J : Finset (Fin d)) : Fin d → ℝ :=
  fun i ↦ if i ∈ J then ν i else 0

theorem restrictExponents_nonneg (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) (i : Fin d) :
    0 ≤ restrictExponents ν J i := by
  unfold restrictExponents
  split_ifs
  · exact hν i
  · exact le_rfl

theorem principalMomentIntegrand_restrictExponents
    (J K : Finset (Fin d)) (X : SymmetricMatrix p) :
    principalMomentIntegrand P (restrictExponents ν J) K X =
      principalMomentIntegrand P ν (K ∩ J) X := by
  unfold principalMomentIntegrand
  rw [← Finset.filter_mem_eq_inter, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hij : i ∈ J <;> simp [restrictExponents, hij]

theorem principalMoment_restrictExponents (J K : Finset (Fin d)) :
    principalMoment α Sigma P (restrictExponents ν J) K =
      principalMoment α Sigma P ν (K ∩ J) := by
  unfold principalMoment
  apply integral_congr_ae
  exact ae_of_all _ (principalMomentIntegrand_restrictExponents P ν J K)

/-- All selected subproduct splits follow from the full selected-split theorem
at the same dimension and scale by setting the omitted exponents to zero. -/
theorem principal_subproduct_splits_of_full_splits
    (hν : ∀ i, 0 ≤ ν i)
    (hfull : ∀ η : Fin d → ℝ, (∀ i, 0 ≤ η i) → ∀ j : Fin d,
      principalMoment α Sigma P η {j} *
          principalMoment α Sigma P η (Finset.univ.erase j) ≤
        principalMoment α Sigma P η Finset.univ)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
      principalMoment α Sigma P ν J := by
  have h := hfull (restrictExponents ν J) (restrictExponents_nonneg ν hν J) j
  have hsingle : ({j} : Finset (Fin d)) ∩ J = {j} :=
    Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hj)
  have hrest : (Finset.univ.erase j : Finset (Fin d)) ∩ J = J.erase j := by
    rw [Finset.erase_inter, Finset.univ_inter]
  simpa only [principalMoment_restrictExponents, hsingle, hrest, Finset.univ_inter] using h

theorem principalMoment_empty (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) :
    principalMoment α Sigma P ν ∅ = 1 := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  simp [principalMoment, principalMomentIntegrand]

theorem principalMoment_pos (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) :
    0 < principalMoment α Sigma P ν J := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact integral_pos_of_pos_ae (integrable_principalMomentIntegrand hSigma hα P ν hν J)
    (ae_principalMomentIntegrand_pos α Sigma P ν J)

theorem principalMoment_singleton_of_exponent_zero
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (i : Fin d) (hi : ν i = 0) : principalMoment α Sigma P ν {i} = 1 := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  simp [principalMoment, principalMomentIntegrand, hi]

/-- Zero exponents really disappear from each product, including off the
positive-definite support, because the usual real zeroth power equals one. -/
theorem principalMomentIntegrand_active_filter (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (X : SymmetricMatrix p) :
    principalMomentIntegrand P ν J X =
      principalMomentIntegrand P ν (J.filter fun i ↦ 0 < ν i) X := by
  unfold principalMomentIntegrand
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hνi : ν i = 0 := le_antisymm
    (le_of_not_gt fun h ↦ hnot (Finset.mem_filter.mpr ⟨hi, h⟩)) (hν i)
  simp [hνi]

theorem principalMoment_active_filter (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) :
    principalMoment α Sigma P ν J =
      principalMoment α Sigma P ν (J.filter fun i ↦ 0 < ν i) := by
  unfold principalMoment
  apply integral_congr_ae
  exact ae_of_all _ (principalMomentIntegrand_active_filter P ν hν J)

theorem principalMoment_factorizes_of_independent
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (hν : ∀ i, 0 ≤ ν i)
    (hind : iIndepFun (fun i X ↦ (principalMinor (P.block i) X) ^ ν i)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) :
    principalMoment α Sigma P ν Finset.univ =
      ∏ i : Fin d, principalMoment α Sigma P ν {i} := by
  have hmeas (i : Fin d) : AEStronglyMeasurable
      (fun X ↦ (principalMinor (P.block i) X) ^ ν i)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by
    have h := (integrable_principalMomentIntegrand hSigma hα P ν hν {i}).aestronglyMeasurable
    have heq : principalMomentIntegrand P ν {i} =
        (fun X ↦ (principalMinor (P.block i) X) ^ ν i) := by
      funext X
      exact Finset.prod_singleton _ _
    rw [heq] at h
    exact h
  simpa only [principalMoment, principalMomentIntegrand, Finset.prod_singleton] using
    hind.integral_fun_prod_eq_prod_integral hmeas

/-- The complete finite assembly for one fixed set of admissible Wishart
parameters. The three inputs are explicitly exposed: selected subproduct
splits, strict comparison of a correlated active pair, and exact moment
factorization under active block-diagonal scale. They must be proved before
this can establish Theorem 1.1. -/
theorem principal_result_of_split_pair_factorization
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (hν : ∀ i, 0 ≤ ν i)
    (hsplit : ∀ J : Finset (Fin d), ∀ j ∈ J,
      principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
        principalMoment α Sigma P ν J)
    (hpair : ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j →
      Sigma.submatrix (fun a : P.block i ↦ (a : Fin p))
        (fun b : P.block j ↦ (b : Fin p)) ≠ 0 →
      principalMoment α Sigma P ν {i} * principalMoment α Sigma P ν {j} <
        principalMoment α Sigma P ν {i, j})
    (hfactor : independentActiveScaleBlocks Sigma P ν →
      principalMoment α Sigma P ν Finset.univ =
        ∏ i : Fin d, principalMoment α Sigma P ν {i}) :
    (∀ J : Finset (Fin d), Integrable (principalMomentIntegrand P ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧
    (∀ j : Fin d,
      principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j) ≤
        principalMoment α Sigma P ν Finset.univ ∧
      (∏ i : Fin d, principalMoment α Sigma P ν {i}) ≤
        principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j)) ∧
    ((principalMoment α Sigma P ν Finset.univ =
        ∏ i : Fin d, principalMoment α Sigma P ν {i}) ↔
      independentActiveScaleBlocks Sigma P ν) := by
  let m := principalMoment α Sigma P ν
  have hpos (i : Fin d) : 0 < m {i} := principalMoment_pos P ν hSigma hα hν {i}
  have hprod (J : Finset (Fin d)) : (∏ i ∈ J, m {i}) ≤ m J :=
    MomentAssembly.product_singletons_le m (principalMoment_empty P ν hSigma hα)
      (fun i ↦ (hpos i).le) hsplit J
  refine ⟨fun J ↦ integrable_principalMomentIntegrand hSigma hα P ν hν J, ?_, ?_⟩
  · intro j
    refine ⟨hsplit _ j (Finset.mem_univ j), ?_⟩
    change (∏ i : Fin d, m {i}) ≤ m {j} * m (Finset.univ.erase j)
    rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ m {i}) (Finset.mem_univ j)]
    exact mul_le_mul_of_nonneg_left (hprod _) (hpos j).le
  · constructor
    · intro heq i j hij hi hj a ha b hb
      by_contra hab
      have hblock : Sigma.submatrix (fun a : P.block i ↦ (a : Fin p))
          (fun b : P.block j ↦ (b : Fin p)) ≠ 0 := by
        intro hz
        exact hab (congrArg
          (fun M : Matrix (P.block i) (P.block j) ℝ ↦ M ⟨a, ha⟩ ⟨b, hb⟩) hz)
      have hpair' : (∏ k ∈ ({i, j} : Finset (Fin d)), m {k}) < m {i, j} := by
        simpa only [Finset.prod_pair hij] using hpair i j hij hi hj hblock
      have hstrict := MomentAssembly.strict_subproduct_implies_strict m hpos hsplit
        {i, j} Finset.univ (Finset.subset_univ _) hpair'
      exact hstrict.ne' heq
    · intro h
      exact hfactor h

/-- The equivalent assembly interface when the supplied probabilistic input
is full joint independence of the actual determinant factors. -/
theorem principal_result_of_split_pair_independence
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (hν : ∀ i, 0 ≤ ν i)
    (hsplit : ∀ J : Finset (Fin d), ∀ j ∈ J,
      principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) ≤
        principalMoment α Sigma P ν J)
    (hpair : ∀ i j : Fin d, i ≠ j → 0 < ν i → 0 < ν j →
      Sigma.submatrix (fun a : P.block i ↦ (a : Fin p))
        (fun b : P.block j ↦ (b : Fin p)) ≠ 0 →
      principalMoment α Sigma P ν {i} * principalMoment α Sigma P ν {j} <
        principalMoment α Sigma P ν {i, j})
    (hind : independentActiveScaleBlocks Sigma P ν →
      iIndepFun (fun i X ↦ (principalMinor (P.block i) X) ^ ν i)
        (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) :
    (∀ J : Finset (Fin d), Integrable (principalMomentIntegrand P ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧
    (∀ j : Fin d,
      principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j) ≤
        principalMoment α Sigma P ν Finset.univ ∧
      (∏ i : Fin d, principalMoment α Sigma P ν {i}) ≤
        principalMoment α Sigma P ν {j} *
          principalMoment α Sigma P ν (Finset.univ.erase j)) ∧
    ((principalMoment α Sigma P ν Finset.univ =
        ∏ i : Fin d, principalMoment α Sigma P ν {i}) ↔
      independentActiveScaleBlocks Sigma P ν) :=
  principal_result_of_split_pair_factorization P ν hSigma hα hν hsplit hpair
    (fun h ↦ principalMoment_factorizes_of_independent P ν hSigma hα hν (hind h))

end PrincipalMoments

end WishartVerification
end CanonicalSource97

section CanonicalSource98
/- Source: Wishart/DisjointBlockIndependence.lean -/



/-!
# Independence for arbitrary disjoint principal index sets

The two selected blocks need not cover the ambient matrix, nor occur in any
particular order. Marginalization to their union transports the block-diagonal
product law to any two injective, disjoint coordinate selections.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def joinPrincipalSelections {p q m : ℕ} (f : Fin q → Fin p) (g : Fin m → Fin p) :
    Fin (q + m) → Fin p := Sum.elim f g ∘ finSumFinEquiv.symm

@[simp] theorem joinPrincipalSelections_castAdd {p q m : ℕ}
    (f : Fin q → Fin p) (g : Fin m → Fin p) (i : Fin q) :
    joinPrincipalSelections f g (Fin.castAdd m i) = f i := by
  simp [joinPrincipalSelections]

@[simp] theorem joinPrincipalSelections_natAdd {p q m : ℕ}
    (f : Fin q → Fin p) (g : Fin m → Fin p) (j : Fin m) :
    joinPrincipalSelections f g (Fin.natAdd q j) = g j := by
  simp [joinPrincipalSelections]

theorem joinPrincipalSelections_injective {p q m : ℕ}
    {f : Fin q → Fin p} {g : Fin m → Fin p}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisjoint : ∀ i j, f i ≠ g j) :
    Function.Injective (joinPrincipalSelections f g) := by
  apply Function.Injective.comp _ finSumFinEquiv.symm.injective
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (hf hij)
  · exact (hdisjoint i j hij).elim
  · exact (hdisjoint j i hij.symm).elim
  · exact congrArg Sum.inr (hg hij)

theorem principalSymmetricBlock_join {p q m : ℕ}
    (f : Fin q → Fin p) (g : Fin m → Fin p) (X : SymmetricMatrix p) :
    (principalSymmetricBlock (Fin.castAdd m)
        (principalSymmetricBlock (joinPrincipalSelections f g) X),
      principalSymmetricBlock (Fin.natAdd q)
        (principalSymmetricBlock (joinPrincipalSelections f g) X)) =
      (principalSymmetricBlock f X, principalSymmetricBlock g X) := by
  apply Prod.ext <;> apply Subtype.ext <;> ext i j <;>
    simp [principalSymmetricBlock, Matrix.submatrix_apply]

theorem submatrix_joinPrincipalSelections_eq_blockDiagonal
    {p q m : ℕ} (f : Fin q → Fin p) (g : Fin m → Fin p)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.IsHermitian)
    (hcross : ∀ i j, S (f i) (g j) = 0) :
    S.submatrix (joinPrincipalSelections f g) (joinPrincipalSelections f g) =
      blockDiagonalMatrix (S.submatrix f f) (S.submatrix g g) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin q ⊕ Fin m ≃ Fin (q + m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin q ⊕ Fin m ≃ Fin (q + m)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [joinPrincipalSelections, blockDiagonalMatrix, Matrix.submatrix_apply]
  · simp [joinPrincipalSelections, blockDiagonalMatrix, Matrix.submatrix_apply, hcross]
  · have hreverse : S (g i) (f j) = 0 := by
      have hs : S (f j) (g i) = S (g i) (f j) := by
        simpa only [star_trivial] using hS.apply (g i) (f j)
      rw [← hs, hcross]
    simpa [joinPrincipalSelections, blockDiagonalMatrix, Matrix.submatrix_apply] using hreverse
  · simp [joinPrincipalSelections, blockDiagonalMatrix, Matrix.submatrix_apply]

/-- Arbitrary disjoint principal blocks of a real-shape Wishart matrix are
independent whenever their cross scale block vanishes. Coordinates outside
the two selections may have arbitrary correlations. -/
theorem map_disjointPrincipalBlocks_nonsingularWishartMeasure
    {n : ℝ} {p q m : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {f : Fin q → Fin p} {g : Fin m → Fin p}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisjoint : ∀ i j, f i ≠ g j)
    (hcross : ∀ i j, S (f i) (g j) = 0) :
    (nonsingularWishartMeasure n S).map
      (fun X => (principalSymmetricBlock f X, principalSymmetricBlock g X)) =
      (nonsingularWishartMeasure n (S.submatrix f f)).prod
        (nonsingularWishartMeasure n (S.submatrix g g)) := by
  have hu := joinPrincipalSelections_injective hf hg hdisjoint
  have hdim : q + m ≤ p := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hu
  have hdegree : (((q + m : ℕ) : ℝ) - 1) < n :=
    (sub_le_sub_right (Nat.cast_le.mpr hdim) 1).trans_lt hn
  have hscale := submatrix_joinPrincipalSelections_eq_blockDiagonal f g
    hS.isHermitian hcross
  have hmarginal := map_principalSymmetricBlock_nonsingularWishartMeasure
    (joinPrincipalSelections f g) hu hS hn
  have hblocks := map_diagonalBlocks_blockDiagonalScale hdegree
    (hS.submatrix hf) (hS.submatrix hg)
  rw [← hscale, ← hmarginal,
    Measure.map_map (by fun_prop) (measurable_principalSymmetricBlock _)] at hblocks
  have hfun :
      (fun X : SymmetricMatrix (q + m) =>
        (principalSymmetricBlock (Fin.castAdd m) X,
          principalSymmetricBlock (Fin.natAdd q) X)) ∘
        principalSymmetricBlock (joinPrincipalSelections f g) =
      fun X => (principalSymmetricBlock f X, principalSymmetricBlock g X) :=
    funext (principalSymmetricBlock_join f g)
  rw [hfun] at hblocks
  exact hblocks

/-- The product law gives exact factorization for any two measurable
observables of the disjoint selected blocks. -/
theorem integral_mul_disjointPrincipalBlocks
    {n : ℝ} {p q m : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hn : (p : ℝ) - 1 < n)
    {f : Fin q → Fin p} {g : Fin m → Fin p}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisjoint : ∀ i j, f i ≠ g j)
    (hcross : ∀ i j, S (f i) (g j) = 0)
    {F : SymmetricMatrix q → ℝ} {G : SymmetricMatrix m → ℝ}
    (hF : Measurable F) (hG : Measurable G) :
    (∫ X, F (principalSymmetricBlock f X) * G (principalSymmetricBlock g X)
      ∂nonsingularWishartMeasure n S) =
      (∫ U, F U ∂nonsingularWishartMeasure n (S.submatrix f f)) *
        ∫ V, G V ∂nonsingularWishartMeasure n (S.submatrix g g) := by
  have hq : q ≤ p := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hf
  have hm : m ≤ p := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hg
  have hnq : (q : ℝ) - 1 < n :=
    (sub_le_sub_right (Nat.cast_le.mpr hq) 1).trans_lt hn
  have hnm : (m : ℝ) - 1 < n :=
    (sub_le_sub_right (Nat.cast_le.mpr hm) 1).trans_lt hn
  letI := isProbabilityMeasure_nonsingularWishartMeasure (hS.submatrix hf) hnq
  letI := isProbabilityMeasure_nonsingularWishartMeasure (hS.submatrix hg) hnm
  have hmap := map_disjointPrincipalBlocks_nonsingularWishartMeasure
    hS hn hf hg hdisjoint hcross
  have hi := integral_map
    (φ := fun X : SymmetricMatrix p =>
      (principalSymmetricBlock f X, principalSymmetricBlock g X))
    (f := fun x : SymmetricMatrix q × SymmetricMatrix m => F x.1 * G x.2)
    (μ := nonsingularWishartMeasure n S) (by fun_prop) (by fun_prop)
  rw [hmap, integral_prod_mul] at hi
  exact hi.symm

end Wishart
end
end CanonicalSource98

section CanonicalSource99
/- Source: Wishart/ActiveBlockFactorization.lean -/



open scoped Classical
open MeasureTheory

/-!
# Actual moment factorization under active block-diagonal scale

The principal matrix on the union of a finite collection of blocks determines
every determinant in that collection. The verified disjoint-block product law
therefore separates one active block from the entire retained product. Finite
induction and exact removal of zero powers prove the equality-sufficiency
direction for the actual density-defined real-shape Wishart measure.

No family-independence assertion or moment factorization is assumed here.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

def principalSetCoordinates (I : Finset (Fin p)) : Fin (Fintype.card I) → Fin p :=
  fun a ↦ ((Fintype.equivFin I).symm a : Fin p)

theorem principalSetCoordinates_injective (I : Finset (Fin p)) :
    Function.Injective (principalSetCoordinates I) :=
  Subtype.coe_injective.comp (Fintype.equivFin I).symm.injective

theorem principalSetCoordinates_mem (I : Finset (Fin p)) (a : Fin (Fintype.card I)) :
    principalSetCoordinates I a ∈ I := ((Fintype.equivFin I).symm a).property

def principalSetMatrix (I : Finset (Fin p)) : SymmetricMatrix p → SymmetricMatrix (Fintype.card I) :=
  Wishart.principalSymmetricBlock (principalSetCoordinates I)

theorem principalSetMatrix_measurable (I : Finset (Fin p)) : Measurable (principalSetMatrix I) :=
  Wishart.measurable_principalSymmetricBlock _

theorem principalSetMatrix_det (I : Finset (Fin p)) (X : SymmetricMatrix p) :
    ((principalSetMatrix I X : SymmetricMatrix (Fintype.card I)) :
      Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ).det = principalMinor I X :=
  (principalMinor_eq_det_enumeration I X (Fintype.equivFin I).symm).symm

def relativePrincipalCoordinates (I J : Finset (Fin p)) (hJI : J ⊆ I) :
    J → Fin (Fintype.card I) :=
  fun a ↦ Fintype.equivFin I ⟨(a : Fin p), hJI a.property⟩

@[simp] theorem principalSetCoordinates_relative
    (I J : Finset (Fin p)) (hJI : J ⊆ I) (a : J) :
    principalSetCoordinates I (relativePrincipalCoordinates I J hJI a) = (a : Fin p) := by
  simp only [principalSetCoordinates, relativePrincipalCoordinates, Equiv.symm_apply_apply]

def relativePrincipalMinor (I J : Finset (Fin p)) (hJI : J ⊆ I)
    (Y : SymmetricMatrix (Fintype.card I)) : ℝ :=
  ((Y : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ).submatrix
    (relativePrincipalCoordinates I J hJI) (relativePrincipalCoordinates I J hJI)).det

theorem relativePrincipalMinor_measurable (I J : Finset (Fin p)) (hJI : J ⊆ I) :
    Measurable (relativePrincipalMinor I J hJI) :=
  ((continuous_subtype_val.matrix_submatrix _ _).matrix_det).measurable

@[simp] theorem relativePrincipalMinor_principalSetMatrix
    (I J : Finset (Fin p)) (hJI : J ⊆ I) (X : SymmetricMatrix p) :
    relativePrincipalMinor I J hJI (principalSetMatrix I X) = principalMinor J X := by
  unfold relativePrincipalMinor principalSetMatrix Wishart.principalSymmetricBlock principalMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, principalSetCoordinates_relative]

/-- The reduced matrix on the union of the indicated blocks determines the
entire product. The subtype product exposes each membership proof explicitly. -/
def retainedBlockProduct (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d))
    (Y : SymmetricMatrix (Fintype.card (J.biUnion P.block))) : ℝ :=
  ∏ i : J, (relativePrincipalMinor (J.biUnion P.block) (P.block i)
    (Finset.subset_biUnion_of_mem P.block i.property) Y) ^ ν i

theorem retainedBlockProduct_measurable (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) : Measurable (retainedBlockProduct P ν J) := by
  unfold retainedBlockProduct
  exact Finset.measurable_prod _ fun i _ ↦
    (relativePrincipalMinor_measurable _ _ _).pow_const _

@[simp] theorem retainedBlockProduct_principalSetMatrix
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (X : SymmetricMatrix p) :
    retainedBlockProduct P ν J (principalSetMatrix (J.biUnion P.block) X) =
      principalMomentIntegrand P ν J X := by
  simp only [retainedBlockProduct, relativePrincipalMinor_principalSetMatrix,
    principalMomentIntegrand]
  exact Finset.prod_coe_sort J (fun i => principalMinor (P.block i) X ^ ν i)

theorem integral_principalSetMatrix
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (I : Finset (Fin p)) (F : SymmetricMatrix (Fintype.card I) → ℝ)
    (hFm : Measurable F) :
    (∫ Y, F Y ∂TauCeti.Probability.nonsingularWishartMeasure α
      (Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I))) =
      ∫ X, F (principalSetMatrix I X) ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma := by
  rw [← Wishart.map_principalSymmetricBlock_nonsingularWishartMeasure
    (principalSetCoordinates I) (principalSetCoordinates_injective I) hSigma hα]
  exact integral_map_of_stronglyMeasurable (principalSetMatrix_measurable I) hFm.stronglyMeasurable

theorem integral_mul_principalSetMatrices
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (I J : Finset (Fin p)) (hIJ : Disjoint I J)
    (hcross : ∀ a ∈ I, ∀ b ∈ J, Sigma a b = 0)
    (F : SymmetricMatrix (Fintype.card I) → ℝ)
    (G : SymmetricMatrix (Fintype.card J) → ℝ)
    (hFm : Measurable F) (hGm : Measurable G) :
    (∫ X, F (principalSetMatrix I X) * G (principalSetMatrix J X)
      ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) =
      (∫ X, F (principalSetMatrix I X) ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma) *
        ∫ X, G (principalSetMatrix J X) ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma := by
  have hd : ∀ a b, principalSetCoordinates I a ≠ principalSetCoordinates J b := by
    intro a b hab
    exact Finset.disjoint_left.mp hIJ (principalSetCoordinates_mem I a)
      (hab.symm ▸ principalSetCoordinates_mem J b)
  have hz : ∀ a b, Sigma (principalSetCoordinates I a) (principalSetCoordinates J b) = 0 :=
    fun a b ↦ hcross _ (principalSetCoordinates_mem I a) _ (principalSetCoordinates_mem J b)
  have h := Wishart.integral_mul_disjointPrincipalBlocks hSigma hα
    (principalSetCoordinates_injective I) (principalSetCoordinates_injective J) hd hz hFm hGm
  rw [integral_principalSetMatrix hSigma hα I F hFm,
    integral_principalSetMatrix hSigma hα J G hGm] at h
  exact h

theorem PrincipalPartition.disjoint_block_biUnion (P : PrincipalPartition p d)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∉ J) :
    Disjoint (P.block j) (J.biUnion P.block) := by
  apply Finset.disjoint_left.mpr
  intro a haj haJ
  obtain ⟨i, hiJ, hai⟩ := Finset.mem_biUnion.mp haJ
  have hji : j ≠ i := fun h ↦ hj (h.symm ▸ hiJ)
  exact Finset.disjoint_left.mp (P.disjoint hji) haj hai

/-- The actual two-block product law separates one active determinant from the
entire retained active product. -/
theorem principalMoment_split_eq_of_activeScaleBlocks
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (hscale : independentActiveScaleBlocks Sigma P ν)
    (J : Finset (Fin d)) (hactive : ∀ i ∈ J, 0 < ν i)
    (j : Fin d) (hj : j ∈ J) :
    principalMoment α Sigma P ν J =
      principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (J.erase j) := by
  let I := P.block j
  let B := (J.erase j).biUnion P.block
  let F : SymmetricMatrix (Fintype.card I) → ℝ :=
    fun Y ↦ ((Y : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℝ).det) ^ ν j
  let G := retainedBlockProduct P ν (J.erase j)
  have hFm : Measurable F := continuous_subtype_val.matrix_det.measurable.pow_const _
  have hGm : Measurable G := retainedBlockProduct_measurable P ν (J.erase j)
  have hIB : Disjoint I B := P.disjoint_block_biUnion (J.erase j) j (Finset.notMem_erase j J)
  have hcross : ∀ a ∈ I, ∀ b ∈ B, Sigma a b = 0 := by
    intro a hai b hbB
    obtain ⟨i, hi, hbi⟩ := Finset.mem_biUnion.mp hbB
    have hij : j ≠ i := Ne.symm (Finset.mem_erase.mp hi).1
    exact hscale j i hij (hactive j hj) (hactive i (Finset.mem_of_mem_erase hi)) a hai b hbi
  have h := integral_mul_principalSetMatrices hSigma hα I B hIB hcross F G hFm hGm
  have hF (X : SymmetricMatrix p) : F (principalSetMatrix I X) =
      (principalMinor (P.block j) X) ^ ν j := by
    dsimp [F, I]
    rw [principalSetMatrix_det]
  have hG (X : SymmetricMatrix p) : G (principalSetMatrix B X) =
      principalMomentIntegrand P ν (J.erase j) X :=
    retainedBlockProduct_principalSetMatrix P ν (J.erase j) X
  simp_rw [hF, hG] at h
  have hprod (X : SymmetricMatrix p) :
      (principalMinor (P.block j) X) ^ ν j * principalMomentIntegrand P ν (J.erase j) X =
        principalMomentIntegrand P ν J X := by
    exact Finset.mul_prod_erase J (fun i ↦ (principalMinor (P.block i) X) ^ ν i) hj
  simp_rw [hprod] at h
  simpa only [principalMoment, principalMomentIntegrand, Finset.prod_singleton] using h

theorem principalMoment_active_factorization
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (hscale : independentActiveScaleBlocks Sigma P ν)
    (J : Finset (Fin d)) (hactive : ∀ i ∈ J, 0 < ν i) :
    principalMoment α Sigma P ν J = ∏ i ∈ J, principalMoment α Sigma P ν {i} := by
  revert hactive
  induction J using Finset.induction_on with
  | empty =>
      intro _
      rw [principalMoment_empty P ν hSigma hα, Finset.prod_empty]
  | @insert j J hj ih =>
      intro hactive
      rw [principalMoment_split_eq_of_activeScaleBlocks P ν hSigma hα hscale
        (insert j J) hactive j (Finset.mem_insert_self j J), Finset.erase_insert hj,
        ih (fun i hi ↦ hactive i (Finset.mem_insert_of_mem hi)), Finset.prod_insert hj]

/-- Equality sufficiency for the actual Wishart moments, including arbitrary
zero powers and correlations involving inactive blocks. -/
theorem principalMoment_factorizes_of_activeScaleBlocks
    {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (hν : ∀ i, 0 ≤ ν i)
    (hscale : independentActiveScaleBlocks Sigma P ν) :
    principalMoment α Sigma P ν Finset.univ =
      ∏ i : Fin d, principalMoment α Sigma P ν {i} := by
  rw [principalMoment_active_filter P ν hν Finset.univ]
  rw [principalMoment_active_factorization P ν hSigma hα hscale _
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)]
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hzero : ν i = 0 := le_antisymm
    (le_of_not_gt fun h ↦ hnot (Finset.mem_filter.mpr ⟨hi, h⟩)) (hν i)
  exact principalMoment_singleton_of_exponent_zero P ν hSigma hα i hzero

end

end WishartVerification
end CanonicalSource99
