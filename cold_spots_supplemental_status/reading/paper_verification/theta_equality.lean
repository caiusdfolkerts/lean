module
public import PaperVerification.ThetaInequality
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter Topology
open PaperVerification.Hyperbolic

def thetaZeroPoint : HalfInterval := ⟨0, by norm_num⟩
def thetaQuarterPoint : HalfInterval := ⟨1 / 4, by norm_num⟩
def thetaHalfPoint : HalfInterval := ⟨1 / 2, by norm_num⟩

def ThetaEquality (μ : ProbabilityMeasure HalfInterval) : Prop :=
  μ = diracProbability thetaZeroPoint ∨ μ = diracProbability thetaQuarterPoint ∨
  μ = diracProbability thetaHalfPoint ∨
  μ = mixProbability (diracProbability thetaZeroPoint) (diracProbability thetaHalfPoint)
    (1 / 2) ⟨by norm_num, by norm_num⟩

def ThetaThree (t : HalfInterval) : Prop :=
  (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 1 / 2

def thetaParameterMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ thetaP α t, continuous_subtype_val.comp (thetaArcMap hα).continuous⟩

lemma probability_map_dirac {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (f : X → Y) (hf : Measurable f) (x : X) :
    (diracProbability x).map f = diracProbability (f x) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map f (Measure.dirac x) = Measure.dirac (f x)
  exact Measure.map_dirac' hf x

lemma probability_map_mix {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [CompactSpace Y] [OpensMeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (μ ν : ProbabilityMeasure X)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    (mixProbability μ ν t ht).map f = mixProbability (μ.map f) (ν.map f) t ht := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, coe_mixProbability]
  rw [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable]

lemma probability_interval_eq_dirac_of_ae {R : ℝ} (μ : ProbabilityMeasure (Interval R))
    (p : Interval R) (h : ∀ᵐ x ∂(μ : Measure (Interval R)), x = p) : μ = diracProbability p := by
  have hs : (μ : Measure (Interval R)).support ⊆ {p,p} :=
    Measure.support_subset_of_isClosed (Set.Finite.insert p (Set.finite_singleton p)).isClosed
      (by filter_upwards [h] with x hx; simp [hx])
  obtain ⟨t, ht, hμ⟩ := probability_eq_pair_mixture μ p p hs
  rw [hμ, mixProbability_same]

lemma thetaP_injective_on_three {α : ℝ} (hα : 0 < α) {t u : HalfInterval}
    (ht : ThetaThree t) (hu : ThetaThree u)
    (heq : thetaP α t = thetaP α u) : t = u := by
  apply Subtype.ext
  rcases ht with ht | ht | ht <;> rcases hu with hu | hu | hu
  all_goals rw [ht, hu] at heq ⊢
  all_goals simp only [thetaP_zero hα, thetaP_quarter hα, thetaP_half] at heq
  all_goals linarith [thetaR_pos hα]

lemma thetaP_eq_midpoint_on_three {α : ℝ} (hα : 0 < α) {t : HalfInterval}
    (ht : ThetaThree t) (heq : thetaP α t = thetaR α / 2) : t = thetaQuarterPoint := by
  apply thetaP_injective_on_three hα ht (Or.inr (Or.inl rfl))
  change thetaP α t = thetaP α (1 / 4)
  rw [thetaP_quarter hα]
  exact heq

lemma theta_push_parameter_integral {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    (∫ p : Interval (thetaR α), (p : ℝ) ∂(thetaPush hα μ)) =
      ∫ t, thetaParameterMap hα t ∂μ := by
  change (∫ p : Interval (thetaR α), (p : ℝ) ∂Measure.map (thetaArcMap hα) (μ : Measure HalfInterval)) = _
  rw [integral_map_of_stronglyMeasurable (thetaArcMap hα).continuous.measurable
    (continuous_subtype_val : Continuous (fun p : Interval (thetaR α) ↦ (p : ℝ))).stronglyMeasurable]
  rfl

lemma theta_equality_of_dirac_push {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hthree : ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval), ThetaThree t)
    (p : Interval (thetaR α)) (hpush : thetaPush hα μ = diracProbability p) :
    ThetaEquality μ := by
  have haepush : ∀ᵐ q ∂(thetaPush hα μ : Measure (Interval (thetaR α))), q = p := by
    rw [hpush, coe_diracProbability, ae_dirac_eq]
    simp
  have hae : ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval), thetaP α t = (p : ℝ) := by
    have h := ae_of_ae_map (thetaArcMap hα).continuous.measurable.aemeasurable haepush
    filter_upwards [h] with t ht
    exact congrArg Subtype.val ht
  obtain ⟨t₀, ht₀, hp₀⟩ := (hthree.and hae).exists
  have hall : ∀ᵐ t ∂(μ : Measure HalfInterval), t = t₀ := by
    filter_upwards [hthree, hae] with t ht hp
    exact thetaP_injective_on_three hα ht ht₀ (hp.trans hp₀.symm)
  have hμ := probability_interval_eq_dirac_of_ae μ t₀ hall
  rcases ht₀ with ht | ht | ht
  · exact Or.inl (hμ.trans (congrArg diracProbability (Subtype.ext ht)))
  · exact Or.inr (Or.inl (hμ.trans (congrArg diracProbability (Subtype.ext ht))))
  · exact Or.inr (Or.inr (Or.inl (hμ.trans (congrArg diracProbability (Subtype.ext ht)))))

lemma theta_equality_of_balanced_push {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hthree : ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval), ThetaThree t)
    (p : Interval (thetaR α))
    (hpush : thetaPush hα μ = mixProbability (diracProbability p)
      (diracProbability (reflectInterval (thetaR α) p)) (1 / 2) ⟨by norm_num, by norm_num⟩) :
    ThetaEquality μ := by
  have haepush : ∀ᵐ q ∂(thetaPush hα μ : Measure (Interval (thetaR α))),
      q = p ∨ q = reflectInterval (thetaR α) p := by
    erw [hpush, coe_mixProbability, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      simp only [coe_diracProbability, ae_dirac_eq, Filter.eventually_pure,
        true_or, or_true]
  have hae : ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval),
      thetaP α t = (p : ℝ) ∨ thetaP α t = thetaR α - (p : ℝ) := by
    have h := ae_of_ae_map (thetaArcMap hα).continuous.measurable.aemeasurable haepush
    filter_upwards [h] with t ht
    exact ht.imp (congrArg Subtype.val) (congrArg Subtype.val)
  by_cases hp : (p : ℝ) = thetaR α / 2
  · have hall : ∀ᵐ t ∂(μ : Measure HalfInterval), t = thetaQuarterPoint := by
      filter_upwards [hthree, hae] with t ht he
      apply thetaP_eq_midpoint_on_three hα ht
      rcases he with he | he <;> rw [hp] at he <;> linarith
    exact Or.inr (Or.inl (probability_interval_eq_dirac_of_ae μ thetaQuarterPoint hall))
  · have hend : ∀ᵐ t ∂(μ : Measure HalfInterval), t = thetaZeroPoint ∨ t = thetaHalfPoint := by
      filter_upwards [hthree, hae] with t ht he
      rcases ht with ht | ht | ht
      · exact Or.inl (Subtype.ext ht)
      · have hc : thetaP α t = thetaR α / 2 := by rw [ht, thetaP_quarter hα]
        rcases he with he | he <;> exact (hp (by linarith)).elim
      · exact Or.inr (Subtype.ext ht)
    have hs : (μ : Measure HalfInterval).support ⊆ {thetaZeroPoint, thetaHalfPoint} :=
      Measure.support_subset_of_isClosed
        (Set.Finite.insert thetaZeroPoint (Set.finite_singleton thetaHalfPoint)).isClosed
        (by filter_upwards [hend] with t ht; simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht)
    obtain ⟨a, ha, hμ⟩ := probability_eq_pair_mixture μ thetaZeroPoint thetaHalfPoint hs
    have hmean : (∫ t, thetaParameterMap hα t ∂μ) = thetaR α / 2 := by
      rw [← theta_push_parameter_integral hα μ, hpush]
      let c : C(Interval (thetaR α), ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
      change (∫ q, c q ∂((mixProbability (diracProbability p)
        (diracProbability (reflectInterval (thetaR α) p)) (1 / 2)
        ⟨by norm_num, by norm_num⟩ : ProbabilityMeasure (Interval (thetaR α))) :
          Measure (Interval (thetaR α)))) = _
      erw [integral_mixProbability]
      simp only [coe_diracProbability, integral_dirac]
      change (1 - (1 / 2 : ℝ)) * (p : ℝ) +
        (1 / 2) * (thetaR α - (p : ℝ)) = thetaR α / 2
      ring
    erw [hμ, integral_mixProbability] at hmean
    simp only [coe_diracProbability, integral_dirac] at hmean
    change (1 - a) * thetaP α 0 + a * thetaP α (1 / 2) = thetaR α / 2 at hmean
    rw [thetaP_zero hα, thetaP_half, mul_zero, add_zero] at hmean
    have hproduct : (a - 1 / 2) * thetaR α = 0 := by nlinarith [hmean]
    have haeq : a = 1 / 2 := sub_eq_zero.mp
      ((mul_eq_zero.mp hproduct).resolve_right (thetaR_pos hα).ne')
    subst a
    exact Or.inr (Or.inr (Or.inr hμ))

theorem theta_equality_forms_of_conditions {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hthree : ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval), ThetaThree t)
    (hH : HyperbolicEquality (thetaR α) (thetaPush hα μ)) : ThetaEquality μ := by
  rcases hH with ⟨p, hp⟩ | ⟨p, hp⟩
  · exact theta_equality_of_dirac_push hα μ hthree p hp
  · exact theta_equality_of_balanced_push hα μ hthree p hp

theorem theta_equality_conditions_of_forms {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) (hμ : ThetaEquality μ) :
    (∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval), ThetaThree t) ∧
      HyperbolicEquality (thetaR α) (thetaPush hα μ) := by
  have hdirac (t : HalfInterval) (ht : ThetaThree t) :
      (∀ᵐ u ∂(diracProbability t : Measure HalfInterval), ThetaThree u) ∧
      HyperbolicEquality (thetaR α) (thetaPush hα (diracProbability t)) := by
    refine ⟨?_, Or.inl ⟨thetaArcMap hα t, ?_⟩⟩
    · simpa only [coe_diracProbability, ae_dirac_eq, Filter.eventually_pure] using ht
    · exact probability_map_dirac _ (thetaArcMap hα).continuous.measurable t
  rcases hμ with rfl | rfl | rfl | rfl
  · exact hdirac thetaZeroPoint (Or.inl rfl)
  · exact hdirac thetaQuarterPoint (Or.inr (Or.inl rfl))
  · exact hdirac thetaHalfPoint (Or.inr (Or.inr rfl))
  · constructor
    · erw [coe_mixProbability, ae_add_measure_iff]
      constructor
      · exact Measure.ae_smul_measure (hdirac thetaZeroPoint (Or.inl rfl)).1 _
      · exact Measure.ae_smul_measure (hdirac thetaHalfPoint (Or.inr (Or.inr rfl))).1 _
    · apply Or.inr
      refine ⟨thetaArcMap hα thetaZeroPoint, ?_⟩
      unfold thetaPush
      erw [probability_map_mix _ (thetaArcMap hα).continuous.measurable,
        probability_map_dirac _ (thetaArcMap hα).continuous.measurable,
        probability_map_dirac _ (thetaArcMap hα).continuous.measurable]
      have href : reflectInterval (thetaR α) (thetaArcMap hα thetaZeroPoint) =
          thetaArcMap hα thetaHalfPoint := by
        apply Subtype.ext
        change thetaR α - thetaP α 0 = thetaP α (1 / 2)
        rw [thetaP_zero hα, thetaP_half, sub_self]
      rw [href]

/-- Proposition 3.2, with exactly the four probability measures displayed in (7). -/
theorem theta_geometric_mean_equality_iff {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    thetaMomentNumerator hα μ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      ThetaEquality μ := by
  rw [theta_geometric_mean_equality_conditions hα μ]
  exact ⟨fun h ↦ theta_equality_forms_of_conditions hα μ h.1 h.2,
    theta_equality_conditions_of_forms hα μ⟩

/-- The same complete equality classification with the four literal eighth
powers of geometric means printed in Proposition 3.2. -/
theorem theta_geometric_mean_equality_literal_iff {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    geometricMean (thetaAMap hα) μ ^ 8 + geometricMean (thetaCMap hα) μ ^ 8 -
      geometricMean (thetaBMap hα) μ ^ 8 - geometricMean (thetaDMap hα) μ ^ 8 =
        2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔ ThetaEquality μ := by
  have h := theta_geometric_mean_equality_iff hα μ
  unfold thetaMomentNumerator at h
  erw [geometricMoment_nat 8 (thetaAMap hα) μ,
    geometricMoment_nat 8 (thetaCMap hα) μ,
    geometricMoment_nat 8 (thetaBMap hα) μ,
    geometricMoment_nat 8 (thetaDMap hα) μ] at h
  exact h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.theta_geometric_mean_equality_literal_iff
