module
public import PaperVerification.ThetaEquality
public import PaperVerification.DnMoments
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter Topology
open PaperVerification.Hyperbolic
open scoped BigOperators

def halfCoordinateMap : C(HalfInterval, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

theorem integral_foldedEmpirical {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (f : C(HalfInterval, ℝ)) :
    (∫ t, f t ∂(foldedEmpirical hn x)) =
      (∑ i, f (foldedCoordinateMap x i)) / (n : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold foldedEmpirical
  change (∫ t, f t ∂Measure.map (foldedCoordinateMap x) (uniformProbability (Fin n))) = _
  rw [integral_map_of_stronglyMeasurable (foldedCoordinateMap x).continuous.measurable
    f.continuous.stronglyMeasurable, integral_uniformProbability]
  simp only [Fintype.card_fin]

lemma empirical_eq_dirac_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t₀ : HalfInterval) :
    foldedEmpirical hn x = diracProbability t₀ ↔
      ∀ i, foldedCoordinateMap x i = t₀ := by
  constructor
  · intro h
    have hae : ∀ᵐ t ∂(foldedEmpirical hn x : Measure HalfInterval), t = t₀ := by
      rw [h, coe_diracProbability, ae_dirac_eq]
      simp
    exact (ae_foldedEmpirical_iff hn x _ (measurableSet_singleton t₀)).mp hae
  · intro h
    apply probability_interval_eq_dirac_of_ae
    exact (ae_foldedEmpirical_iff hn x _ (measurableSet_singleton t₀)).mpr h

lemma theta_endpoints_measure_of_mean (μ : ProbabilityMeasure HalfInterval)
    (hae : ∀ᵐ t ∂(μ : Measure HalfInterval), t = thetaZeroPoint ∨ t = thetaHalfPoint)
    (hmean : (∫ t, halfCoordinateMap t ∂μ) = 1 / 4) :
    μ = mixProbability (diracProbability thetaZeroPoint) (diracProbability thetaHalfPoint)
      (1 / 2) ⟨by norm_num, by norm_num⟩ := by
  have hs : (μ : Measure HalfInterval).support ⊆ {thetaZeroPoint,thetaHalfPoint} :=
    Measure.support_subset_of_isClosed
      (Set.Finite.insert thetaZeroPoint (Set.finite_singleton thetaHalfPoint)).isClosed
      (by filter_upwards [hae] with t ht; simpa only [mem_insert_iff, mem_singleton_iff] using ht)
  obtain ⟨a, ha, hμ⟩ := probability_eq_pair_mixture μ thetaZeroPoint thetaHalfPoint hs
  rw [hμ, integral_mixProbability] at hmean
  simp only [coe_diracProbability, integral_dirac, halfCoordinateMap, ContinuousMap.coe_mk,
    thetaZeroPoint, thetaHalfPoint] at hmean
  have haeq : a = 1 / 2 := by linarith
  subst a
  exact hμ

theorem empirical_balanced_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    foldedEmpirical hn x =
      mixProbability (diracProbability thetaZeroPoint) (diracProbability thetaHalfPoint)
        (1 / 2) ⟨by norm_num, by norm_num⟩ ↔ BalancedHalfGrid x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hμ
    have hae : ∀ᵐ t ∂(foldedEmpirical hn x : Measure HalfInterval),
        t = thetaZeroPoint ∨ t = thetaHalfPoint := by
      rw [hμ]
      erw [coe_mixProbability]
      rw [ae_add_measure_iff]
      constructor <;> apply Measure.ae_smul_measure <;>
        simp only [coe_diracProbability, ae_dirac_eq, Filter.eventually_pure, true_or, or_true]
    have hall := (ae_foldedEmpirical_iff hn x _
      ((measurableSet_singleton thetaZeroPoint).union (measurableSet_singleton thetaHalfPoint))).mp hae
    refine ⟨fun i ↦ (hall i).imp (congrArg Subtype.val) (congrArg Subtype.val), ?_⟩
    have hmean : (∫ t, halfCoordinateMap t ∂(foldedEmpirical hn x)) = 1 / 4 := by
      rw [hμ]
      erw [integral_mixProbability]
      norm_num [coe_diracProbability, halfCoordinateMap, thetaZeroPoint, thetaHalfPoint]
    rw [integral_foldedEmpirical] at hmean
    change (∑ i, foldedRadius x i) / (n : ℝ) = 1 / 4 at hmean
    exact (div_eq_iff hnR.ne').mp hmean |>.trans (by ring)
  · intro hx
    apply theta_endpoints_measure_of_mean
    · apply (ae_foldedEmpirical_iff hn x _
        ((measurableSet_singleton thetaZeroPoint).union (measurableSet_singleton thetaHalfPoint))).mpr
      intro i
      exact (hx.1 i).imp Subtype.ext Subtype.ext
    · rw [integral_foldedEmpirical]
      change (∑ i, foldedRadius x i) / (n : ℝ) = 1 / 4
      rw [hx.2]
      field_simp [hnR.ne']

def FoldedThetaEquality {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, foldedRadius x i = 0) ∨ (∀ i, foldedRadius x i = 1 / 4) ∨
  (∀ i, foldedRadius x i = 1 / 2) ∨ BalancedHalfGrid x

theorem thetaEquality_empirical_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ThetaEquality (foldedEmpirical hn x) ↔ FoldedThetaEquality x := by
  unfold ThetaEquality FoldedThetaEquality
  rw [empirical_eq_dirac_iff, empirical_eq_dirac_iff, empirical_eq_dirac_iff, empirical_balanced_iff]
  have h0 : (∀ i, foldedCoordinateMap x i = thetaZeroPoint) ↔ ∀ i, foldedRadius x i = 0 := by
    constructor <;> intro h i
    · exact congrArg Subtype.val (h i)
    · exact Subtype.ext (h i)
  have hq : (∀ i, foldedCoordinateMap x i = thetaQuarterPoint) ↔ ∀ i, foldedRadius x i = 1 / 4 := by
    constructor <;> intro h i
    · exact congrArg Subtype.val (h i)
    · exact Subtype.ext (h i)
  have hh : (∀ i, foldedCoordinateMap x i = thetaHalfPoint) ↔ ∀ i, foldedRadius x i = 1 / 2 := by
    constructor <;> intro h i
    · exact congrArg Subtype.val (h i)
    · exact Subtype.ext (h i)
  rw [h0, hq, hh]

theorem folded_theta_equality_iff {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    thetaMomentNumerator hα (foldedEmpirical hn x) =
      2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔ FoldedThetaEquality x := by
  rw [theta_geometric_mean_equality_iff hα, thetaEquality_empirical_iff]

end PaperVerification.ColdSpots
