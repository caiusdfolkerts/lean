module
public import PaperVerification.DnGaussian
public import PaperVerification.DimensionLift
public import PaperVerification.ThetaGeometricTransfer
public import PaperVerification.FiniteGeometricMean
public import PaperVerification.LatticeGeometry
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Topology.Order
@[expose] public section
/-!
# Empirical measures and the unrestricted dimension argument

The results in this file connect the genuine lattice Gaussian to the measure
inequality, without changing the dimension or replacing the lattice by a finite
sample. A hypothesis named `hbase` is explicitly the separately proved theta
measure inequality. The final principal theorem must instantiate it.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter Topology
open PaperVerification.Hyperbolic
open scoped BigOperators

def foldedCoordinateMap {n : ℕ} (x : Fin n → ℝ) : C(Fin n, HalfInterval) :=
  ⟨fun i ↦ ⟨foldedRadius x i, foldedRadius_nonneg x i, foldedRadius_le_half x i⟩,
    continuous_of_discreteTopology⟩

def foldedEmpirical {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ProbabilityMeasure HalfInterval := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (uniformProbability (Fin n)).map (foldedCoordinateMap x)

theorem geometricMoment_foldedEmpirical {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (k : ℝ) (hk : 0 < k) (f : C(HalfInterval, ℝ)) (hf : ∀ t, 0 ≤ f t) :
    geometricMoment k f (foldedEmpirical hn x) =
      (∏ i, f (foldedCoordinateMap x i)) ^ (k / (n : ℝ)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold foldedEmpirical
  rw [geometricMoment_map, geometricMoment_uniformProbability (Fin n) k hk _
    (fun i ↦ hf (foldedCoordinateMap x i))]
  simp only [Fintype.card_fin, ContinuousMap.comp_apply]

theorem ae_foldedEmpirical_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (p : HalfInterval → Prop) (hp : MeasurableSet {t | p t}) :
    (∀ᵐ t ∂(foldedEmpirical hn x : Measure HalfInterval), p t) ↔
      ∀ i, p (foldedCoordinateMap x i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold foldedEmpirical
  rw [ProbabilityMeasure.toMeasure_map,
    ae_map_iff (foldedCoordinateMap x).continuous.measurable.aemeasurable hp,
    ae_uniformProbability_iff]

def foldedAProduct {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussian α (foldedRadius x i)

def foldedBProduct {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, alternatingGaussian α (foldedRadius x i)

def foldedCProduct {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, gaussian α (foldedRadius x i - 1 / 2)

def foldedDProduct {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, alternatingGaussian α (foldedRadius x i - 1 / 2)

lemma foldedAProduct_pos {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    0 < foldedAProduct α x := Finset.prod_pos (fun i _ ↦ gaussian_pos hα _)

lemma foldedBProduct_nonneg {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    0 ≤ foldedBProduct α x := Finset.prod_nonneg
  (fun i _ ↦ alternatingGaussian_nonneg hα (foldedRadius_nonneg x i) (foldedRadius_le_half x i))

lemma foldedCProduct_pos {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    0 < foldedCProduct α x := Finset.prod_pos (fun i _ ↦ gaussian_pos hα _)

lemma foldedDProduct_nonneg {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    0 ≤ foldedDProduct α x := Finset.prod_nonneg
  (fun i _ ↦ thetaDMap_nonneg hα (foldedCoordinateMap x i))

lemma prod_lt_prod_of_nonnegative {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 < g i)
    (hfg : ∀ i, f i < g i) : (∏ i, f i) < ∏ i, g i := by
  classical
  by_cases hz : (∏ i, f i) = 0
  · rw [hz]
    exact Finset.prod_pos (fun i _ ↦ hg i)
  · exact Finset.prod_lt_prod_of_nonempty₀
      (fun i hi ↦ lt_of_le_of_ne (hf i) (Ne.symm ((Finset.prod_ne_zero_iff.mp hz) i hi)))
      (fun i _ ↦ hfg i) Finset.univ_nonempty

lemma foldedBProduct_lt_A {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : foldedBProduct α x < foldedAProduct α x := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply prod_lt_prod_of_nonnegative
  · intro i
    exact alternatingGaussian_nonneg hα (foldedRadius_nonneg x i) (foldedRadius_le_half x i)
  · intro i
    exact gaussian_pos hα _
  · intro i
    exact (le_abs_self _).trans_lt (abs_alternatingGaussian_lt hα _)

lemma foldedDProduct_lt_C {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : foldedDProduct α x < foldedCProduct α x := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply prod_lt_prod_of_nonnegative
  · intro i
    exact thetaDMap_nonneg hα (foldedCoordinateMap x i)
  · intro i
    exact gaussian_pos hα _
  · intro i
    exact (le_abs_self _).trans_lt (abs_alternatingGaussian_lt hα _)

theorem dPlusGaussian_folded_lower {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    (1 / 2) * (foldedAProduct α x + foldedCProduct α x -
      foldedBProduct α x - foldedDProduct α x) ≤ dPlusGaussian α x := by
  have hA : (∏ i, gaussian α (x i)) = foldedAProduct α x := by
    unfold foldedAProduct
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_fold α (x i)
  have hC : (∏ i, gaussian α (x i - 1 / 2)) = foldedCProduct α x := by
    unfold foldedCProduct
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_halfshift_fold α (x i)
  have hB : |∏ i, alternatingGaussian α (x i)| = foldedBProduct α x := by
    rw [Finset.abs_prod]
    unfold foldedBProduct
    apply Finset.prod_congr rfl
    intro i _
    exact alternatingGaussian_fold hα (x i)
  have hD : |∏ i, alternatingGaussian α (x i - 1 / 2)| = foldedDProduct α x := by
    rw [Finset.abs_prod]
    unfold foldedDProduct
    apply Finset.prod_congr rfl
    intro i _
    exact alternatingGaussian_halfshift_fold hα (x i)
  have hb := neg_abs_le (∏ i, alternatingGaussian α (x i))
  have hd := neg_abs_le (∏ i, alternatingGaussian α (x i - 1 / 2))
  rw [hB] at hb
  rw [hD] at hd
  rw [dPlusGaussian_eq_product hα, hA, hC]
  linarith

theorem thetaMomentNumerator_empirical {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (x : Fin n → ℝ) :
    thetaMomentNumerator hα (foldedEmpirical hn x) =
      foldedAProduct α x ^ (8 / (n : ℝ)) + foldedCProduct α x ^ (8 / (n : ℝ)) -
      foldedBProduct α x ^ (8 / (n : ℝ)) - foldedDProduct α x ^ (8 / (n : ℝ)) := by
  unfold thetaMomentNumerator
  rw [geometricMoment_foldedEmpirical hn x 8 (by norm_num) _
      (fun t ↦ (thetaAMap_pos hα t).le),
    geometricMoment_foldedEmpirical hn x 8 (by norm_num) _
      (fun t ↦ (thetaCMap_pos hα t).le),
    geometricMoment_foldedEmpirical hn x 8 (by norm_num) _ (thetaBMap_nonneg hα),
    geometricMoment_foldedEmpirical hn x 8 (by norm_num) _ (thetaDMap_nonneg hα)]
  rfl

lemma dimension_rpow_cancel {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 0 < n) :
    (p ^ (8 / (n : ℝ))) ^ ((n : ℝ) / 8) = p := by
  rw [← Real.rpow_mul hp]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show 8 / (n : ℝ) * ((n : ℝ) / 8) = 1 by field_simp]
  exact Real.rpow_one p

lemma base_rpow_dimension {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (a ^ 4) ^ ((n : ℝ) / 8) = a ^ ((n : ℝ) / 2) := by
  rw [← Real.rpow_natCast_mul ha]
  congr 1
  ring

/-- The all-dimensional analytic lower bound, with its exact measure dependency explicit. -/
theorem dPlusGaussian_lower_of_theta {n : ℕ} (hn : 8 ≤ n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ)
    (hbase : 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤
      thetaMomentNumerator hα (foldedEmpirical (by omega) x)) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ≤ dPlusGaussian α x := by
  have hn0 : 0 < n := by omega
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [thetaMomentNumerator_empirical] at hbase
  have hB := foldedBProduct_nonneg hα x
  have hD := foldedDProduct_nonneg hα x
  have hA := foldedAProduct_pos hα x
  have hC := foldedCProduct_pos hα x
  have he : 0 < 8 / (n : ℝ) := div_pos (by norm_num) hnR0
  have hlift := dimension_lift_bound
    (Real.rpow_nonneg hB _) (Real.rpow_nonneg hD _)
    (Real.rpow_le_rpow hB (foldedBProduct_lt_A hn0 hα x).le he.le)
    (Real.rpow_le_rpow hD (foldedDProduct_lt_C hn0 hα x).le he.le)
    (pow_nonneg (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))).le 4)
    (show 1 ≤ (n : ℝ) / 8 by linarith) hbase
  rw [dimension_rpow_cancel hA.le hn0, dimension_rpow_cancel hC.le hn0,
    dimension_rpow_cancel hB hn0, dimension_rpow_cancel hD hn0,
    base_rpow_dimension (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))).le] at hlift
  linarith [dPlusGaussian_folded_lower hα x]

theorem dPlusGaussian_equality_products_of_theta {n : ℕ} (hn : 8 < n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ)
    (hbase : 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤
      thetaMomentNumerator hα (foldedEmpirical (by omega) x))
    (heq : dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2)) :
    foldedBProduct α x = 0 ∧ foldedDProduct α x = 0 ∧
      foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ∧
      foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) := by
  have hn0 : 0 < n := by omega
  have hnR : (8 : ℝ) < n := by exact_mod_cast hn
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : 0 < 8 / (n : ℝ) := div_pos (by norm_num) hnR0
  have hB := foldedBProduct_nonneg hα x
  have hD := foldedDProduct_nonneg hα x
  have hA := foldedAProduct_pos hα x
  have hC := foldedCProduct_pos hα x
  have hac := mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  rw [thetaMomentNumerator_empirical] at hbase
  have hltA := Real.rpow_lt_rpow hB (foldedBProduct_lt_A hn0 hα x) he
  have hltC := Real.rpow_lt_rpow hD (foldedDProduct_lt_C hn0 hα x) he
  have hlower := dimension_lift_bound (Real.rpow_nonneg hB _) (Real.rpow_nonneg hD _)
    hltA.le hltC.le (pow_nonneg hac.le 4) (show 1 ≤ (n : ℝ) / 8 by linarith) hbase
  have hid := dimension_lift_equality (Real.rpow_nonneg hB _) (Real.rpow_nonneg hD _)
    hltA hltC (pow_pos hac 4) (show 1 < (n : ℝ) / 8 by linarith) hbase
  have heqlift :
      (foldedAProduct α x ^ (8 / (n : ℝ))) ^ ((n : ℝ) / 8) +
      (foldedCProduct α x ^ (8 / (n : ℝ))) ^ ((n : ℝ) / 8) -
      (foldedBProduct α x ^ (8 / (n : ℝ))) ^ ((n : ℝ) / 8) -
      (foldedDProduct α x ^ (8 / (n : ℝ))) ^ ((n : ℝ) / 8) =
      2 * ((gaussian α 0 * gaussian α (1 / 2)) ^ 4) ^ ((n : ℝ) / 8) := by
    apply le_antisymm _ hlower
    rw [dimension_rpow_cancel hA.le hn0, dimension_rpow_cancel hC.le hn0,
      dimension_rpow_cancel hB hn0, dimension_rpow_cancel hD hn0, base_rpow_dimension hac.le]
    have h := dPlusGaussian_folded_lower hα x
    rw [heq] at h
    linarith
  obtain ⟨hB0, hD0, hAeq, hCeq⟩ := hid.mp heqlift
  have hn8 : (n : ℝ) / 8 ≠ 0 :=
    (div_pos hnR0 (by norm_num : (0 : ℝ) < 8)).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun r : ℝ ↦ r ^ ((n : ℝ) / 8)) hB0
    simpa only [dimension_rpow_cancel hB hn0,
      Real.zero_rpow hn8] using h
  · have h := congrArg (fun r : ℝ ↦ r ^ ((n : ℝ) / 8)) hD0
    simpa only [dimension_rpow_cancel hD hn0,
      Real.zero_rpow hn8] using h
  · have h := congrArg (fun r : ℝ ↦ r ^ ((n : ℝ) / 8)) hAeq
    simpa only [dimension_rpow_cancel hA.le hn0, base_rpow_dimension hac.le] using h
  · have h := congrArg (fun r : ℝ ↦ r ^ ((n : ℝ) / 8)) hCeq
    simpa only [dimension_rpow_cancel hC.le hn0, base_rpow_dimension hac.le] using h

end PaperVerification.ColdSpots
