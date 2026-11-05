module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order
public import paper_verification.lattice002
public import paper_verification.lattice003

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.DnMoments
section Source_DnMoments

-- original header: module
-- original header: public import PaperVerification.DnGaussian
-- original header: public import PaperVerification.DimensionLift
-- original header: public import PaperVerification.ThetaGeometricTransfer
-- original header: public import PaperVerification.FiniteGeometricMean
-- original header: public import PaperVerification.LatticeGeometry
-- original header: public import Mathlib.MeasureTheory.MeasurableSpace.Instances
-- original header: public import Mathlib.Topology.Order
-- original header: @[expose] public section
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
end
end Source_DnMoments
-- END ORIGINAL PaperVerification.DnMoments


-- BEGIN ORIGINAL PaperVerification.DnEquality
section Source_DnEquality

-- original header: module
-- original header: public import PaperVerification.DnMoments
-- original header: public import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators
open MeasureTheory

lemma prod_eq_const_forces_factors {n : ℕ} (f : Fin n → ℝ) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ i, c ≤ f i) (heq : (∏ i, f i) = c ^ n) :
    ∀ i, f i = c := by
  intro i
  by_contra hne
  have hlt : c < f i := lt_of_le_of_ne (hbound i) (Ne.symm hne)
  have hp := Finset.prod_lt_prod₀ (s := Finset.univ) (f := fun _ : Fin n ↦ c)
    (g := f) (fun _ _ ↦ hc) (fun i _ ↦ hbound i) ⟨i, Finset.mem_univ i, hlt⟩
  have hp' : c ^ n < c ^ n := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, heq] using hp
  exact (lt_irrefl (c ^ n)) hp'

lemma half_interval_two_mul_integer_iff {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    (∃ z : ℤ, 2 * t = (z : ℝ)) ↔ t = 0 ∨ t = 1 / 2 := by
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by linarith)
    have hz1 : z ≤ (1 : ℤ) := by exact_mod_cast (show (z : ℝ) ≤ 1 by linarith)
    have hcases : z = 0 ∨ z = 1 := by omega
    rcases hcases with rfl | rfl
    · left
      norm_num at hz
      linarith
    · right
      norm_num at hz
      linarith
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

theorem folded_endpoints_of_product_equalities {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ)
    (hA : foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2))
    (hC : foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2)) :
    ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 := by
  let c := gaussian α 0 * gaussian α (1 / 2)
  have hc : 0 < c := mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  have hprod : (∏ i, gaussian α (foldedRadius x i) *
      gaussian α (foldedRadius x i - 1 / 2)) = c ^ n := by
    rw [Finset.prod_mul_distrib]
    change foldedAProduct α x * foldedCProduct α x = _
    rw [hA, hC]
    change c ^ ((n : ℝ) / 2) * c ^ ((n : ℝ) / 2) = c ^ n
    rw [← Real.rpow_add hc, show (n : ℝ) / 2 + (n : ℝ) / 2 = n by ring,
      Real.rpow_natCast]
  have hpoint := prod_eq_const_forces_factors _ hc
    (fun i ↦ gaussian_shift_product_min hα (foldedRadius x i)) hprod
  intro i
  apply (half_interval_two_mul_integer_iff (foldedRadius_nonneg x i)
    (foldedRadius_le_half x i)).mp
  exact (gaussian_shift_product_min_iff hα (foldedRadius x i)).mp (hpoint i)

lemma log_foldedAProduct_of_endpoints {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    Real.log (foldedAProduct α x) = (n : ℝ) * Real.log (gaussian α 0) +
      2 * (∑ i, foldedRadius x i) *
        (Real.log (gaussian α (1 / 2)) - Real.log (gaussian α 0)) := by
  unfold foldedAProduct
  rw [Real.log_prod (fun i _ ↦ (gaussian_pos hα _).ne')]
  have hi (i : Fin n) : Real.log (gaussian α (foldedRadius x i)) =
      Real.log (gaussian α 0) + 2 * foldedRadius x i *
        (Real.log (gaussian α (1 / 2)) - Real.log (gaussian α 0)) := by
    rcases hx i with h | h <;> rw [h] <;> ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum]

lemma log_foldedCProduct_of_endpoints {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    Real.log (foldedCProduct α x) = (n : ℝ) * Real.log (gaussian α (1 / 2)) +
      2 * (∑ i, foldedRadius x i) *
        (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) := by
  unfold foldedCProduct
  rw [Real.log_prod (fun i _ ↦ (gaussian_pos hα _).ne')]
  have hi (i : Fin n) : Real.log (gaussian α (foldedRadius x i - 1 / 2)) =
      Real.log (gaussian α (1 / 2)) + 2 * foldedRadius x i *
        (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) := by
    rcases hx i with h | h
    · rw [h, zero_sub, gaussian_even]
      ring
    · rw [h, sub_self]
      ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem balanced_of_folded_product_equalities {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ)
    (hA : foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2))
    (hC : foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2)) :
    BalancedHalfGrid x := by
  have hx := folded_endpoints_of_product_equalities hα x hA hC
  refine ⟨hx, ?_⟩
  have hlog := congrArg Real.log (hA.trans hC.symm)
  rw [log_foldedAProduct_of_endpoints hα x hx,
    log_foldedCProduct_of_endpoints hα x hx] at hlog
  have hlt : Real.log (gaussian α (1 / 2)) < Real.log (gaussian α 0) :=
    Real.log_lt_log (gaussian_pos hα _) (gaussian_half_lt_zero hα)
  have hp : ((n : ℝ) - 4 * ∑ i, foldedRadius x i) *
      (Real.log (gaussian α 0) - Real.log (gaussian α (1 / 2))) = 0 := by
    nlinarith only [hlog]
  have hzero := (mul_eq_zero.mp hp).resolve_right (sub_pos.mpr hlt).ne'
  linarith

lemma foldedProducts_of_balanced {n : ℕ} {α : ℝ} (hα : 0 < α)
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    foldedAProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ∧
    foldedCProduct α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) := by
  have hac := mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))
  have hloga := log_foldedAProduct_of_endpoints hα x hx.1
  have hlogc := log_foldedCProduct_of_endpoints hα x hx.1
  rw [hx.2] at hloga hlogc
  constructor
  · rw [← Real.exp_log (foldedAProduct_pos hα x), hloga, Real.rpow_def_of_pos hac,
      Real.log_mul (gaussian_pos hα 0).ne' (gaussian_pos hα (1 / 2)).ne']
    congr 1
    ring
  · rw [← Real.exp_log (foldedCProduct_pos hα x), hlogc, Real.rpow_def_of_pos hac,
      Real.log_mul (gaussian_pos hα 0).ne' (gaussian_pos hα (1 / 2)).ne']
    congr 1
    ring

lemma balanced_has_both_endpoints {n : ℕ} (hn : 0 < n) {x : Fin n → ℝ}
    (hx : BalancedHalfGrid x) :
    (∃ i, foldedRadius x i = 0) ∧ ∃ i, foldedRadius x i = 1 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · by_contra h
    push_neg at h
    have hall : ∀ i, foldedRadius x i = 1 / 2 := fun i ↦ (hx.1 i).resolve_left (h i)
    have hs := hx.2
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    linarith
  · by_contra h
    push_neg at h
    have hall : ∀ i, foldedRadius x i = 0 := fun i ↦ (hx.1 i).resolve_right (h i)
    have hs := hx.2
    simp only [hall, Finset.sum_const_zero] at hs
    linarith

theorem dPlusGaussian_of_balanced {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) := by
  classical
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := balanced_has_both_endpoints hn hx
  have hB : (∏ k, alternatingGaussian α (x k)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply abs_eq_zero.mp
    rw [alternatingGaussian_fold hα]
    change alternatingGaussian α (foldedRadius x j) = 0
    rw [hj, alternatingGaussian_half]
  have hD : (∏ k, alternatingGaussian α (x k - 1 / 2)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply abs_eq_zero.mp
    rw [alternatingGaussian_halfshift_fold hα]
    change alternatingGaussian α (foldedRadius x i - 1 / 2) = 0
    rw [hi, zero_sub, alternatingGaussian_even, alternatingGaussian_half]
  obtain ⟨hA, hC⟩ := foldedProducts_of_balanced hα hx
  rw [dPlusGaussian_eq_product hα, hB, hD]
  have hpA : (∏ i, gaussian α (x i)) = foldedAProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_fold α (x i)
  have hpC : (∏ i, gaussian α (x i - 1 / 2)) = foldedCProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_halfshift_fold α (x i)
  rw [hpA, hpC, hA, hC]
  ring

/-- Exact equivalence to the geometric deep-hole locus in every even n>8,
conditional only on the displayed theta measure theorem being supplied. -/
theorem coldSpot_dPlus_iff_deepHole_of_theta {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α)
    (hbase : ∀ μ : ProbabilityMeasure HalfInterval,
      2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ)
    (x : Fin n → ℝ) : IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x := by
  have hn0 : 0 < n := by omega
  rw [isDeepHole_dPlus_iff_balanced hn heven x]
  constructor
  · intro hcold
    obtain ⟨y, hy⟩ := exists_balancedHalfGrid heven
    have hxy := hcold y
    rw [setGaussian_dPlus_eq hn0 hα, setGaussian_dPlus_eq hn0 hα,
      dPlusGaussian_of_balanced hn0 hα hy] at hxy
    have heq := le_antisymm hxy (dPlusGaussian_lower_of_theta hn.le hα x
      (hbase (foldedEmpirical hn0 x)))
    obtain ⟨_, _, hA, hC⟩ := dPlusGaussian_equality_products_of_theta hn hα x
      (hbase (foldedEmpirical hn0 x)) heq
    exact balanced_of_folded_product_equalities hα x hA hC
  · intro hx y
    rw [setGaussian_dPlus_eq hn0 hα, setGaussian_dPlus_eq hn0 hα,
      dPlusGaussian_of_balanced hn0 hα hx]
    exact dPlusGaussian_lower_of_theta hn.le hα y (hbase (foldedEmpirical hn0 y))

end PaperVerification.ColdSpots
end
end Source_DnEquality
-- END ORIGINAL PaperVerification.DnEquality


-- BEGIN ORIGINAL PaperVerification.ThetaInequality
section Source_ThetaInequality

-- original header: module
-- original header: public import PaperVerification.ThetaGeometricTransfer
-- original header: public import PaperVerification.HyperbolicTheorem
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter
open PaperVerification.Hyperbolic

lemma centeredCoshMap_eq (R : ℝ) : centeredCoshMap R = intervalCenteredCosh R := rfl

/-- The inequality in Proposition 3.2, for every Borel probability measure,
including endpoint atoms and vanishing alternating geometric means. -/
theorem theta_geometric_mean_inequality {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ := by
  apply thetaMoment_bound_from_hyperbolic hα μ
  rw [centeredCoshMap_eq]
  exact hyperbolic_geometric_mean_inequality (thetaR α) (thetaR_pos hα) (thetaPush hα μ)

theorem theta_geometric_mean_inequality_literal {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤
      geometricMean (thetaAMap hα) μ ^ 8 + geometricMean (thetaCMap hα) μ ^ 8 -
      geometricMean (thetaBMap hα) μ ^ 8 - geometricMean (thetaDMap hα) μ ^ 8 := by
  have h := theta_geometric_mean_inequality hα μ
  unfold thetaMomentNumerator at h
  erw [geometricMoment_nat 8 (thetaAMap hα) μ,
    geometricMoment_nat 8 (thetaCMap hα) μ,
    geometricMoment_nat 8 (thetaBMap hα) μ,
    geometricMoment_nat 8 (thetaDMap hα) μ] at h
  exact h

/-- Exact equality before converting the three-point support into the paper's
four displayed measures. The conversion is a separate measure-theoretic lemma. -/
theorem theta_geometric_mean_equality_conditions {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    thetaMomentNumerator hα μ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      (∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval),
        (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 1 / 2) ∧
      HyperbolicEquality (thetaR α) (thetaPush hα μ) := by
  have hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ) := by
    rw [centeredCoshMap_eq]
    exact hyperbolic_geometric_mean_inequality (thetaR α) (thetaR_pos hα) (thetaPush hα μ)
  rw [thetaMoment_equality_from_hyperbolic hα μ hH,
    thetaDiagonal_geometric_eq_iff hα μ, centeredCoshMap_eq,
    hyperbolic_geometric_mean_equality_iff (thetaR α) (thetaR_pos hα)]

end PaperVerification.ColdSpots
end
end Source_ThetaInequality
-- END ORIGINAL PaperVerification.ThetaInequality


-- BEGIN ORIGINAL PaperVerification.DnTheorems
section Source_DnTheorems

-- original header: module
-- original header: public import PaperVerification.DnEquality
-- original header: public import PaperVerification.ThetaInequality
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

/-- Theorem 3.3's lower bound over every dimension n>=8 and every positive alpha. -/
theorem dPlusGaussian_lower {n : ℕ} (hn : 8 ≤ n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ≤ dPlusGaussian α x :=
  dPlusGaussian_lower_of_theta hn hα x (theta_geometric_mean_inequality hα _)

/-- The exact Gaussian equality set in every dimension strictly above eight. -/
theorem dPlusGaussian_eq_min_iff_balanced {n : ℕ} (hn : 8 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ↔
      BalancedHalfGrid x := by
  constructor
  · intro heq
    obtain ⟨_, _, hA, hC⟩ := dPlusGaussian_equality_products_of_theta hn hα x
      (theta_geometric_mean_inequality hα _) heq
    exact balanced_of_folded_product_equalities hα x hA hC
  · exact dPlusGaussian_of_balanced (by omega) hα

/-- The literal half-integer-grid equality set in equation (10), including the
usual count of noninteger coordinates and the whole even dimension range n>8. -/
theorem dPlusGaussian_eq_min_iff_paperHalfGrid {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ ((n : ℝ) / 2) ↔
      PaperHalfGrid x := by
  rw [dPlusGaussian_eq_min_iff_balanced hn hα x, balancedHalfGrid_iff_paperHalfGrid heven x]

/-- The D_n^+ part of Theorem 1.1 above dimension eight, stated for the actual
infinite lattice Gaussian and actual Euclidean deep-hole predicate. -/
theorem coldSpot_dPlus_iff_deepHole_above_eight {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x :=
  coldSpot_dPlus_iff_deepHole_of_theta hn heven hα (theta_geometric_mean_inequality hα) x

end PaperVerification.ColdSpots
end
end Source_DnTheorems
-- END ORIGINAL PaperVerification.DnTheorems


-- BEGIN ORIGINAL PaperVerification.DnSigns
section Source_DnSigns

-- original header: module
-- original header: public import PaperVerification.DnEquality
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

lemma alternatingGaussian_fold_sign (α t : ℝ) (q : ℤ) :
    alternatingGaussian α t = paritySign q * alternatingGaussian α |t - (q : ℝ)| := by
  have h := alternatingGaussian_int_period α (t - (q : ℝ)) q
  rw [sub_add_cancel] at h
  rw [alternatingGaussian_abs_argument]
  exact h

lemma alternatingGaussian_halfRounded_sign {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    alternatingGaussian α (x i - 1 / 2) =
      paritySign (halfRoundedInt x i) * alternatingGaussian α (foldedRadius x i - 1 / 2) := by
  rw [alternatingGaussian_fold_sign α (x i - 1 / 2) (halfRoundedInt x i)]
  have habs : |x i - 1 / 2 - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  rw [habs, show (1 / 2 : ℝ) - foldedRadius x i = -(foldedRadius x i - 1 / 2) by ring,
    alternatingGaussian_even]

theorem signed_integer_product_fold {n : ℕ} (α : ℝ) (x : Fin n → ℝ) :
    (∏ i, alternatingGaussian α (x i)) =
      paritySign (∑ i, roundedInt x i) * foldedBProduct α x := by
  have hi (i : Fin n) : alternatingGaussian α (x i) =
      paritySign (roundedInt x i) * alternatingGaussian α (foldedRadius x i) :=
    alternatingGaussian_fold_sign α (x i) (roundedInt x i)
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, ← paritySign_sum]
  rfl

theorem signed_half_product_fold {n : ℕ} (α : ℝ) (x : Fin n → ℝ) :
    (∏ i, alternatingGaussian α (x i - 1 / 2)) =
      paritySign (∑ i, halfRoundedInt x i) * foldedDProduct α x := by
  rw [show (∏ i, alternatingGaussian α (x i - 1 / 2)) =
      ∏ i, paritySign (halfRoundedInt x i) *
        alternatingGaussian α (foldedRadius x i - 1 / 2) by
    apply Finset.prod_congr rfl
    intro i _
    exact alternatingGaussian_halfRounded_sign α x i]
  rw [Finset.prod_mul_distrib, ← paritySign_sum]
  rfl

theorem dPlusGaussian_signed_fold {n : ℕ} {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) *
      (foldedAProduct α x + foldedCProduct α x +
        paritySign (∑ i, roundedInt x i) * foldedBProduct α x +
        paritySign (∑ i, halfRoundedInt x i) * foldedDProduct α x) := by
  rw [dPlusGaussian_eq_product hα, signed_integer_product_fold, signed_half_product_fold]
  have ha : (∏ i, gaussian α (x i)) = foldedAProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_fold α (x i)
  have hc : (∏ i, gaussian α (x i - 1 / 2)) = foldedCProduct α x := by
    apply Finset.prod_congr rfl
    intro i _
    exact gaussian_halfshift_fold α (x i)
  rw [ha,hc]
  ring

def FoldedSignCondition {n : ℕ} (α : ℝ) (x : Fin n → ℝ) : Prop :=
  (foldedBProduct α x = 0 ∨ ¬Even (∑ i, roundedInt x i)) ∧
  (foldedDProduct α x = 0 ∨ ¬Even (∑ i, halfRoundedInt x i))

theorem dPlusGaussian_eq_folded_lower_iff {n : ℕ} {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    dPlusGaussian α x = (1 / 2) * (foldedAProduct α x + foldedCProduct α x -
      foldedBProduct α x - foldedDProduct α x) ↔ FoldedSignCondition α x := by
  rw [dPlusGaussian_signed_fold hα]
  unfold FoldedSignCondition paritySign
  have hb := foldedBProduct_nonneg hα x
  have hd := foldedDProduct_nonneg hα x
  by_cases hi : Even (∑ i, roundedInt x i) <;>
    by_cases hh : Even (∑ i, halfRoundedInt x i) <;>
    simp only [hi, hh, if_true, if_false, not_true_eq_false, not_false_eq_true,
      or_false, or_true, and_true, true_and]
  all_goals constructor <;> intro h
  all_goals first | exact ⟨by linarith, by linarith⟩ | rcases h with ⟨h₁,h₂⟩; linarith | linarith | trivial

lemma folded_alternating_zero_of_balanced {n : ℕ} (hn : 0 < n) {α : ℝ}
    {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    foldedBProduct α x = 0 ∧ foldedDProduct α x = 0 := by
  classical
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := balanced_has_both_endpoints hn hx
  constructor
  · exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, alternatingGaussian_half])
  · exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [hi, zero_sub, alternatingGaussian_even, alternatingGaussian_half])

lemma folded_B_constant {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    foldedBProduct α x = alternatingGaussian α t ^ n := by
  simp [foldedBProduct, ht]

lemma folded_D_constant {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    foldedDProduct α x = alternatingGaussian α (t - 1 / 2) ^ n := by
  simp [foldedDProduct, ht]

end PaperVerification.ColdSpots
end
end Source_DnSigns
-- END ORIGINAL PaperVerification.DnSigns


-- BEGIN ORIGINAL PaperVerification.ThetaEquality
section Source_ThetaEquality

-- original header: module
-- original header: public import PaperVerification.ThetaInequality
-- original header: @[expose] public section
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
end
end Source_ThetaEquality
-- END ORIGINAL PaperVerification.ThetaEquality


-- BEGIN ORIGINAL PaperVerification.ThetaEmpirical
section Source_ThetaEmpirical

-- original header: module
-- original header: public import PaperVerification.ThetaEquality
-- original header: public import PaperVerification.DnMoments
-- original header: @[expose] public section
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
end
end Source_ThetaEmpirical
-- END ORIGINAL PaperVerification.ThetaEmpirical


-- BEGIN ORIGINAL PaperVerification.E8Theorems
section Source_E8Theorems

-- original header: module
-- original header: public import PaperVerification.DnTheorems
-- original header: public import PaperVerification.DnSigns
-- original header: public import PaperVerification.ThetaEmpirical
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem folded_equality_signs_iff_E8_hole {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    FoldedThetaEquality x ∧ FoldedSignCondition α x ↔ E8FoldedHole x := by
  have hb0 : 0 < alternatingGaussian α 0 ^ 8 := pow_pos (alternatingGaussian_zero_pos hα) 8
  have hbq : 0 < alternatingGaussian α (1 / 4) ^ 8 :=
    pow_pos (alternatingGaussian_pos hα (by norm_num) (by norm_num)) 8
  constructor
  · rintro ⟨hx, hi, hh⟩
    rcases hx with h0 | hq | hhf | hbal
    · apply Or.inl
      refine ⟨h0, ?_⟩
      rw [folded_B_constant α x 0 h0] at hi
      exact hi.resolve_left hb0.ne'
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨hq, ?_, ?_⟩
      · rw [folded_B_constant α x (1 / 4) hq] at hi
        exact hi.resolve_left hbq.ne'
      · rw [folded_D_constant α x (1 / 4) hq,
          show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4) by ring, alternatingGaussian_even] at hh
        exact hh.resolve_left hbq.ne'
    · apply Or.inr ∘ Or.inl
      refine ⟨hhf, ?_⟩
      rw [folded_D_constant α x (1 / 2) hhf, sub_self] at hh
      exact hh.resolve_left hb0.ne'
    · exact Or.inr (Or.inr (Or.inl hbal))
  · rintro (⟨h0, hi⟩ | ⟨hh, hp⟩ | hbal | ⟨hq, hi, hh⟩)
    · refine ⟨Or.inl h0, Or.inr hi, Or.inl ?_⟩
      rw [folded_D_constant α x 0 h0, zero_sub, alternatingGaussian_even,
        alternatingGaussian_half, zero_pow (by decide : 8 ≠ 0)]
    · refine ⟨Or.inr (Or.inr (Or.inl hh)), Or.inl ?_, Or.inr hp⟩
      rw [folded_B_constant α x (1 / 2) hh, alternatingGaussian_half, zero_pow (by decide : 8 ≠ 0)]
    · obtain ⟨hb,hd⟩ := folded_alternating_zero_of_balanced (by decide : 0 < 8) hbal
      exact ⟨Or.inr (Or.inr (Or.inr hbal)), Or.inl hb, Or.inl hd⟩
    · exact ⟨Or.inr (Or.inl hq), Or.inr hi, Or.inr hh⟩

lemma thetaMomentNumerator_eight {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    thetaMomentNumerator hα (foldedEmpirical (by decide : 0 < 8) x) =
      foldedAProduct α x + foldedCProduct α x - foldedBProduct α x - foldedDProduct α x := by
  rw [thetaMomentNumerator_empirical]
  norm_num

/-- The full exceptional dimension-eight equality analysis in canonical folded
coordinates, including both parity restrictions on the quarter family. -/
theorem dPlusGaussian_eight_eq_min_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    dPlusGaussian α x = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔ E8FoldedHole x := by
  rw [← folded_equality_signs_iff_E8_hole hα x,
    ← folded_theta_equality_iff (by decide : 0 < 8) hα x,
    ← dPlusGaussian_eq_folded_lower_iff hα x, thetaMomentNumerator_eight]
  have hbase := theta_geometric_mean_inequality hα (foldedEmpirical (by decide : 0 < 8) x)
  rw [thetaMomentNumerator_eight] at hbase
  have hfold := dPlusGaussian_folded_lower hα x
  constructor
  · intro heq
    constructor <;> linarith
  · rintro ⟨h₁,h₂⟩
    linarith

theorem dPlusGaussian_eight_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ dPlusGaussian α x := by
  have h := dPlusGaussian_lower (by decide : 8 ≤ 8) hα x
  norm_num at h
  exact h

/-- The E8 part of Theorem 1.1, for every point in the real ambient space and
every positive Gaussian parameter. -/
theorem coldSpot_E8_iff_deepHole {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    IsColdSpot (dPlusSet 8) α x ↔ IsDeepHole (dPlusSet 8) x := by
  rw [isDeepHole_E8_iff, ← dPlusGaussian_eight_eq_min_iff hα]
  constructor
  · intro h
    obtain ⟨y,hy⟩ := exists_balancedHalfGrid (by decide : Even 8)
    have hxy := h y
    rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      dPlusGaussian_of_balanced (by decide : 0 < 8) hα hy] at hxy
    norm_num at hxy
    exact le_antisymm hxy (dPlusGaussian_eight_lower hα x)
  · intro heq y
    rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
      setGaussian_dPlus_eq (by decide : 0 < 8) hα, heq]
    exact dPlusGaussian_eight_lower hα y

/-- The entire D_n^+ family in Theorem 1.1, with no omitted dimension or
additional geometric or analytic hypothesis. -/
theorem coldSpot_dPlus_iff_deepHole {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x := by
  rcases eq_or_lt_of_le hn with rfl | hlt
  · exact coldSpot_E8_iff_deepHole hα x
  · exact coldSpot_dPlus_iff_deepHole_above_eight hlt heven hα x

lemma even_dimension_half_cast {n : ℕ} (heven : Even n) :
    (n : ℝ) / 2 = ((n / 2 : ℕ) : ℝ) := by
  obtain ⟨k,rfl⟩ := heven
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

/-- Theorem 3.3's attained minimum in the paper's integer-exponent notation. -/
theorem dPlusGaussian_minimum {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2) ≤ setGaussian (dPlusSet n) α x) ∧
    (∃ x, setGaussian (dPlusSet n) α x = (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2)) := by
  have hn0 : 0 < n := by omega
  constructor
  · intro x
    rw [setGaussian_dPlus_eq hn0 hα]
    have h := dPlusGaussian_lower hn hα x
    rwa [even_dimension_half_cast heven, Real.rpow_natCast] at h
  · obtain ⟨x,hx⟩ := exists_balancedHalfGrid heven
    refine ⟨x, ?_⟩
    rw [setGaussian_dPlus_eq hn0 hα, dPlusGaussian_of_balanced hn0 hα hx,
      even_dimension_half_cast heven, Real.rpow_natCast]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_dPlus_iff_deepHole
#print axioms PaperVerification.ColdSpots.dPlusGaussian_minimum
end
end Source_E8Theorems
-- END ORIGINAL PaperVerification.E8Theorems


-- BEGIN ORIGINAL PaperVerification.E7Coordinates
section Source_E7Coordinates

-- original header: module
-- original header: public import PaperVerification.DnGaussian
-- original header: public import Mathlib.LinearAlgebra.Pi
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: @[expose] public section
/-!
# The dual E7 lattice in its genuine seven-dimensional ambient space

All ambient points have coordinate sum zero. The lattice below is the orthogonal
projection of the actual E8 coordinate lattice, and the duality theorem identifies
it with the integral dual of E8 intersected with that hyperplane. Thus no assertion
about a rank-seven lattice quantifies over the larger eight-dimensional space.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def zeroSumSpace : Submodule ℝ (Fin 8 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, x i) = 0 at hx
    change (∑ i, y i) = 0 at hy
    change (∑ i, (x + y) i) = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change (∑ i, x i) = 0 at hx
    change (∑ i, (a • x) i) = 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- Evaluation of a vector in the literal zero-sum subspace. -/
instance zeroSumSpaceCoeFun : CoeFun zeroSumSpace (fun _ ↦ Fin 8 → ℝ) where
  coe x := x.val

def project8 (x : Fin 8 → ℝ) : zeroSumSpace :=
  ⟨fun i ↦ x i - (∑ j, x j) / 8, by
    change (∑ i, (x i - (∑ j, x j) / 8)) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring⟩

@[simp] lemma project8_apply (x : Fin 8 → ℝ) (i : Fin 8) :
    project8 x i = x i - (∑ j, x j) / 8 := rfl

lemma zeroSumSpace_sum (x : zeroSumSpace) : (∑ i, x i) = 0 := x.property

@[simp] lemma project8_coe (x : zeroSumSpace) : project8 x.val = x := by
  apply Subtype.ext
  ext i
  simp only [project8_apply, zeroSumSpace_sum, zero_div, sub_zero]

theorem project8_add_constant (x : Fin 8 → ℝ) (c : ℝ) :
    project8 (fun i ↦ x i + c) = project8 x := by
  apply Subtype.ext
  ext i
  simp only [project8_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def coordinateInner (x y : Fin 8 → ℝ) : ℝ := ∑ i, x i * y i

theorem coordinateInner_project_left (x : Fin 8 → ℝ) (y : zeroSumSpace) :
    coordinateInner (project8 x).val y.val = coordinateInner x y.val := by
  unfold coordinateInner
  simp only [project8_apply, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    zeroSumSpace_sum, mul_zero, sub_zero]

def e7Set : Set zeroSumSpace := {x | x.val ∈ dPlusSet 8}

def e7DualSet : Set zeroSumSpace :=
  {y | ∀ x ∈ e7Set, ∃ k : ℤ, coordinateInner y.val x.val = (k : ℝ)}

def e7ProjectedSet : Set zeroSumSpace :=
  {y | ∃ z : Fin 8 → ℤ, Even (∑ i, z i) ∧ y = project8 (intVec z)}

theorem project8_mem_e7Projected {v : Fin 8 → ℝ} (hv : v ∈ dPlusSet 8) :
    project8 v ∈ e7ProjectedSet := by
  rcases hv with ⟨z, hz, rfl | rfl⟩
  · exact ⟨z, hz, rfl⟩
  · exact ⟨z, hz, project8_add_constant (intVec z) (1 / 2)⟩

theorem e7Projected_mem_dual {y : zeroSumSpace} (hy : y ∈ e7ProjectedSet) :
    y ∈ e7DualSet := by
  rcases hy with ⟨z, hz, rfl⟩
  intro x hx
  rw [coordinateInner_project_left]
  rcases hx with ⟨w, hw, h | h⟩
  · refine ⟨∑ i, z i * w i, ?_⟩
    rw [h]
    simp [coordinateInner, intVec]
  · obtain ⟨k, hk⟩ := hz
    refine ⟨(∑ i, z i * w i) + k, ?_⟩
    rw [h]
    simp only [coordinateInner, intVec, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, Int.cast_add, Int.cast_sum, Int.cast_mul]
    have hcast : (∑ i, (z i : ℝ)) = (k : ℝ) + k := by exact_mod_cast hk
    rw [hcast]
    ring

def coordinateDifferenceInt (i : Fin 8) : Fin 8 → ℤ :=
  fun j ↦ (if j = i then 1 else 0) - (if j = 0 then 1 else 0)

lemma sum_coordinateDifferenceInt (i : Fin 8) :
    (∑ j, coordinateDifferenceInt i j) = 0 := by
  simp [coordinateDifferenceInt, Finset.sum_sub_distrib]

def coordinateDifference (i : Fin 8) : zeroSumSpace :=
  ⟨intVec (coordinateDifferenceInt i), by
    change (∑ j, (coordinateDifferenceInt i j : ℝ)) = 0
    exact_mod_cast sum_coordinateDifferenceInt i⟩

lemma coordinateDifference_mem_e7 (i : Fin 8) : coordinateDifference i ∈ e7Set := by
  refine ⟨coordinateDifferenceInt i, ?_, Or.inl rfl⟩
  rw [sum_coordinateDifferenceInt]
  exact ⟨0, rfl⟩

lemma inner_coordinateDifference (y : zeroSumSpace) (i : Fin 8) :
    coordinateInner y.val (coordinateDifference i).val = y i - y 0 := by
  simp [coordinateInner, coordinateDifference, coordinateDifferenceInt, intVec,
    mul_sub, Finset.sum_sub_distrib, mul_ite]

def halfRootInt : Fin 8 → ℤ := fun i ↦ if i.val < 4 then 0 else -1

lemma sum_halfRootInt : (∑ i, halfRootInt i) = -4 := by
  norm_num [halfRootInt, Fin.sum_univ_succ]

def balancedHalfRoot : zeroSumSpace :=
  ⟨fun i ↦ (halfRootInt i : ℝ) + 1 / 2, by
    change (∑ i, ((halfRootInt i : ℝ) + 1 / 2)) = 0
    norm_num [halfRootInt, Fin.sum_univ_succ]⟩

lemma balancedHalfRoot_mem_e7 : balancedHalfRoot ∈ e7Set := by
  refine ⟨halfRootInt, ?_, Or.inr rfl⟩
  rw [sum_halfRootInt]
  exact ⟨-2, by norm_num⟩

/-- An explicit coordinate proof of the E7 dual/projection correspondence. -/
theorem e7DualSet_eq_projected : e7DualSet = e7ProjectedSet := by
  apply Set.Subset.antisymm
  · intro y hy
    have hi (i : Fin 8) : ∃ k : ℤ, y i - y 0 = (k : ℝ) := by
      simpa only [inner_coordinateDifference] using
        hy (coordinateDifference i) (coordinateDifference_mem_e7 i)
    choose z hz using hi
    have hsum : (∑ i, (z i : ℝ)) = -8 * y 0 := by
      calc
        _ = ∑ i, (y i - y 0) := Finset.sum_congr rfl (fun i _ ↦ (hz i).symm)
        _ = _ := by
          rw [Finset.sum_sub_distrib, zeroSumSpace_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    have hproj : y = project8 (intVec z) := by
      apply Subtype.ext
      ext i
      simp only [project8_apply, intVec, hsum]
      linarith [hz i]
    obtain ⟨k, hk⟩ := hy balancedHalfRoot balancedHalfRoot_mem_e7
    rw [hproj, coordinateInner_project_left] at hk
    have hdot : coordinateInner (intVec z) balancedHalfRoot.val =
        ((∑ i, z i * halfRootInt i : ℤ) : ℝ) + (∑ i, (z i : ℝ)) / 2 := by
      simp only [coordinateInner, intVec, balancedHalfRoot, mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul, Int.cast_sum, Int.cast_mul]
      ring
    rw [hdot] at hk
    push_cast at hk
    have hint : (∑ i, z i) =
        2 * (k - ∑ i, z i * halfRootInt i) := by
      apply Int.cast_injective (α := ℝ)
      push_cast
      linarith
    refine ⟨z, ?_, hproj⟩
    rw [hint]
    exact even_two_mul _
  · intro y hy
    exact e7Projected_mem_dual hy

def e7Lift (y : e7ProjectedSet) : Fin 8 → ℤ := Classical.choose y.property

lemma e7Lift_even (y : e7ProjectedSet) : Even (∑ i, e7Lift y i) :=
  (Classical.choose_spec y.property).1

lemma e7Lift_projects (y : e7ProjectedSet) : project8 (intVec (e7Lift y)) = y.val :=
  (Classical.choose_spec y.property).2.symm

lemma even_sum_add_constant (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) (q : ℤ) :
    Even (∑ i, (z i + q)) := by
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hz.add (by exact ⟨4 * q, by ring⟩)

lemma intVec_add_half_multiple_mem (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) (k : ℤ) :
    (fun i ↦ (z i : ℝ) + (k : ℝ) / 2) ∈ dPlusSet 8 := by
  rcases Int.even_or_odd k with he | ho
  · obtain ⟨q, hq⟩ := he
    refine ⟨fun i ↦ z i + q, even_sum_add_constant z hz q, Or.inl ?_⟩
    ext i
    rw [hq]
    simp only [Int.cast_add, intVec]
    ring
  · obtain ⟨q, hq⟩ := ho
    refine ⟨fun i ↦ z i + q, even_sum_add_constant z hz q, Or.inr ?_⟩
    ext i
    rw [hq]
    push_cast
    ring

def e8FibreMap (yk : e7ProjectedSet × ℤ) : dPlusSet 8 :=
  ⟨fun i ↦ (e7Lift yk.1 i : ℝ) + (yk.2 : ℝ) / 2,
    intVec_add_half_multiple_mem _ (e7Lift_even yk.1) yk.2⟩

lemma e8FibreMap_projects (y : e7ProjectedSet) (k : ℤ) :
    project8 (e8FibreMap (y, k)).val = y.val := by
  change project8 (fun i ↦ (e7Lift y i : ℝ) + (k : ℝ) / 2) = y.val
  rw [project8_add_constant]
  change project8 (intVec (e7Lift y)) = y.val
  exact e7Lift_projects y

/-- Exact infinite-fibre parametrization of E8, with no multiplicity. -/
theorem e8FibreMap_bijective : Function.Bijective e8FibreMap := by
  constructor
  · rintro ⟨y, k⟩ ⟨z, l⟩ h
    have hp := congrArg (fun v : dPlusSet 8 ↦ project8 v.val) h
    simp only [e8FibreMap_projects] at hp
    have hyz : y = z := Subtype.ext hp
    subst z
    have h0 := congrFun (congrArg Subtype.val h) 0
    change (e7Lift y 0 : ℝ) + (k : ℝ) / 2 = (e7Lift y 0 : ℝ) + (l : ℝ) / 2 at h0
    have hkl : k = l := Int.cast_injective (by linarith : (k : ℝ) = (l : ℝ))
    subst l
    rfl
  · intro v
    let y : e7ProjectedSet := ⟨project8 v.val, project8_mem_e7Projected v.property⟩
    have hp : project8 (intVec (e7Lift y)) = project8 v.val := e7Lift_projects y
    have hdiff (i : Fin 8) : v.val i - (e7Lift y i : ℝ) =
        v.val 0 - (e7Lift y 0 : ℝ) := by
      have hi := congrFun (congrArg Subtype.val hp) i
      have h0 := congrFun (congrArg Subtype.val hp) 0
      simp only [project8_apply, intVec] at hi h0
      linarith
    rcases v.property with ⟨w, hw, hv | hv⟩
    · refine ⟨(y, 2 * (w 0 - e7Lift y 0)), ?_⟩
      apply Subtype.ext
      ext i
      change (e7Lift y i : ℝ) + ((2 * (w 0 - e7Lift y 0) : ℤ) : ℝ) / 2 = v.val i
      have hd := hdiff i
      rw [hv] at hd ⊢
      simp only [intVec, Int.cast_mul, Int.cast_ofNat, Int.cast_sub] at hd ⊢
      linarith
    · refine ⟨(y, 2 * (w 0 - e7Lift y 0) + 1), ?_⟩
      apply Subtype.ext
      ext i
      change (e7Lift y i : ℝ) + ((2 * (w 0 - e7Lift y 0) + 1 : ℤ) : ℝ) / 2 = v.val i
      have hd := hdiff i
      rw [hv] at hd ⊢
      push_cast at hd ⊢
      linarith

def e8FibreEquiv : e7ProjectedSet × ℤ ≃ dPlusSet 8 :=
  Equiv.ofBijective e8FibreMap e8FibreMap_bijective

end PaperVerification.ColdSpots
end
end Source_E7Coordinates
-- END ORIGINAL PaperVerification.E7Coordinates


-- BEGIN ORIGINAL PaperVerification.E7Projection
section Source_E7Projection

-- original header: module
-- original header: public import PaperVerification.E7Coordinates
-- original header: public import PaperVerification.GaussianExtrema
-- original header: public import PaperVerification.LatticeGeometry
-- original header: public import Mathlib.Algebra.Ring.Int.Parity
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e7Gaussian (α : ℝ) (x : zeroSumSpace) : ℝ :=
  ∑' y : e7ProjectedSet, Real.exp (-α * sqDist y.val.val x.val)

def e7SquaredDepth (x : zeroSumSpace) : ℝ :=
  sInf ((fun y : zeroSumSpace ↦ sqDist x.val y.val) '' e7ProjectedSet)

def IsE7ColdSpot (α : ℝ) (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7Gaussian α x ≤ e7Gaussian α y

def IsE7DeepHole (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7SquaredDepth y ≤ e7SquaredDepth x

def e7Slice (x : zeroSumSpace) : Fin 8 → ℝ := fun i ↦ x i + 1 / 8

def e7FibreOffset (y : e7ProjectedSet) : ℝ := (∑ i, (e7Lift y i : ℝ)) / 4

lemma e7FibreOffset_half_integer (y : e7ProjectedSet) :
    ∃ l : ℤ, e7FibreOffset y = (l : ℝ) / 2 := by
  obtain ⟨l, hl⟩ := e7Lift_even y
  refine ⟨l, ?_⟩
  unfold e7FibreOffset
  have hc : (∑ i, (e7Lift y i : ℝ)) = (l : ℝ) + l := by exact_mod_cast hl
  rw [hc]
  ring

theorem sqDist_e8Fibre_slice (y : e7ProjectedSet) (k : ℤ) (x : zeroSumSpace) :
    sqDist (e8FibreMap (y, k)).val (e7Slice x) =
      sqDist y.val.val x.val + 2 * ((k : ℝ) + e7FibreOffset y - 1 / 4) ^ 2 := by
  have hy (i : Fin 8) : (e7Lift y i : ℝ) =
      y.val i + e7FibreOffset y / 2 := by
    have h := congrFun (congrArg Subtype.val (e7Lift_projects y)) i
    simp only [project8_apply, intVec] at h
    unfold e7FibreOffset
    linarith
  have hsum : (∑ i, (y.val i - x i)) = 0 := by
    rw [Finset.sum_sub_distrib, zeroSumSpace_sum, zeroSumSpace_sum, sub_self]
  unfold sqDist e8FibreMap e7Slice
  simp only [hy]
  have hterm (i : Fin 8) :
      (y.val i + e7FibreOffset y / 2 + (k : ℝ) / 2 - (x i + 1 / 8)) ^ 2 =
        (y.val i - x i) ^ 2 +
        (y.val i - x i) * ((k : ℝ) + e7FibreOffset y - 1 / 4) +
        ((k : ℝ) + e7FibreOffset y - 1 / 4) ^ 2 / 4 := by ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma gaussian_quarter_half_integer_shift (α : ℝ) (l : ℤ) :
    gaussian α (1 / 4 - (l : ℝ) / 2) = gaussian α (1 / 4) := by
  rcases Int.even_or_odd l with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [hq]
    push_cast
    rw [show (1 / 4 : ℝ) - ((q : ℝ) + q) / 2 = 1 / 4 + (-q : ℤ) by
      push_cast; ring, gaussian_int_period]
  · rw [hq]
    push_cast
    rw [show (1 / 4 : ℝ) - (2 * (q : ℝ) + 1) / 2 = -(1 / 4) + (-q : ℤ) by
      push_cast; ring, gaussian_int_period, gaussian_even]

lemma hasSum_e8_fibre {α : ℝ} (hα : 0 < α) (y : e7ProjectedSet) (x : zeroSumSpace) :
    HasSum (fun k : ℤ ↦ Real.exp (-α * sqDist (e8FibreMap (y, k)).val (e7Slice x)))
      (gaussian (2 * α) (1 / 4) * Real.exp (-α * sqDist y.val.val x.val)) := by
  have h2 : 0 < 2 * α := by positivity
  obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y
  have h := (hasSum_gaussian h2 (1 / 4 - e7FibreOffset y)).mul_right
    (Real.exp (-α * sqDist y.val.val x.val))
  rw [hl, gaussian_quarter_half_integer_shift] at h
  convert h using 1
  funext k
  rw [sqDist_e8Fibre_slice, hl, ← Real.exp_add]
  congr 1
  ring

theorem summable_setGaussian_dPlus {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) :
    Summable (fun z : dPlusSet n ↦ Real.exp (-α * sqDist z.val x)) := by
  let f : dPlusSet n → ℝ := fun z ↦ Real.exp (-α * sqDist z.val x)
  have hl : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inl z)))
      (dGaussian α x) := (summable_dGaussian hα x).hasSum
  have hr : HasSum (fun z : EvenTuple n ↦ f (dPlusTagEquiv hn (Sum.inr z)))
      (dGaussian α (fun i ↦ x i - 1 / 2)) := by
    change HasSum (fun z : EvenTuple n ↦
      Real.exp (-α * sqDist (fun i ↦ (z.val i : ℝ) + 1 / 2) x)) _
    simp only [sqDist_half_shift]
    exact (summable_dGaussian hα _).hasSum
  exact (((dPlusTagEquiv hn).hasSum_iff (f := f)).mp (hl.sum hr)).summable

/-- Equation (25): exact factorization of convergent Gaussian sums. -/
theorem e8_slice_gaussian_factorization {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    setGaussian (dPlusSet 8) α (e7Slice x) =
      gaussian (2 * α) (1 / 4) * e7Gaussian α x := by
  have hs := summable_setGaussian_dPlus (by decide : 0 < 8) hα (e7Slice x)
  have hsum := (e8FibreEquiv.hasSum_iff
    (f := fun z : dPlusSet 8 ↦ Real.exp (-α * sqDist z.val (e7Slice x)))).mpr hs.hasSum
  have houter := hsum.prod_fiberwise (fun y ↦ hasSum_e8_fibre hα y x)
  have heq := houter.tsum_eq
  rw [tsum_mul_left] at heq
  exact heq.symm

theorem summable_e7Gaussian {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    Summable (fun y : e7ProjectedSet ↦ Real.exp (-α * sqDist y.val.val x.val)) := by
  have hs := summable_setGaussian_dPlus (by decide : 0 < 8) hα (e7Slice x)
  have hsum := (e8FibreEquiv.hasSum_iff
    (f := fun z : dPlusSet 8 ↦ Real.exp (-α * sqDist z.val (e7Slice x)))).mpr hs.hasSum
  have houter := (hsum.prod_fiberwise (fun y ↦ hasSum_e8_fibre hα y x)).summable
  exact (summable_mul_left_iff (gaussian_pos (show 0 < 2 * α by positivity) _).ne').mp houter

lemma half_integer_quarter_distance_lower (k l : ℤ) :
    (1 / 8 : ℝ) ≤ 2 * ((k : ℝ) + (l : ℝ) / 2 - 1 / 4) ^ 2 := by
  rcases le_or_gt (2 * k + l) 0 with h | h
  · have hr : (2 : ℝ) * k + l ≤ 0 := by exact_mod_cast h
    have ht : (k : ℝ) + (l : ℝ) / 2 - 1 / 4 ≤ -(1 / 4 : ℝ) := by linarith
    nlinarith [sq_nonneg ((k : ℝ) + (l : ℝ) / 2)]
  · have hr : (1 : ℝ) ≤ 2 * k + l := by exact_mod_cast (show (1 : ℤ) ≤ 2 * k + l by omega)
    have ht : (1 / 4 : ℝ) ≤ (k : ℝ) + (l : ℝ) / 2 - 1 / 4 := by linarith
    nlinarith [sq_nonneg ((k : ℝ) + (l : ℝ) / 2 - 1 / 2)]

lemma exists_half_integer_quarter_distance_eq (l : ℤ) :
    ∃ k : ℤ, 2 * ((k : ℝ) + (l : ℝ) / 2 - 1 / 4) ^ 2 = 1 / 8 := by
  rcases Int.even_or_odd l with ⟨q, hq⟩ | ⟨q, hq⟩
  · refine ⟨-q, ?_⟩
    rw [hq]
    push_cast
    ring
  · refine ⟨-q, ?_⟩
    rw [hq]
    push_cast
    ring

lemma e7Projected_nonempty : e7ProjectedSet.Nonempty :=
  ⟨project8 (intVec 0), ⟨0, by simp, rfl⟩⟩

lemma e7SquaredDepth_le (x : zeroSumSpace) {y : zeroSumSpace} (hy : y ∈ e7ProjectedSet) :
    e7SquaredDepth x ≤ sqDist x.val y.val :=
  csInf_le ⟨0, by rintro r ⟨z, hz, rfl⟩; exact sqDist_nonneg _ _⟩ ⟨y, hy, rfl⟩

/-- The squared-distance identity is proved directly, independently of a
large-parameter asymptotic argument. -/
theorem e8_slice_depth_factorization (x : zeroSumSpace) :
    squaredDepth (dPlusSet 8) (e7Slice x) = e7SquaredDepth x + 1 / 8 := by
  apply le_antisymm
  · have hle : squaredDepth (dPlusSet 8) (e7Slice x) - 1 / 8 ≤ e7SquaredDepth x := by
      apply le_csInf (e7Projected_nonempty.image _)
      rintro d ⟨y, hy, rfl⟩
      let y' : e7ProjectedSet := ⟨y, hy⟩
      obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y'
      obtain ⟨k, hk⟩ := exists_half_integer_quarter_distance_eq l
      have h := squaredDepth_le (e7Slice x) (e8FibreMap (y', k)).property
      rw [sqDist_comm, sqDist_e8Fibre_slice, hl, hk, sqDist_comm] at h
      linarith
    linarith
  · apply le_csInf ((dPlusSet_nonempty 8).image _)
    rintro d ⟨v, hv, rfl⟩
    obtain ⟨⟨y, k⟩, heq⟩ := e8FibreMap_bijective.surjective ⟨v, hv⟩
    have heqv := congrArg Subtype.val heq
    change (e8FibreMap (y, k)).val = v at heqv
    change e7SquaredDepth x + 1 / 8 ≤ sqDist (e7Slice x) v
    rw [← heqv, sqDist_comm, sqDist_e8Fibre_slice]
    obtain ⟨l, hl⟩ := e7FibreOffset_half_integer y
    have hbase := e7SquaredDepth_le x y.property
    rw [sqDist_comm] at hbase
    rw [hl]
    linarith [half_integer_quarter_distance_lower k l]

theorem e7SquaredDepth_le_seven_eighths (x : zeroSumSpace) : e7SquaredDepth x ≤ 7 / 8 := by
  have h := squaredDepth_dPlus_le (n := 8) (by decide) (e7Slice x)
  rw [e8_slice_depth_factorization] at h
  norm_num at h
  linarith

end PaperVerification.ColdSpots
end
end Source_E7Projection
-- END ORIGINAL PaperVerification.E7Projection


-- BEGIN ORIGINAL PaperVerification.E7Transfer
section Source_E7Transfer

-- original header: module
-- original header: public import PaperVerification.E7Projection
-- original header: public import PaperVerification.ThetaRelations
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e8Axis : Fin 8 → ℝ := intVec (fun i ↦ if i = 0 then 1 else 0)

def e7Witness : zeroSumSpace := project8 e8Axis

lemma e8Axis_sum : (∑ i, e8Axis i) = 1 := by simp [e8Axis, intVec]

theorem e7Slice_witness : e7Slice e7Witness = e8Axis := by
  ext i
  simp only [e7Slice, e7Witness, project8_apply, e8Axis_sum]
  ring

theorem e8Axis_folded_hole : E8FoldedHole e8Axis := by
  apply Or.inl
  constructor
  · intro i
    simp only [foldedRadius, roundedInt, e8Axis, intVec, round_intCast, sub_self, abs_zero]
  · change ¬Even (∑ i, round ((if i = 0 then 1 else 0 : ℤ) : ℝ))
    simp only [round_intCast]
    have hs : (∑ i : Fin 8, (if i = 0 then 1 else 0 : ℤ)) = 1 := by simp
    rw [hs]
    decide

theorem e8Axis_depth : squaredDepth (dPlusSet 8) e8Axis = 1 :=
  (squaredDepth_E8_eq_one_iff e8Axis).mpr e8Axis_folded_hole

theorem e7Witness_depth : e7SquaredDepth e7Witness = 7 / 8 := by
  have h := e8_slice_depth_factorization e7Witness
  rw [e7Slice_witness, e8Axis_depth] at h
  linarith

/-- The squared covering radius is exactly 7/8, in the true hyperplane ambient space. -/
theorem e7_covering_radius :
    (∀ x, e7SquaredDepth x ≤ 7 / 8) ∧ ∃ x, e7SquaredDepth x = 7 / 8 :=
  ⟨e7SquaredDepth_le_seven_eighths, e7Witness, e7Witness_depth⟩

theorem isE7DeepHole_iff_depth (x : zeroSumSpace) :
    IsE7DeepHole x ↔ e7SquaredDepth x = 7 / 8 := by
  constructor
  · intro hx
    apply le_antisymm (e7SquaredDepth_le_seven_eighths x)
    simpa only [e7Witness_depth] using hx e7Witness
  · intro hx y
    rw [hx]
    exact e7SquaredDepth_le_seven_eighths y

theorem isDeepHole_slice_iff (x : zeroSumSpace) :
    IsDeepHole (dPlusSet 8) (e7Slice x) ↔ IsE7DeepHole x := by
  rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8),
    isE7DeepHole_iff_depth, e8_slice_depth_factorization]
  norm_num
  constructor <;> intro h <;> linarith

theorem dPlusGaussian_axis {α : ℝ} (hα : 0 < α) :
    dPlusGaussian α e8Axis = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by
  have hA1 : gaussian α 1 = gaussian α 0 := by simpa using gaussian_one_period α 0
  have hB1 : alternatingGaussian α 1 = -alternatingGaussian α 0 := by
    simpa using alternatingGaussian_antiperiod α 0
  have hdiag : thetaDiagonal α 0 = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by
    apply (thetaDiagonal_min_iff hα 0).mpr
    exact ⟨0, by norm_num⟩
  rw [← hdiag, dPlusGaussian_eq_product hα]
  norm_num [e8Axis, intVec, Fin.prod_univ_succ, hA1, hB1, thetaDiagonal,
    gaussian_even, alternatingGaussian_even, alternatingGaussian_half]
  ring

theorem e7Gaussian_witness {α : ℝ} (hα : 0 < α) :
    e7Gaussian α e7Witness =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) := by
  have h := e8_slice_gaussian_factorization hα e7Witness
  rw [e7Slice_witness, setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_axis hα] at h
  apply (eq_div_iff (gaussian_pos (show 0 < 2 * α by positivity) _).ne').mpr
  linarith

/-- Projection transfer with its only substantive input explicitly displayed:
the full E8 cold-spot/deep-hole equivalence at this parameter. -/
theorem e7_coldSpot_iff_deepHole_of_E8 {α : ℝ} (hα : 0 < α)
    (hE8 : ∀ v : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α v ↔ IsDeepHole (dPlusSet 8) v)
    (x : zeroSumSpace) : IsE7ColdSpot α x ↔ IsE7DeepHole x := by
  have hc : 0 < gaussian (2 * α) (1 / 4) := gaussian_pos (by positivity) _
  have haxis : IsColdSpot (dPlusSet 8) α e8Axis :=
    (hE8 e8Axis).mpr ((isDeepHole_E8_iff e8Axis).mpr e8Axis_folded_hole)
  constructor
  · intro hx
    apply (isDeepHole_slice_iff x).mp
    apply (hE8 (e7Slice x)).mp
    intro v
    have hle := mul_le_mul_of_nonneg_left (hx e7Witness) hc.le
    rw [← e8_slice_gaussian_factorization hα x,
      ← e8_slice_gaussian_factorization hα e7Witness, e7Slice_witness] at hle
    exact hle.trans (haxis v)
  · intro hx y
    have hglobal := (hE8 (e7Slice x)).mpr ((isDeepHole_slice_iff x).mpr hx)
    have h := hglobal (e7Slice y)
    rw [e8_slice_gaussian_factorization hα x, e8_slice_gaussian_factorization hα y] at h
    exact (mul_le_mul_iff_of_pos_left hc).mp h

theorem e7Gaussian_minimum_of_E8 {α : ℝ} (hα : 0 < α)
    (hE8 : ∀ v : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α v ↔ IsDeepHole (dPlusSet 8) v) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ≤
      e7Gaussian α x) ∧
    (∀ x, e7Gaussian α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ↔
        IsE7DeepHole x) := by
  have hwdeep := (isE7DeepHole_iff_depth e7Witness).mpr e7Witness_depth
  have hwcold := (e7_coldSpot_iff_deepHole_of_E8 hα hE8 e7Witness).mpr hwdeep
  have hbound : ∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 /
      gaussian (2 * α) (1 / 4) ≤ e7Gaussian α x := by
    intro x
    simpa only [e7Gaussian_witness hα] using hwcold x
  refine ⟨hbound, ?_⟩
  intro x
  constructor
  · intro heq
    apply (e7_coldSpot_iff_deepHole_of_E8 hα hE8 x).mp
    intro y
    rw [heq]
    exact hbound y
  · intro hx
    have hcold := (e7_coldSpot_iff_deepHole_of_E8 hα hE8 x).mpr hx
    apply le_antisymm _ (hbound x)
    simpa only [e7Gaussian_witness hα] using hcold e7Witness

end PaperVerification.ColdSpots
end
end Source_E7Transfer
-- END ORIGINAL PaperVerification.E7Transfer


-- BEGIN ORIGINAL PaperVerification.E7Theorems
section Source_E7Theorems

-- original header: module
-- original header: public import PaperVerification.E7Transfer
-- original header: public import PaperVerification.E8Theorems
-- original header: @[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

/-- The E7* part of Theorem 1.1, in its true orthogonal-complement ambient space.
`e7DualSet_eq_projected` proves that the summed lattice is exactly the integral dual. -/
theorem coldSpot_E7_dual_iff_deepHole {α : ℝ} (hα : 0 < α) (x : zeroSumSpace) :
    IsE7ColdSpot α x ↔ IsE7DeepHole x :=
  e7_coldSpot_iff_deepHole_of_E8 hα (coldSpot_E8_iff_deepHole hα) x

/-- The full analytic minimum and equality claim in Theorem 6.2. -/
theorem e7Dual_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ≤
      e7Gaussian α x) ∧
    (∀ x, e7Gaussian α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ↔ IsE7DeepHole x) :=
  e7Gaussian_minimum_of_E8 hα (coldSpot_E8_iff_deepHole hα)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_E7_dual_iff_deepHole
#print axioms PaperVerification.ColdSpots.e7Dual_gaussian_minimum
end
end Source_E7Theorems
-- END ORIGINAL PaperVerification.E7Theorems


-- BEGIN ORIGINAL PaperVerification.BWCode
section Source_BWCode

-- original header: module
-- original header: public import Mathlib.Data.ZMod.Basic
-- original header: public import Mathlib.Data.Fin.Tuple.Basic
-- original header: public import Mathlib.Algebra.BigOperators.Fin
-- original header: public import Mathlib.Tactic.FinCases
-- original header: public import Mathlib.Tactic.NormNum
-- original header: public import Mathlib.Tactic.Ring
-- original header: public import Mathlib.Tactic.LinearCombination
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section
/-! # The binary affine code in the Barnes–Wall construction

All code membership is literal membership in RM(1,3), the evaluations of affine
functions on F₂³.  Finite identities are proved by the kernel's ordinary decision
procedure, without `native_decide` or externally trusted computation.  These are
supporting finite algebra lemmas, not finite tests of the lattice theorem.
-/

namespace PaperVerification.ColdSpots

open scoped BigOperators

set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev Binary := ZMod 2
abbrev AffineCoefficients3 := Fin 4 → Binary
abbrev LinearCoefficients3 := Fin 3 → Binary
abbrev BinaryWord8 := Fin 8 → Binary

@[simp] theorem binary_two_eq_zero : (2 : Binary) = 0 := by decide

@[simp] theorem binary_four_eq_zero : (4 : Binary) = 0 := by decide

@[simp] theorem binary_one_val : (1 : Binary).val = 1 := by decide

/-- Binary expansion of the coordinate index, with the last coordinate paired. -/
def binaryDigit (i : Fin 8) (j : Fin 3) : Binary := ((i.val / 2 ^ j.val) % 2 : ℕ)

/-- Evaluation of a literal affine function on F₂³. -/
def affineWord3 (a : AffineCoefficients3) : BinaryWord8 :=
  fun i => a 3 + ∑ j : Fin 3, a j.castSucc * binaryDigit i j

def linearWord3 (a : LinearCoefficients3) : BinaryWord8 :=
  fun i => ∑ j : Fin 3, a j * binaryDigit i j

/-- The first-order Reed–Muller code RM(1,3). -/
def InRM3 (c : BinaryWord8) : Prop := ∃ a : AffineCoefficients3, c = affineWord3 a

instance (c : BinaryWord8) : Decidable (InRM3 c) := by
  unfold InRM3
  infer_instance

/-- The four independent equations defining the same affine code in pair order. -/
def PairCodeCondition (c : BinaryWord8) : Prop :=
  c 0 + c 1 = c 2 + c 3 ∧ c 0 + c 1 = c 4 + c 5 ∧
  c 0 + c 1 = c 6 + c 7 ∧ c 0 + c 2 + c 4 + c 6 = 0

instance (c : BinaryWord8) : Decidable (PairCodeCondition c) := by
  unfold PairCodeCondition
  infer_instance

theorem inRM3_iff_pairCondition : ∀ c : BinaryWord8, InRM3 c ↔ PairCodeCondition c := by
  decide

theorem affineWord3_injective : Function.Injective affineWord3 := by decide

theorem linearWord3_injective : Function.Injective linearWord3 := by decide

theorem linearWord3_zero_coordinate (a : LinearCoefficients3) : linearWord3 a 0 = 0 := by
  simp [linearWord3, binaryDigit]

theorem linearWord3_mem (a : LinearCoefficients3) : InRM3 (linearWord3 a) := by
  refine ⟨Fin.snoc a 0, ?_⟩
  funext i
  unfold linearWord3 affineWord3
  rw [show (3 : Fin 4) = Fin.last 3 by decide]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, zero_add]

theorem inRM3_zero : InRM3 (fun _ => 0) := by
  refine ⟨fun _ => 0, ?_⟩
  funext i
  simp only [affineWord3, zero_mul, Finset.sum_const_zero, add_zero]

theorem inRM3_one : InRM3 (fun _ => 1) := by
  exact (inRM3_iff_pairCondition _).mpr (by decide)

theorem inRM3_add {c d : BinaryWord8} (hc : InRM3 c) (hd : InRM3 d) :
    InRM3 (fun i => c i + d i) := by
  rcases hc with ⟨a, rfl⟩
  rcases hd with ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  funext i
  simp only [affineWord3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem inRM3_neg {c : BinaryWord8} (hc : InRM3 c) : InRM3 (fun i => -c i) := by
  rcases hc with ⟨a, rfl⟩
  refine ⟨-a, ?_⟩
  funext i
  simp only [affineWord3, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem inRM3_sub {c d : BinaryWord8} (hc : InRM3 c) (hd : InRM3 d) :
    InRM3 (fun i => c i - d i) := by
  simpa only [sub_eq_add_neg] using inRM3_add hc (inRM3_neg hd)

def binaryWeight (c : BinaryWord8) : ℕ := (Finset.univ.filter fun i => c i = 1).card

/-- The exact weight enumerator support of RM(1,3). -/
theorem inRM3_weight : ∀ c : BinaryWord8, InRM3 c →
    binaryWeight c = 0 ∨ binaryWeight c = 4 ∨ binaryWeight c = 8 := by decide

theorem inRM3_even_weight {c : BinaryWord8} (hc : InRM3 c) : Even (binaryWeight c) := by
  rcases inRM3_weight c hc with h | h | h <;> rw [h] <;> decide

theorem inRM3_weight_div_four {c : BinaryWord8} (hc : InRM3 c) : 4 ∣ binaryWeight c := by
  rcases inRM3_weight c hc with h | h | h <;> rw [h] <;> decide

/-- The complementary-pair representatives used for M/E8. -/
theorem inRM3_linear_or_complement : ∀ c : BinaryWord8, InRM3 c →
    ∃ a : LinearCoefficients3, c = linearWord3 a ∨ c = fun i => 1 + linearWord3 a i := by
  decide

theorem linearWord3_weight : ∀ a : LinearCoefficients3,
    binaryWeight (linearWord3 a) = 0 ∨ binaryWeight (linearWord3 a) = 4 := by decide

/-- The code's binary sum agrees with the parity of its number of ones. -/
theorem binary_sum_eq_weight : ∀ c : BinaryWord8,
    (∑ i, c i) = (binaryWeight c : Binary) := by decide

theorem binary_weight_le (c : BinaryWord8) : binaryWeight c ≤ 8 := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem binary_weight_zero_iff : ∀ c : BinaryWord8,
    binaryWeight c = 0 ↔ ∀ i, c i = 0 := by decide

theorem binary_weight_eight_iff : ∀ c : BinaryWord8,
    binaryWeight c = 8 ↔ ∀ i, c i = 1 := by decide

/-- Distances between an eligible four-half word and the code are exactly 2,4,6. -/
theorem eligible_word_difference_weights {c d : BinaryWord8}
    (hc : binaryWeight c = 4) (hnc : ¬InRM3 c) (hd : InRM3 d) :
      binaryWeight (fun i => c i - d i) = 2 ∨
      binaryWeight (fun i => c i - d i) = 4 ∨
      binaryWeight (fun i => c i - d i) = 6 := by
  let e : BinaryWord8 := fun i => c i - d i
  have he : Even (binaryWeight e) := by
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← binary_sum_eq_weight]
    change (∑ i, (c i - d i)) = 0
    rw [Finset.sum_sub_distrib, binary_sum_eq_weight, binary_sum_eq_weight, hc]
    have hed := ZMod.natCast_eq_zero_iff_even.mpr (inRM3_even_weight hd)
    simpa only [hed, sub_zero, Nat.cast_ofNat] using binary_four_eq_zero
  have hn0 : binaryWeight e ≠ 0 := by
    intro h
    have he0 := (binary_weight_zero_iff e).mp h
    have hcd : c = d := by funext i; exact sub_eq_zero.mp (he0 i)
    exact hnc (hcd.symm ▸ hd)
  have hn8 : binaryWeight e ≠ 8 := by
    intro h
    have he1 := (binary_weight_eight_iff e).mp h
    have hcd : c = fun i => d i + 1 := by
      funext i
      have hi : c i - d i = 1 := he1 i
      linear_combination hi
    rw [hcd] at hnc
    exact hnc (inRM3_add hd inRM3_one)
  obtain ⟨k, hk⟩ := he
  have hle := binary_weight_le e
  change binaryWeight e = 2 ∨ binaryWeight e = 4 ∨ binaryWeight e = 6
  omega

theorem binary_eq_zero_or_one : ∀ c : Binary, c = 0 ∨ c = 1 := by decide

theorem binary_val_zero_or_one (c : Binary) : c.val = 0 ∨ c.val = 1 := by
  have h := c.val_lt
  omega

theorem binary_val_cast (c : Binary) : ((c.val : ℤ) : Binary) = c := by
  simp

theorem sum_binary_val (c : BinaryWord8) :
    (∑ i, (c i).val) = binaryWeight c := by
  unfold binaryWeight
  have hi (i : Fin 8) : (c i).val = if c i = 1 then 1 else 0 := by
    rcases binary_eq_zero_or_one (c i) with h | h <;> norm_num [h]
  simp only [hi]
  simp

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.inRM3_iff_pairCondition
#print axioms PaperVerification.ColdSpots.eligible_word_difference_weights
end Source_BWCode
-- END ORIGINAL PaperVerification.BWCode


-- BEGIN ORIGINAL PaperVerification.LatticeTranslations
section Source_LatticeTranslations

-- original header: module
-- original header: public import PaperVerification.LatticeGeometry
-- original header: public import PaperVerification.DnGaussian
-- original header: public import Mathlib.Algebra.Group.Subgroup.Basic
-- original header: @[expose] public section
/-! # Actual translation symmetries and nearest points

The distance and Gaussian symmetries are proved for the underlying real point
sets.  The nearest-point result is an exact attainment theorem, obtained from
coordinate rounding and parity repair, rather than an assumed lattice compactness
principle.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

theorem intVec_add (z w : Fin n → ℤ) : intVec (z + w) = intVec z + intVec w := by
  funext i
  simp [intVec]

theorem dPlusSet_add (heven : Even n) {x y : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) (hy : y ∈ dPlusSet n) : x + y ∈ dPlusSet n := by
  rcases hx with ⟨z, hz, rfl | rfl⟩ <;> rcases hy with ⟨w, hw, rfl | rfl⟩
  · refine ⟨z + w, ?_, Or.inl (intVec_add z w).symm⟩
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
  · refine ⟨z + w, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
    · funext i
      simp [intVec] <;> ring
  · refine ⟨z + w, ?_, Or.inr ?_⟩
    · simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
    · funext i
      simp [intVec] <;> ring
  · refine ⟨fun i => z i + w i + 1, ?_, Or.inl ?_⟩
    · have hn : Even (n : ℤ) := (Int.even_coe_nat n).mpr heven
      simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using (hz.add hw).add hn
    · funext i
      simp only [Pi.add_apply, intVec, Int.cast_add, Int.cast_one]
      ring

theorem dPlusSet_neg (heven : Even n) {x : Fin n → ℝ} (hx : x ∈ dPlusSet n) :
    -x ∈ dPlusSet n := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · refine ⟨-z, ?_, Or.inl ?_⟩
    · simpa only [Pi.neg_apply, Finset.sum_neg_distrib] using hz.neg
    · funext i
      simp [intVec]
  · refine ⟨fun i => -z i - 1, ?_, Or.inr ?_⟩
    · have hn : Even (n : ℤ) := (Int.even_coe_nat n).mpr heven
      simpa only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hz.neg.sub hn
    · funext i
      simp only [Pi.neg_apply, Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring

theorem dPlusSet_sub (heven : Even n) {x y : Fin n → ℝ}
    (hx : x ∈ dPlusSet n) (hy : y ∈ dPlusSet n) : x - y ∈ dPlusSet n := by
  simpa only [sub_eq_add_neg] using dPlusSet_add heven hx (dPlusSet_neg heven hy)

def dPlusAddSubgroup (n : ℕ) (heven : Even n) : AddSubgroup (Fin n → ℝ) where
  carrier := dPlusSet n
  zero_mem' := zero_mem_dPlusSet n
  add_mem' := dPlusSet_add heven
  neg_mem' := dPlusSet_neg heven

theorem sqDist_add_add (x y g : Fin n → ℝ) : sqDist (x + g) (y + g) = sqDist x y := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem sqDist_add_left (x y g : Fin n → ℝ) : sqDist (x + g) y = sqDist x (y - g) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem sqDist_sub_left (x y g : Fin n → ℝ) : sqDist (x - g) y = sqDist x (y + g) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem squaredDepth_add_of_subgroup (L : AddSubgroup (Fin n → ℝ))
    (x g : Fin n → ℝ) (hg : g ∈ L) : squaredDepth (L : Set _) (x + g) = squaredDepth (L : Set _) x := by
  unfold squaredDepth
  congr 1
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - g, L.sub_mem hz hg, ?_⟩
    exact (sqDist_add_left x z g).symm
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + g, L.add_mem hz hg, ?_⟩
    exact sqDist_add_add x z g

theorem setGaussian_add_of_subgroup (L : AddSubgroup (Fin n → ℝ))
    (α : ℝ) (x g : Fin n → ℝ) (hg : g ∈ L) :
    setGaussian (L : Set _) α (x + g) = setGaussian (L : Set _) α x := by
  let e : L ≃ L := Equiv.addRight ⟨g, hg⟩
  let f : L → ℝ := fun z => Real.exp (-α * sqDist z.val (x + g))
  calc
    _ = ∑' z : L, f (e z) := (e.tsum_eq f).symm
    _ = _ := by
      apply tsum_congr
      intro z
      change Real.exp (-α * sqDist (z.val + g) (x + g)) = Real.exp (-α * sqDist z.val x)
      rw [sqDist_add_add]

theorem exists_integerRepairCost_witness (x : Fin n → ℝ) (j : Fin n) :
    ∃ z ∈ dPlusSet n, sqDist x z ≤ integerRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, roundedInt x i)
  · refine ⟨intVec (roundedInt x), ⟨roundedInt x, he, Or.inl rfl⟩, ?_⟩
    rw [sqDist_roundedInt]
    simp [integerRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_integer_bound x j
    refine ⟨intVec z, ⟨z, hz, Or.inl rfl⟩, ?_⟩
    simpa [sqDist, intVec, integerRepairCost, integerBaseCost, he,
      sub_eq_add_neg, add_assoc] using hdist

theorem exists_halfRepairCost_witness (x : Fin n → ℝ) (j : Fin n) :
    ∃ z ∈ dPlusSet n, sqDist x z ≤ halfRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, halfRoundedInt x i)
  · refine ⟨(fun i => (halfRoundedInt x i : ℝ) + 1 / 2),
      ⟨halfRoundedInt x, he, Or.inr rfl⟩, ?_⟩
    rw [sqDist_halfRoundedInt]
    simp [halfRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_half_integer_bound x j
    refine ⟨(fun i => (z i : ℝ) + 1 / 2), ⟨z, hz, Or.inr rfl⟩, ?_⟩
    simpa [sqDist, halfRepairCost, halfBaseCost, he] using hdist

/-- The nearest E8 point exists for every real vector.  The general theorem
holds for every positive dimension in the coordinate realization D_n^+. -/
theorem exists_nearest_dPlus (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ z ∈ dPlusSet n, sqDist x z = squaredDepth (dPlusSet n) x := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have heq := squaredDepth_dPlus_eq x lo hi (fun i => hlo i (Finset.mem_univ _))
    (fun i => hhi i (Finset.mem_univ _))
  rcases le_total (integerRepairCost x (foldedRadius x hi))
    (halfRepairCost x (foldedRadius x lo)) with h | h
  · rw [min_eq_left h] at heq
    obtain ⟨z, hz, hdist⟩ := exists_integerRepairCost_witness x hi
    exact ⟨z, hz, le_antisymm (hdist.trans_eq heq.symm) (squaredDepth_le x hz)⟩
  · rw [min_eq_right h] at heq
    obtain ⟨z, hz, hdist⟩ := exists_halfRepairCost_witness x lo
    exact ⟨z, hz, le_antisymm (hdist.trans_eq heq.symm) (squaredDepth_le x hz)⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.exists_nearest_dPlus
#print axioms PaperVerification.ColdSpots.setGaussian_add_of_subgroup
end
end Source_LatticeTranslations
-- END ORIGINAL PaperVerification.LatticeTranslations


-- BEGIN ORIGINAL PaperVerification.BWCoordinates
section Source_BWCoordinates

-- original header: module
-- original header: public import PaperVerification.BWCode
-- original header: public import PaperVerification.LatticeTranslations
-- original header: public import Mathlib.Tactic.LinearCombination
-- original header: @[expose] public section
/-! # The exact E8 similarity behind the Barnes–Wall glue

The lattice M is defined by doubled integer coordinates whose residues belong to
RM(1,3).  The half-Hadamard map is proved to carry the actual E8 point set onto M;
its squared scale is one half.  No classification or covering result for M is
assumed in this identification.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

set_option maxRecDepth 65536

/-- The unnormalized pairwise Hadamard transformation. -/
def pairButterfly {R : Type*} [AddGroup R] (x : Fin 8 → R) : Fin 8 → R :=
  ![x 0 + x 1, x 0 - x 1, x 2 + x 3, x 2 - x 3,
    x 4 + x 5, x 4 - x 5, x 6 + x 7, x 6 - x 7]

/-- The similarity with squared norm factor one half. -/
def halfHadamard (x : Fin 8 → ℝ) : Fin 8 → ℝ := fun i => pairButterfly x i / 2

def evenPositionWord : Fin 8 → ℤ := ![1, 0, 1, 0, 1, 0, 1, 0]

def bwMSet : Set (Fin 8 → ℝ) :=
  {x | ∃ z : Fin 8 → ℤ, InRM3 (fun i => (z i : Binary)) ∧
    x = fun i => (z i : ℝ) / 2}

theorem pairButterfly_intCast (z : Fin 8 → ℤ) (i : Fin 8) :
    ((pairButterfly z i : ℤ) : ℝ) = pairButterfly (intVec z) i := by
  fin_cases i <;> simp [pairButterfly, intVec]

theorem pairButterfly_binaryCast (z : Fin 8 → ℤ) (i : Fin 8) :
    ((pairButterfly z i : ℤ) : Binary) = pairButterfly (fun i => (z i : Binary)) i := by
  fin_cases i <;> simp [pairButterfly]

theorem pairButterfly_sum (z : Fin 8 → ℤ) :
    (∑ i, pairButterfly z i) = 2 * (z 0 + z 2 + z 4 + z 6) := by
  simp [pairButterfly, Fin.sum_univ_succ]
  ring

theorem halfHadamard_add (x y : Fin 8 → ℝ) :
    halfHadamard (x + y) = halfHadamard x + halfHadamard y := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_sub (x y : Fin 8 → ℝ) :
    halfHadamard (x - y) = halfHadamard x - halfHadamard y := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_double_inverse (x : Fin 8 → ℝ) :
    halfHadamard (fun i => 2 * halfHadamard x i) = x := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem double_halfHadamard_inverse (x : Fin 8 → ℝ) :
    (fun i => 2 * halfHadamard (halfHadamard x) i) = x := by
  funext i
  fin_cases i <;> simp [halfHadamard, pairButterfly] <;> ring

theorem halfHadamard_injective : Function.Injective halfHadamard := by
  intro x y h
  calc
    x = (fun i => 2 * halfHadamard (halfHadamard x) i) := (double_halfHadamard_inverse x).symm
    _ = (fun i => 2 * halfHadamard (halfHadamard y) i) := by rw [h]
    _ = y := double_halfHadamard_inverse y

theorem sqDist_halfHadamard (x y : Fin 8 → ℝ) :
    sqDist (halfHadamard x) (halfHadamard y) = sqDist x y / 2 := by
  simp [sqDist, halfHadamard, pairButterfly, Fin.sum_univ_succ]
  ring

theorem bwMSet_zero : (0 : Fin 8 → ℝ) ∈ bwMSet := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [Pi.zero_apply, Int.cast_zero] using inRM3_zero
  · funext i
    simp

theorem bwMSet_add {x y : Fin 8 → ℝ} (hx : x ∈ bwMSet) (hy : y ∈ bwMSet) :
    x + y ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl⟩
  rcases hy with ⟨w, hw, rfl⟩
  refine ⟨z + w, ?_, ?_⟩
  · simpa only [Pi.add_apply, Int.cast_add] using inRM3_add hz hw
  · funext i
    simp only [Pi.add_apply, Int.cast_add]
    ring

theorem bwMSet_neg {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) : -x ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl⟩
  refine ⟨-z, ?_, ?_⟩
  · simpa only [Pi.neg_apply, Int.cast_neg] using inRM3_neg hz
  · funext i
    simp only [Pi.neg_apply, Int.cast_neg]
    ring

def bwMAddSubgroup : AddSubgroup (Fin 8 → ℝ) where
  carrier := bwMSet
  zero_mem' := bwMSet_zero
  add_mem' := bwMSet_add
  neg_mem' := bwMSet_neg

theorem intVec_mem_bwM (z : Fin 8 → ℤ) : intVec z ∈ bwMSet := by
  refine ⟨fun i => 2 * z i, ?_, ?_⟩
  · simpa using (inRM3_zero : InRM3 (fun _ : Fin 8 => (0 : Binary)))
  · funext i
    simp [intVec]

theorem dPlusSet_subset_bwM : dPlusSet 8 ⊆ bwMSet := by
  rintro x ⟨z, hz, rfl | rfl⟩
  · exact intVec_mem_bwM z
  · refine ⟨fun i => 2 * z i + 1, ?_, ?_⟩
    · simpa using (inRM3_one : InRM3 (fun _ : Fin 8 => (1 : Binary)))
    · funext i
      push_cast
      ring

/-- Pairwise parity conditions of a butterfly are constant in all eight slots. -/
theorem binary_pairButterfly_common : ∀ c : BinaryWord8, PairCodeCondition c →
    ∀ i, pairButterfly c i = c 0 + c 1 := by decide

set_option maxHeartbeats 0 in
theorem binary_pairButterfly_code : ∀ c : BinaryWord8, (∑ i, c i) = 0 →
    PairCodeCondition (pairButterfly c) := by decide

theorem evenPositionWord_inRM3 : InRM3 (fun i => (evenPositionWord i : Binary)) := by decide

theorem butterfly_inRM3_of_even_sum (z : Fin 8 → ℤ) (hz : Even (∑ i, z i)) :
    InRM3 (fun i => ((pairButterfly z i : ℤ) : Binary)) := by
  apply (inRM3_iff_pairCondition _).mpr
  have hsum : (∑ i, (z i : Binary)) = 0 := by
    rw [← Int.cast_sum]
    exact hz.intCast_zmod_two
  have hmap : (fun i => ((pairButterfly z i : ℤ) : Binary)) =
      pairButterfly (fun i => (z i : Binary)) := funext (pairButterfly_binaryCast z)
  rw [hmap]
  exact binary_pairButterfly_code _ hsum

theorem halfHadamard_mem_bwM {x : Fin 8 → ℝ} (hx : x ∈ dPlusSet 8) :
    halfHadamard x ∈ bwMSet := by
  rcases hx with ⟨z, hz, rfl | rfl⟩
  · refine ⟨pairButterfly z, butterfly_inRM3_of_even_sum z hz, ?_⟩
    funext i
    simp only [halfHadamard, pairButterfly_intCast]
  · refine ⟨fun i => pairButterfly z i + evenPositionWord i, ?_, ?_⟩
    · simpa only [Int.cast_add] using
        inRM3_add (butterfly_inRM3_of_even_sum z hz) evenPositionWord_inRM3
    · funext i
      fin_cases i <;> simp [halfHadamard, pairButterfly, evenPositionWord] <;> push_cast <;> ring

/-- Inverse inclusion, proved by reconstructing actual even-sum integer coordinates. -/
theorem double_halfHadamard_mem_e8 {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) :
    (fun i => 2 * halfHadamard x i) ∈ dPlusSet 8 := by
  rcases hx with ⟨w, hw, rfl⟩
  let τ : ℤ := ((w 0 : Binary) + (w 1 : Binary)).val
  have hτ : τ = 0 ∨ τ = 1 := by
    have h := binary_val_zero_or_one ((w 0 : Binary) + (w 1 : Binary))
    rcases h with h | h
    · left
      change (((w 0 : Binary) + (w 1 : Binary)).val : ℤ) = 0
      rw [h]
      rfl
    · right
      change (((w 0 : Binary) + (w 1 : Binary)).val : ℤ) = 1
      rw [h]
      rfl
  have hτcast : (τ : Binary) = (w 0 : Binary) + (w 1 : Binary) := binary_val_cast _
  have hcommon (i : Fin 8) : Even (pairButterfly w i - τ) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [Int.cast_sub, pairButterfly_binaryCast, hτcast,
      binary_pairButterfly_common _ ((inRM3_iff_pairCondition _).mp hw) i, sub_self]
  let z : Fin 8 → ℤ := fun i => (pairButterfly w i - τ) / 2
  have hzcoord (i : Fin 8) : 2 * z i = pairButterfly w i - τ := by
    exact Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hcommon i))
  have hsum : (∑ i, z i) = w 0 + w 2 + w 4 + w 6 - 4 * τ := by
    have h := congrArg (fun f : Fin 8 → ℤ => ∑ i, f i) (funext hzcoord)
    change (∑ i, 2 * z i) = ∑ i, (pairButterfly w i - τ) at h
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, pairButterfly_sum] at h
    simp only [
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    omega
  have he : Even (w 0 + w 2 + w 4 + w 6) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    simpa only [Int.cast_add] using ((inRM3_iff_pairCondition _).mp hw).2.2.2
  have hz : Even (∑ i, z i) := by
    rw [hsum]
    exact he.sub (show Even (4 * τ) from ⟨2 * τ, by ring⟩)
  have hreal (i : Fin 8) : 2 * halfHadamard (fun i => (w i : ℝ) / 2) i =
      (z i : ℝ) + (τ : ℝ) / 2 := by
    have hi : 2 * (z i : ℝ) = ((pairButterfly w i : ℤ) : ℝ) - (τ : ℝ) := by exact_mod_cast hzcoord i
    have hb : 2 * halfHadamard (fun i => (w i : ℝ) / 2) i = ((pairButterfly w i : ℤ) : ℝ) / 2 := by
      fin_cases i <;> simp [halfHadamard, pairButterfly] <;> push_cast <;> ring
    rw [hb]
    linarith
  refine ⟨z, hz, ?_⟩
  rcases hτ with h | h
  · left
    funext i
    simpa only [h, Int.cast_zero, zero_div, add_zero, intVec] using hreal i
  · right
    funext i
    simpa only [h, Int.cast_one] using hreal i

/-- Exact similarity, as equality of subsets of ordinary R⁸. -/
theorem bwMSet_eq_halfHadamard_image : bwMSet = halfHadamard '' dPlusSet 8 := by
  ext x
  constructor
  · intro hx
    exact ⟨(fun i => 2 * halfHadamard x i), double_halfHadamard_mem_e8 hx,
      halfHadamard_double_inverse x⟩
  · rintro ⟨y, hy, rfl⟩
    exact halfHadamard_mem_bwM hy

def e8ToMEquiv : dPlusSet 8 ≃ bwMSet :=
  Equiv.ofBijective (fun x => ⟨halfHadamard x.val, halfHadamard_mem_bwM x.property⟩)
    ⟨fun x y h => Subtype.ext (halfHadamard_injective (congrArg Subtype.val h)), by
      intro x
      refine ⟨⟨(fun i => 2 * halfHadamard x.val i), double_halfHadamard_mem_e8 x.property⟩, ?_⟩
      exact Subtype.ext (halfHadamard_double_inverse x.val)⟩

theorem sqDist_bwM_correspondence (x y : Fin 8 → ℝ) :
    sqDist x (halfHadamard y) = sqDist (fun i => 2 * halfHadamard x i) y / 2 := by
  simpa only [halfHadamard_double_inverse] using
    sqDist_halfHadamard (fun i => 2 * halfHadamard x i) y

/-- Exact nearest-point distance under the similarity. -/
theorem squaredDepth_bwM (x : Fin 8 → ℝ) :
    squaredDepth bwMSet x = squaredDepth (dPlusSet 8) (fun i => 2 * halfHadamard x i) / 2 := by
  obtain ⟨z, hz, hdist⟩ := exists_nearest_dPlus (by decide : 0 < 8)
    (fun i => 2 * halfHadamard x i)
  apply le_antisymm
  · calc
      _ ≤ sqDist x (halfHadamard z) := squaredDepth_le x (halfHadamard_mem_bwM hz)
      _ = _ := by rw [sqDist_bwM_correspondence, hdist]
  · apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist x z))
    rintro r ⟨v, hv, rfl⟩
    rw [bwMSet_eq_halfHadamard_image] at hv
    rcases hv with ⟨y, hy, rfl⟩
    change squaredDepth (dPlusSet 8) (fun i => 2 * halfHadamard x i) / 2 ≤
      sqDist x (halfHadamard y)
    rw [sqDist_bwM_correspondence]
    exact div_le_div_of_nonneg_right (squaredDepth_le _ hy) (by norm_num)

theorem squaredDepth_bwM_le (x : Fin 8 → ℝ) : squaredDepth bwMSet x ≤ 1 / 2 := by
  rw [squaredDepth_bwM]
  have h := squaredDepth_dPlus_le (by decide : 8 ≤ 8) (fun i => 2 * halfHadamard x i)
  norm_num at h
  linarith

/-- The Gaussian of the actual point set transforms with parameter α/2. -/
theorem setGaussian_bwM (α : ℝ) (x : Fin 8 → ℝ) :
    setGaussian bwMSet α x = setGaussian (dPlusSet 8) (α / 2)
      (fun i => 2 * halfHadamard x i) := by
  rw [setGaussian, ← e8ToMEquiv.tsum_eq]
  apply tsum_congr
  intro z
  change Real.exp (-α * sqDist (halfHadamard z.val) x) = _
  rw [sqDist_comm, sqDist_bwM_correspondence, sqDist_comm]
  congr 1
  ring

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwMSet_eq_halfHadamard_image
#print axioms PaperVerification.ColdSpots.squaredDepth_bwM
#print axioms PaperVerification.ColdSpots.setGaussian_bwM
end
end Source_BWCoordinates
-- END ORIGINAL PaperVerification.BWCoordinates


-- BEGIN ORIGINAL PaperVerification.LatticeE8Families
section Source_LatticeE8Families

-- original header: module
-- original header: public import PaperVerification.LatticeGeometry
-- original header: public import Mathlib.Algebra.Ring.Int.Parity
-- original header: @[expose] public section
/-! # The literal coordinate families of the E8 deep holes

This module identifies the complete folded-coordinate result with the three
families printed in Proposition 3.4.  In particular, the quarter-grid family
retains both its odd integer-sum condition and its even number of minus signs.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

def negativeSignCount (ε : Fin n → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ε i = -1).card

/-- The exceptional quarter-coordinate family with its literal sign parity. -/
def E8QuarterFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ m ε : Fin 8 → ℤ, Odd (∑ i, m i) ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
    Even (negativeSignCount ε) ∧ ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4

/-- The first coordinate vector in the Euclidean realization of E8. -/
def e8FirstVector : Fin 8 → ℝ := fun i => if i = 0 then 1 else 0

/-- The literal translate `e₁ + E8`. -/
def E8FirstFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ y ∈ dPlusSet 8, x = e8FirstVector + y

/-- An elementary intermediate description of the same odd coset. -/
def E8OddCoset (x : Fin 8 → ℝ) : Prop :=
  ∃ z : Fin 8 → ℤ, Odd (∑ i, z i) ∧
    (x = intVec z ∨ x = fun i => (z i : ℝ) + 1 / 2)

theorem roundedInt_intVec (z : Fin n → ℤ) : roundedInt (intVec z) = z := by
  funext i
  simp [roundedInt, intVec]

theorem halfRoundedInt_halfVec (z : Fin n → ℤ) :
    halfRoundedInt (fun i => (z i : ℝ) + 1 / 2) = z := by
  have hh : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
  funext i
  have hround : roundedInt (fun i => (z i : ℝ) + 1 / 2) i = z i + 1 := by
    simp only [roundedInt, round_intCast_add, hh]
  have hneg : ¬(0 : ℝ) ≤ (z i : ℝ) + 1 / 2 - ((z i + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  simp only [halfRoundedInt, hround, if_neg hneg]
  ring

theorem e8OddCoset_iff_folded_endpoints (x : Fin 8 → ℝ) :
    E8OddCoset x ↔
      ((∀ i, foldedRadius x i = 0) ∧ ¬Even (∑ i, roundedInt x i)) ∨
      ((∀ i, foldedRadius x i = 1 / 2) ∧ ¬Even (∑ i, halfRoundedInt x i)) := by
  constructor
  · rintro ⟨z, hz, hx | hx⟩
    · subst x
      refine Or.inl ⟨?_, ?_⟩
      · intro i
        exact (foldedRadius_eq_zero_iff _ i).mpr ⟨z i, rfl⟩
      · rw [roundedInt_intVec]
        exact Int.not_even_iff_odd.mpr hz
    · subst x
      refine Or.inr ⟨?_, ?_⟩
      · intro i
        exact (foldedRadius_eq_half_iff _ i).mpr ⟨z i, rfl⟩
      · rw [halfRoundedInt_halfVec]
        exact Int.not_even_iff_odd.mpr hz
  · rintro (⟨hr, hp⟩ | ⟨hr, hp⟩)
    · refine ⟨roundedInt x, Int.not_even_iff_odd.mp hp, Or.inl ?_⟩
      funext i
      exact sub_eq_zero.mp (abs_eq_zero.mp (hr i))
    · refine ⟨halfRoundedInt x, Int.not_even_iff_odd.mp hp, Or.inr ?_⟩
      funext i
      have h := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp h)

theorem e8FirstFamily_iff_oddCoset (x : Fin 8 → ℝ) :
    E8FirstFamily x ↔ E8OddCoset x := by
  classical
  constructor
  · rintro ⟨y, ⟨z, hz, hy | hy⟩, hx⟩
    all_goals
      refine ⟨alterCoordinate z 0 1, ?_, ?_⟩
    · rw [sum_alterCoordinate]
      apply Int.not_even_iff_odd.mp
      simpa only [Int.even_add_one, not_not] using hz
    · left
      rw [hx, hy]
      funext i
      by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
    · rw [sum_alterCoordinate]
      apply Int.not_even_iff_odd.mp
      simpa only [Int.even_add_one, not_not] using hz
    · right
      rw [hx, hy]
      funext i
      by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
  · rintro ⟨z, hz, hx | hx⟩
    · refine ⟨intVec (alterCoordinate z 0 (-1)), ?_, ?_⟩
      · refine ⟨alterCoordinate z 0 (-1), ?_, Or.inl rfl⟩
        rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr hz)
      · rw [hx]
        funext i
        by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
    · refine ⟨(fun i => (alterCoordinate z 0 (-1) i : ℝ) + 1 / 2), ?_, ?_⟩
      · refine ⟨alterCoordinate z 0 (-1), ?_, Or.inr rfl⟩
        rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr hz)
      · rw [hx]
        funext i
        by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring

theorem roundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) : roundedInt x = m := by
  have hp : round (1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
  have hn : round (-1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
  funext i
  dsimp [roundedInt]
  rw [hx i, round_intCast_add]
  rcases hε i with he | he <;> norm_num [he, hp, hn]

theorem foldedRadius_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    ∀ i, foldedRadius x i = 1 / 4 := by
  intro i
  unfold foldedRadius
  rw [roundedInt_of_signed_quarters hε hx, hx i]
  rcases hε i with he | he <;> norm_num [he]

theorem halfRoundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    ∀ i, halfRoundedInt x i = m i - if ε i = -1 then 1 else 0 := by
  intro i
  unfold halfRoundedInt
  rw [roundedInt_of_signed_quarters hε hx, hx i]
  rcases hε i with he | he <;> norm_num [he, sub_eq_add_neg]

theorem sum_halfRoundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    (∑ i, halfRoundedInt x i) = (∑ i, m i) - (negativeSignCount ε : ℤ) := by
  classical
  simp only [halfRoundedInt_of_signed_quarters hε hx, Finset.sum_sub_distrib]
  simp [negativeSignCount, Finset.sum_ite]

theorem e8QuarterFamily_iff_folded (x : Fin 8 → ℝ) :
    E8QuarterFamily x ↔ ((∀ i, foldedRadius x i = 1 / 4) ∧
      ¬Even (∑ i, roundedInt x i) ∧ ¬Even (∑ i, halfRoundedInt x i)) := by
  classical
  constructor
  · rintro ⟨m, ε, hm, hε, he, hx⟩
    refine ⟨foldedRadius_of_signed_quarters hε hx, ?_, ?_⟩
    · rw [roundedInt_of_signed_quarters hε hx]
      exact Int.not_even_iff_odd.mpr hm
    · rw [sum_halfRoundedInt_of_signed_quarters hε hx]
      apply Int.not_even_iff_odd.mpr
      exact Int.odd_sub.mpr ⟨fun _ => (Int.even_coe_nat _).mpr he, fun _ => hm⟩
  · rintro ⟨hr, hm, hh⟩
    let m := roundedInt x
    let ε : Fin 8 → ℤ := fun i => if 0 ≤ x i - (m i : ℝ) then 1 else -1
    have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
      intro i
      by_cases hi : 0 ≤ x i - (m i : ℝ)
      · exact Or.inl (if_pos hi)
      · exact Or.inr (if_neg hi)
    have hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4 := by
      intro i
      have hi : |x i - (m i : ℝ)| = 1 / 4 := hr i
      by_cases hs : 0 ≤ x i - (m i : ℝ)
      · rw [abs_of_nonneg hs] at hi
        simp only [ε, if_pos hs, Int.cast_one]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hs)] at hi
        simp only [ε, if_neg hs, Int.cast_neg, Int.cast_one]
        linarith
    have hmo : Odd (∑ i, m i) := Int.not_even_iff_odd.mp hm
    have hho := Int.not_even_iff_odd.mp hh
    rw [sum_halfRoundedInt_of_signed_quarters hε hx] at hho
    have he : Even (negativeSignCount ε) :=
      (Int.even_coe_nat _).mp ((Int.odd_sub.mp hho).mp hmo)
    exact ⟨m, ε, hmo, hε, he, hx⟩

/-- The paper's three complete coordinate families, with no bounded enumeration. -/
def E8PaperHole (x : Fin 8 → ℝ) : Prop :=
  E8FirstFamily x ∨ PaperHalfGrid x ∨ E8QuarterFamily x

theorem e8FoldedHole_iff_paper (x : Fin 8 → ℝ) : E8FoldedHole x ↔ E8PaperHole x := by
  rw [E8PaperHole, e8FirstFamily_iff_oddCoset, e8OddCoset_iff_folded_endpoints,
    ← balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8), e8QuarterFamily_iff_folded]
  unfold E8FoldedHole
  tauto

/-- Proposition 3.4 in its literal dimension-eight coordinate formulation. -/
theorem isDeepHole_E8_iff_paper (x : Fin 8 → ℝ) :
    IsDeepHole (dPlusSet 8) x ↔ E8PaperHole x :=
  (isDeepHole_E8_iff x).trans (e8FoldedHole_iff_paper x)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8FoldedHole_iff_paper
#print axioms PaperVerification.ColdSpots.isDeepHole_E8_iff_paper
end
end Source_LatticeE8Families
-- END ORIGINAL PaperVerification.LatticeE8Families


-- BEGIN ORIGINAL PaperVerification.BWCosets
section Source_BWCosets

-- original header: module
-- original header: public import PaperVerification.BWCoordinates
-- original header: public import PaperVerification.LatticeE8Families
-- original header: public import Mathlib.Logic.Equiv.Set
-- original header: @[expose] public section
/-! # The sixteen actual E8 cosets in M

The representatives are exactly equation (27): half of a homogeneous affine
word, followed by the optional first-coordinate unit vector.  Coverage and
uniqueness are proved on real lattice points, giving a bijection usable for
both infinite Gaussian sums and exact distances.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def halfWord (c : BinaryWord8) : Fin 8 → ℝ := fun i => ((c i).val : ℝ) / 2

theorem halfWord_apply_of_eq_zero {c : BinaryWord8} {i : Fin 8} (h : c i = 0) :
    halfWord c i = 0 := by
  change ((c i).val : ℝ) / 2 = 0
  rw [h, ZMod.val_zero]
  norm_num

theorem halfWord_apply_of_eq_one {c : BinaryWord8} {i : Fin 8} (h : c i = 1) :
    halfWord c i = 1 / 2 := by
  change ((c i).val : ℝ) / 2 = 1 / 2
  rw [h, show (1 : Binary).val = 1 by decide]
  norm_num

def bitUnit (ε : Binary) : Fin 8 → ℤ := fun i => if i = 0 then ε.val else 0

abbrev BWQuotient := LinearCoefficients3 × Binary

def bwRepresentative (q : BWQuotient) : Fin 8 → ℝ :=
  halfWord (linearWord3 q.1) + intVec (bitUnit q.2)

theorem card_bwQuotient : Fintype.card BWQuotient = 16 := by
  norm_num [BWQuotient, LinearCoefficients3, Binary, Fintype.card_fun]

theorem sum_bitUnit (ε : Binary) : (∑ i, bitUnit ε i) = (ε.val : ℤ) := by
  simp [bitUnit]

theorem halfWord_mem_bwM {c : BinaryWord8} (hc : InRM3 c) : halfWord c ∈ bwMSet := by
  refine ⟨fun i => (c i).val, ?_, rfl⟩
  simpa only [binary_val_cast] using hc

theorem bwRepresentative_mem (q : BWQuotient) : bwRepresentative q ∈ bwMSet :=
  bwMSet_add (halfWord_mem_bwM (linearWord3_mem q.1)) (intVec_mem_bwM (bitUnit q.2))

theorem bwMSet_iff_integer_halfCode (x : Fin 8 → ℝ) :
    x ∈ bwMSet ↔ ∃ m : Fin 8 → ℤ, ∃ c : BinaryWord8,
      InRM3 c ∧ x = intVec m + halfWord c := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    let c : BinaryWord8 := fun i => (w i : Binary)
    let m : Fin 8 → ℤ := fun i => (w i - (c i).val) / 2
    have hi (i : Fin 8) : 2 * m i = w i - (c i).val := by
      apply Int.mul_ediv_cancel'
      apply even_iff_two_dvd.mp
      apply ZMod.intCast_eq_zero_iff_even.mp
      simp only [Int.cast_sub, binary_val_cast, c, sub_self]
    refine ⟨m, c, hw, ?_⟩
    funext i
    change (w i : ℝ) / 2 = (m i : ℝ) + ((c i).val : ℝ) / 2
    have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
    linarith
  · rintro ⟨m, c, hc, rfl⟩
    exact bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM hc)

theorem halfWord_complement (c : BinaryWord8) :
    halfWord (fun i => 1 + c i) = fun i => 1 / 2 - halfWord c i := by
  funext i
  change (((1 + c i).val : ℝ) / 2) = 1 / 2 - ((c i).val : ℝ) / 2
  rcases binary_eq_zero_or_one (c i) with h | h
  · rw [h, add_zero, show (1 : Binary).val = 1 by decide, ZMod.val_zero]
    norm_num
  · rw [h, show (1 + 1 : Binary) = 0 by decide, ZMod.val_zero,
      show (1 : Binary).val = 1 by decide]
    norm_num

theorem intVec_mem_dPlus_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℤ) :
    intVec z ∈ dPlusSet n ↔ Even (∑ i, z i) := by
  constructor
  · rintro ⟨w, hw, he | he⟩
    · have hzw := intVec_injective n he
      simpa only [hzw] using hw
    · have hi := congrFun he ⟨0, hn⟩
      exact (integer_ne_half_shift (z ⟨0, hn⟩) (w ⟨0, hn⟩) hi).elim
  · intro hz
    exact ⟨z, hz, Or.inl rfl⟩

theorem even_sum_sub_parity_bit (m : Fin 8 → ℤ) :
    Even ((∑ i, m i) - (((∑ i, m i : ℤ) : Binary).val : ℤ)) := by
  apply ZMod.intCast_eq_zero_iff_even.mp
  simp only [Int.cast_sub, binary_val_cast, sub_self]

/-- Every actual M point belongs to one of the sixteen displayed cosets. -/
theorem bw_coset_coverage {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) :
    ∃ q : BWQuotient, ∃ l ∈ dPlusSet 8, x = l + bwRepresentative q := by
  rcases (bwMSet_iff_integer_halfCode x).mp hx with ⟨m, c, hc, rfl⟩
  obtain ⟨a, hc | hc⟩ := inRM3_linear_or_complement c hc
  · subst c
    let ε : Binary := (∑ i, m i : ℤ)
    let z := m - bitUnit ε
    have hz : Even (∑ i, z i) := by
      simpa only [z, Pi.sub_apply, Finset.sum_sub_distrib, sum_bitUnit, ε] using
        even_sum_sub_parity_bit m
    refine ⟨(a, ε), intVec z, ⟨z, hz, Or.inl rfl⟩, ?_⟩
    funext i
    simp only [bwRepresentative, Pi.add_apply, intVec, z, Pi.sub_apply, Int.cast_sub]
    ring
  · rw [hc, halfWord_complement]
    let ε : Binary := (∑ i, m i : ℤ)
    let u : Fin 8 → ℤ := fun i => (linearWord3 a i).val
    let z : Fin 8 → ℤ := fun i => m i - u i - bitUnit ε i
    have hu : Even (∑ i, u i) := by
      have h := (Int.even_coe_nat _).mpr (inRM3_even_weight (linearWord3_mem a))
      simpa only [u, ← Nat.cast_sum, sum_binary_val] using h
    have hz : Even (∑ i, z i) := by
      have hm := (even_sum_sub_parity_bit m).sub hu
      have heq : (∑ i, z i) = ((∑ i, m i) - (ε.val : ℤ)) - ∑ i, u i := by
        simp only [z, Finset.sum_sub_distrib, sum_bitUnit]
        ring
      rw [heq]
      exact hm
    refine ⟨(a, ε), (fun i => (z i : ℝ) + 1 / 2), ⟨z, hz, Or.inr rfl⟩, ?_⟩
    funext i
    simp only [bwRepresentative, Pi.add_apply, intVec, z, u, Int.cast_sub, halfWord,
      Int.cast_natCast]
    ring

/-- Distinct displayed representatives never differ by an E8 vector. -/
theorem bwRepresentative_mod_e8_injective {q r : BWQuotient}
    (h : bwRepresentative q - bwRepresentative r ∈ dPlusSet 8) : q = r := by
  rcases h with ⟨z, hz, he | he⟩
  · have hword : linearWord3 q.1 = linearWord3 r.1 := by
      funext i
      have hi := congrFun he i
      change ((linearWord3 q.1 i).val : ℝ) / 2 + (bitUnit q.2 i : ℝ) -
        (((linearWord3 r.1 i).val : ℝ) / 2 + (bitUnit r.2 i : ℝ)) = (z i : ℝ) at hi
      have hint : ((linearWord3 q.1 i).val : ℤ) - (linearWord3 r.1 i).val +
          2 * (bitUnit q.2 i - bitUnit r.2 i) = 2 * z i := by
        exact_mod_cast (show ((linearWord3 q.1 i).val : ℝ) - (linearWord3 r.1 i).val +
          2 * ((bitUnit q.2 i : ℝ) - (bitUnit r.2 i : ℝ)) = 2 * (z i : ℝ) by linarith)
      have hb := congrArg (fun k : ℤ => (k : Binary)) hint
      have hsub : linearWord3 q.1 i - linearWord3 r.1 i = 0 := by simpa using hb
      exact sub_eq_zero.mp hsub
    have ha : q.1 = r.1 := linearWord3_injective hword
    have hz' : intVec (bitUnit q.2 - bitUnit r.2) ∈ dPlusSet 8 := by
      have heq : bwRepresentative q - bwRepresentative r = intVec (bitUnit q.2 - bitUnit r.2) := by
        funext i
        simp only [bwRepresentative, Pi.sub_apply, Pi.add_apply, hword, intVec, Int.cast_sub]
        ring
      rw [heq] at he
      rw [he]
      exact ⟨z, hz, Or.inl rfl⟩
    have hp := (intVec_mem_dPlus_iff (by decide : 0 < 8) _).mp hz'
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_bitUnit] at hp
    have hb := hp.intCast_zmod_two
    have heps : q.2 = r.2 := sub_eq_zero.mp (by simpa only [Int.cast_sub, binary_val_cast] using hb)
    exact Prod.ext ha heps
  · have hi := congrFun he 0
    have he0 : (((q.2.val : ℤ) - (r.2.val : ℤ) : ℤ) : ℝ) =
        (z 0 : ℝ) + 1 / 2 := by
      simpa [bwRepresentative, halfWord, linearWord3_zero_coordinate,
        intVec, bitUnit] using hi
    exact (integer_ne_half_shift ((q.2.val : ℤ) - r.2.val) (z 0) he0).elim

def bwCosetMap (v : BWQuotient × dPlusSet 8) : bwMSet :=
  ⟨v.2.val + bwRepresentative v.1, bwMSet_add (dPlusSet_subset_bwM v.2.property)
    (bwRepresentative_mem v.1)⟩

theorem bwCosetMap_bijective : Function.Bijective bwCosetMap := by
  constructor
  · rintro ⟨q, l⟩ ⟨r, k⟩ he
    have hv := congrArg Subtype.val he
    change l.val + bwRepresentative q = k.val + bwRepresentative r at hv
    have hd : bwRepresentative q - bwRepresentative r = k.val - l.val := by
      funext i
      have hi := congrFun hv i
      change l.val i + bwRepresentative q i = k.val i + bwRepresentative r i at hi
      change bwRepresentative q i - bwRepresentative r i = k.val i - l.val i
      linarith
    have hq : q = r := bwRepresentative_mod_e8_injective
      (hd.symm ▸ dPlusSet_sub (by decide : Even 8) k.property l.property)
    subst r
    have hl : l = k := Subtype.ext (add_right_cancel hv)
    cases hl
    rfl
  · intro x
    obtain ⟨q, l, hl, hx⟩ := bw_coset_coverage x.property
    exact ⟨(q, ⟨l, hl⟩), Subtype.ext hx.symm⟩

def bwCosetEquiv : BWQuotient × dPlusSet 8 ≃ bwMSet :=
  Equiv.ofBijective bwCosetMap bwCosetMap_bijective

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.bwCosetMap_bijective
#print axioms PaperVerification.ColdSpots.bw_coset_coverage
end
end Source_BWCosets
-- END ORIGINAL PaperVerification.BWCosets


-- BEGIN ORIGINAL PaperVerification.LatticeGluing
section Source_LatticeGluing

-- original header: module
-- original header: public import Mathlib.Data.Real.Basic
-- original header: public import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- original header: public import Mathlib.Algebra.BigOperators.Ring.Finset
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Exact finite-profile gluing inequality

This file proves the finite-dimensional inequality and equality statement used in
Proposition 7.1 of `lattice_cold_spots(2).pdf`. The theorem is an algebraic statement
about coset profiles; the identification of these profiles with Gaussian lattice
sums is a separate dependency and is not assumed to have been verified here.
-/

namespace PaperVerification.Lattice

open scoped BigOperators

variable {ι : Type*}

/-- The exact nonnegative-defect identity behind diagonal gluing. -/
theorem diagonal_gluing_defect (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ) :
    (∑ i ∈ s, u i * v i) - (2 * κ * σ - (s.card : ℝ) * κ ^ 2) =
      (∑ i ∈ s, (u i - κ) * (v i - κ)) +
        κ * ((∑ i ∈ s, u i) - σ) + κ * ((∑ i ∈ s, v i) - σ) := by
  have hexp (i : ι) : (u i - κ) * (v i - κ) =
      u i * v i - κ * u i - κ * v i + κ ^ 2 := by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- Proposition 7.1's finite-profile bound, for an arbitrary finite quotient. -/
theorem diagonal_gluing_bound (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ)
    (hκ : 0 ≤ κ) (hu : ∀ i ∈ s, κ ≤ u i) (hv : ∀ i ∈ s, κ ≤ v i)
    (hSu : σ ≤ ∑ i ∈ s, u i) (hSv : σ ≤ ∑ i ∈ s, v i) :
    2 * κ * σ - (s.card : ℝ) * κ ^ 2 ≤ ∑ i ∈ s, u i * v i := by
  have hd : 0 ≤ ∑ i ∈ s, (u i - κ) * (v i - κ) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (sub_nonneg.mpr (hu i hi))
      (sub_nonneg.mpr (hv i hi))
  have hU := mul_nonneg hκ (sub_nonneg.mpr hSu)
  have hV := mul_nonneg hκ (sub_nonneg.mpr hSv)
  linarith [diagonal_gluing_defect s u v κ σ]

/-- The exact equality locus. Strict positivity of the profile minimum is needed
for equality in the two marginal bounds; Gaussian profile minima are positive. -/
theorem diagonal_gluing_eq_iff (s : Finset ι) (u v : ι → ℝ) (κ σ : ℝ)
    (hκ : 0 < κ) (hu : ∀ i ∈ s, κ ≤ u i) (hv : ∀ i ∈ s, κ ≤ v i)
    (hSu : σ ≤ ∑ i ∈ s, u i) (hSv : σ ≤ ∑ i ∈ s, v i) :
    (∑ i ∈ s, u i * v i) = 2 * κ * σ - (s.card : ℝ) * κ ^ 2 ↔
      (∑ i ∈ s, u i) = σ ∧ (∑ i ∈ s, v i) = σ ∧
        ∀ i ∈ s, u i = κ ∨ v i = κ := by
  have hi : ∀ i ∈ s, 0 ≤ (u i - κ) * (v i - κ) :=
    fun i hi => mul_nonneg (sub_nonneg.mpr (hu i hi)) (sub_nonneg.mpr (hv i hi))
  have hd : 0 ≤ ∑ i ∈ s, (u i - κ) * (v i - κ) := Finset.sum_nonneg hi
  have hU := mul_nonneg hκ.le (sub_nonneg.mpr hSu)
  have hV := mul_nonneg hκ.le (sub_nonneg.mpr hSv)
  constructor
  · intro h
    have hdu : κ * ((∑ i ∈ s, u i) - σ) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    have hdv : κ * ((∑ i ∈ s, v i) - σ) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    have hz : (∑ i ∈ s, (u i - κ) * (v i - κ)) = 0 := by
      linarith [diagonal_gluing_defect s u v κ σ]
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hdu).resolve_left (ne_of_gt hκ))
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hdv).resolve_left (ne_of_gt hκ))
    · intro i his
      have hp : (u i - κ) * (v i - κ) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hi).mp hz i his
      exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro ⟨hUeq, hVeq, hzero⟩
    have hz : (∑ i ∈ s, (u i - κ) * (v i - κ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases hzero i hi with h | h <;> simp [h]
    have hid := diagonal_gluing_defect s u v κ σ
    rw [hUeq, hVeq, hz] at hid
    simp only [sub_self, mul_zero, add_zero, zero_add] at hid
    exact sub_eq_zero.mp hid

end PaperVerification.Lattice

#print axioms PaperVerification.Lattice.diagonal_gluing_bound
#print axioms PaperVerification.Lattice.diagonal_gluing_eq_iff
end Source_LatticeGluing
-- END ORIGINAL PaperVerification.LatticeGluing


-- BEGIN ORIGINAL PaperVerification.BWGluing
section Source_BWGluing

-- original header: module
-- original header: public import PaperVerification.BWCosets
-- original header: public import PaperVerification.E7Projection
-- original header: public import PaperVerification.LatticeGluing
-- original header: public import Mathlib.Topology.Algebra.InfiniteSum.Real
-- original header: @[expose] public section
/-! # Exact Gaussian and distance gluing for the Barnes–Wall point set

The sums are over actual distinct points of the diagonal union of E8 cosets.
Bijections and absolute convergence justify every infinite rearrangement.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

/-- The sixteen-dimensional diagonal lattice in Section 7. -/
def bwGammaSet : Set (Fin 16 → ℝ) :=
  {z | ∃ q : BWQuotient, ∃ l ∈ dPlusSet 8, ∃ k ∈ dPlusSet 8,
    z = Fin.append (l + bwRepresentative q) (k + bwRepresentative q)}

def bwLeft (z : Fin 16 → ℝ) : Fin 8 → ℝ := fun i => z (Fin.castAdd 8 i)
def bwRight (z : Fin 16 → ℝ) : Fin 8 → ℝ := fun i => z (Fin.natAdd 8 i)

@[simp] theorem bwLeft_append (x y : Fin 8 → ℝ) : bwLeft (Fin.append x y) = x := by
  funext i
  exact Fin.append_left x y i

@[simp] theorem bwRight_append (x y : Fin 8 → ℝ) : bwRight (Fin.append x y) = y := by
  funext i
  exact Fin.append_right x y i

theorem append_bw_blocks (z : Fin 16 → ℝ) : Fin.append (bwLeft z) (bwRight z) = z := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left (bwLeft z) (bwRight z) j
  · exact Fin.append_right (bwLeft z) (bwRight z) j

theorem sqDist_append (x y u v : Fin 8 → ℝ) :
    sqDist (Fin.append x y) (Fin.append u v) = sqDist x u + sqDist y v := by
  unfold sqDist
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def bwGammaMap (v : BWQuotient × (dPlusSet 8 × dPlusSet 8)) : bwGammaSet :=
  ⟨Fin.append (v.2.1.val + bwRepresentative v.1) (v.2.2.val + bwRepresentative v.1),
    v.1, v.2.1.val, v.2.1.property, v.2.2.val, v.2.2.property, rfl⟩

theorem bwGammaMap_bijective : Function.Bijective bwGammaMap := by
  constructor
  · rintro ⟨q, l, k⟩ ⟨r, l', k'⟩ h
    have hv := congrArg Subtype.val h
    have hl : l.val + bwRepresentative q = l'.val + bwRepresentative r := by
      simpa only [bwGammaMap, bwLeft_append] using congrArg bwLeft hv
    have hcoset : bwCosetMap (q, l) = bwCosetMap (r, l') := Subtype.ext hl
    have hp := bwCosetMap_bijective.1 hcoset
    have hq := congrArg Prod.fst hp
    have hll := congrArg Prod.snd hp
    change q = r at hq
    change l = l' at hll
    subst r
    subst l'
    have hk : k.val + bwRepresentative q = k'.val + bwRepresentative q := by
      simpa only [bwGammaMap, bwRight_append] using congrArg bwRight hv
    have hkk : k = k' := Subtype.ext (add_right_cancel hk)
    subst k'
    rfl
  · rintro ⟨x, q, l, hl, k, hk, hx⟩
    exact ⟨(q, ⟨l, hl⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩

def bwGammaEquiv : BWQuotient × (dPlusSet 8 × dPlusSet 8) ≃ bwGammaSet :=
  Equiv.ofBijective bwGammaMap bwGammaMap_bijective

def bwThetaProfile (α : ℝ) (x : Fin 8 → ℝ) (q : BWQuotient) : ℝ :=
  setGaussian (dPlusSet 8) α (x - bwRepresentative q)

def bwDepthProfile (x : Fin 8 → ℝ) (q : BWQuotient) : ℝ :=
  squaredDepth (dPlusSet 8) (x - bwRepresentative q)

theorem bwThetaProfile_nonneg (α : ℝ) (x : Fin 8 → ℝ) (q : BWQuotient) :
    0 ≤ bwThetaProfile α x q := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- The marginal Gaussian sum is exactly the sum of the sixteen coset profiles. -/
theorem setGaussian_bwM_eq_sum_profiles {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    setGaussian bwMSet α x = ∑ q : BWQuotient, bwThetaProfile α x q := by
  let f : BWQuotient × dPlusSet 8 → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.val + bwRepresentative v.1) x)
  have hfq (q : BWQuotient) : Summable (fun l : dPlusSet 8 => f (q, l)) := by
    simpa only [f, sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (x - bwRepresentative q)
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr
    ⟨hfq, Summable.of_finite⟩
  calc
    _ = ∑' v, f v := (bwCosetEquiv.tsum_eq (fun z : bwMSet => Real.exp (-α * sqDist z.val x))).symm
    _ = ∑' q : BWQuotient, ∑' l : dPlusSet 8, f (q, l) := hf.tsum_prod
    _ = _ := by simp only [tsum_fintype, f, sqDist_add_left, bwThetaProfile, setGaussian]

/-- Convergent product of the two Gaussian series in one diagonal coset. -/
theorem hasSum_bw_coset_product {α : ℝ} (hα : 0 < α)
    (x y : Fin 8 → ℝ) (q : BWQuotient) :
    HasSum (fun v : dPlusSet 8 × dPlusSet 8 =>
      Real.exp (-α * sqDist (v.1.val + bwRepresentative q) x) *
      Real.exp (-α * sqDist (v.2.val + bwRepresentative q) y))
      (bwThetaProfile α x q * bwThetaProfile α y q) := by
  have hx : Summable (fun l : dPlusSet 8 => Real.exp (-α * sqDist (l.val + bwRepresentative q) x)) := by
    simpa only [sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (x - bwRepresentative q)
  have hy : Summable (fun l : dPlusSet 8 => Real.exp (-α * sqDist (l.val + bwRepresentative q) y)) := by
    simpa only [sqDist_add_left] using
      summable_setGaussian_dPlus (by decide : 0 < 8) hα (y - bwRepresentative q)
  have hprod := Summable.mul_of_nonneg hx hy (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  have hs := hx.hasSum.mul hy.hasSum hprod
  simpa only [bwThetaProfile, setGaussian, sqDist_add_left] using hs

/-- The exact inner-product formula in Proposition 7.1 for the actual lattice. -/
theorem setGaussian_bwGamma_eq_sum_profiles {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) =
      ∑ q : BWQuotient, bwThetaProfile α x q * bwThetaProfile α y q := by
  let f : BWQuotient × (dPlusSet 8 × dPlusSet 8) → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.1.val + bwRepresentative v.1) x) *
    Real.exp (-α * sqDist (v.2.2.val + bwRepresentative v.1) y)
  have hq (q : BWQuotient) : HasSum (fun v => f (q, v))
      (bwThetaProfile α x q * bwThetaProfile α y q) := hasSum_bw_coset_product hα x y q
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => mul_nonneg
    (Real.exp_pos _).le (Real.exp_pos _).le)).mpr ⟨fun q => (hq q).summable, Summable.of_finite⟩
  calc
    _ = ∑' v, Real.exp (-α * sqDist (bwGammaEquiv v).val (Fin.append x y)) :=
      (bwGammaEquiv.tsum_eq _).symm
    _ = ∑' v, f v := by
      apply tsum_congr
      rintro ⟨q, l, k⟩
      change Real.exp (-α * sqDist (Fin.append (l.val + bwRepresentative q)
        (k.val + bwRepresentative q)) (Fin.append x y)) = _
      rw [sqDist_append, mul_add, Real.exp_add]
    _ = ∑' q : BWQuotient, ∑' v : dPlusSet 8 × dPlusSet 8, f (q, v) := hf.tsum_prod
    _ = _ := by simp only [(hq _).tsum_eq, tsum_fintype]

/-- Absolute convergence for the actual diagonal point-set series. -/
theorem summable_setGaussian_bwGamma {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    Summable (fun v : bwGammaSet => Real.exp (-α * sqDist v.val z)) := by
  let x := bwLeft z
  let y := bwRight z
  let f : BWQuotient × (dPlusSet 8 × dPlusSet 8) → ℝ := fun v =>
    Real.exp (-α * sqDist (v.2.1.val + bwRepresentative v.1) x) *
    Real.exp (-α * sqDist (v.2.2.val + bwRepresentative v.1) y)
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => mul_nonneg
    (Real.exp_pos _).le (Real.exp_pos _).le)).mpr
      ⟨fun q => (hasSum_bw_coset_product hα x y q).summable, Summable.of_finite⟩
  apply (bwGammaEquiv.summable_iff (f := fun v : bwGammaSet => Real.exp (-α * sqDist v.val z))).mp
  convert hf using 1
  funext v
  change Real.exp (-α * sqDist (Fin.append (v.2.1.val + bwRepresentative v.1)
    (v.2.2.val + bwRepresentative v.1)) z) = _
  rw [← append_bw_blocks z, sqDist_append, mul_add, Real.exp_add]

/-- A profile value is attained by a point in that actual coset. -/
theorem bwDepthProfile_attained (x : Fin 8 → ℝ) (q : BWQuotient) :
    ∃ l ∈ dPlusSet 8, sqDist x (l + bwRepresentative q) = bwDepthProfile x q := by
  obtain ⟨l, hl, hd⟩ := exists_nearest_dPlus (by decide : 0 < 8) (x - bwRepresentative q)
  refine ⟨l, hl, ?_⟩
  rw [← sqDist_sub_left, hd]
  rfl

theorem bwDepthProfile_le_sqDist (x : Fin 8 → ℝ) (q : BWQuotient)
    {l : Fin 8 → ℝ} (hl : l ∈ dPlusSet 8) :
    bwDepthProfile x q ≤ sqDist x (l + bwRepresentative q) := by
  rw [← sqDist_sub_left]
  exact squaredDepth_le _ hl

/-- One of the sixteen profile distances is the exact distance to M. -/
theorem exists_min_bwDepthProfile (x : Fin 8 → ℝ) :
    ∃ q : BWQuotient, bwDepthProfile x q = squaredDepth bwMSet x ∧
      ∀ r, bwDepthProfile x q ≤ bwDepthProfile x r := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ (bwDepthProfile x)
    (show (Finset.univ : Finset BWQuotient).Nonempty from ⟨(0, 0), Finset.mem_univ _⟩)
  have hmin : ∀ r, bwDepthProfile x q ≤ bwDepthProfile x r := fun r => hq r (Finset.mem_univ _)
  refine ⟨q, ?_, hmin⟩
  apply le_antisymm
  · apply le_csInf ((show bwMSet.Nonempty from ⟨0, bwMSet_zero⟩).image (fun z => sqDist x z))
    rintro v ⟨z, hz, rfl⟩
    obtain ⟨r, l, hl, rfl⟩ := bw_coset_coverage hz
    exact (hmin r).trans (bwDepthProfile_le_sqDist x r hl)
  · obtain ⟨l, hl, hdist⟩ := bwDepthProfile_attained x q
    rw [← hdist]
    exact squaredDepth_le x (bwMSet_add (dPlusSet_subset_bwM hl) (bwRepresentative_mem q))

theorem squaredDepth_bwM_le_profile (x : Fin 8 → ℝ) (q : BWQuotient) :
    squaredDepth bwMSet x ≤ bwDepthProfile x q := by
  obtain ⟨r, hr, hmin⟩ := exists_min_bwDepthProfile x
  rw [← hr]
  exact hmin q

theorem bwGamma_nonempty : bwGammaSet.Nonempty := by
  exact ⟨Fin.append (0 + bwRepresentative (0, 0)) (0 + bwRepresentative (0, 0)),
    (0, 0), 0, zero_mem_dPlusSet 8, 0, zero_mem_dPlusSet 8, rfl⟩

/-- Exact lower-bound characterization of the distance to the actual diagonal set. -/
theorem le_squaredDepth_bwGamma_iff (x y : Fin 8 → ℝ) (r : ℝ) :
    r ≤ squaredDepth bwGammaSet (Fin.append x y) ↔
      ∀ q : BWQuotient, r ≤ bwDepthProfile x q + bwDepthProfile y q := by
  constructor
  · intro hr q
    obtain ⟨l, hl, hx⟩ := bwDepthProfile_attained x q
    obtain ⟨k, hk, hy⟩ := bwDepthProfile_attained y q
    have hd := squaredDepth_le (Fin.append x y)
      (show Fin.append (l + bwRepresentative q) (k + bwRepresentative q) ∈ bwGammaSet from
        ⟨q, l, hl, k, hk, rfl⟩)
    rw [sqDist_append, hx, hy] at hd
    exact hr.trans hd
  · intro hr
    apply le_csInf (bwGamma_nonempty.image (fun z => sqDist (Fin.append x y) z))
    rintro v ⟨z, ⟨q, l, hl, k, hk, rfl⟩, rfl⟩
    dsimp only
    rw [sqDist_append]
    exact (hr q).trans (add_le_add (bwDepthProfile_le_sqDist x q hl)
      (bwDepthProfile_le_sqDist y q hk))

theorem squaredDepth_bwGamma_le_profile (x y : Fin 8 → ℝ) (q : BWQuotient) :
    squaredDepth bwGammaSet (Fin.append x y) ≤ bwDepthProfile x q + bwDepthProfile y q :=
  (le_squaredDepth_bwGamma_iff x y _).mp le_rfl q

theorem bwDepthProfile_le_one (x : Fin 8 → ℝ) (q : BWQuotient) : bwDepthProfile x q ≤ 1 := by
  have h := squaredDepth_dPlus_le (by decide : 8 ≤ 8) (x - bwRepresentative q)
  norm_num at h
  exact h

/-- The covering estimate is valid at every point of ordinary R¹⁶. -/
theorem squaredDepth_bwGamma_le (z : Fin 16 → ℝ) : squaredDepth bwGammaSet z ≤ 3 / 2 := by
  rw [← append_bw_blocks z]
  obtain ⟨q, hq, _⟩ := exists_min_bwDepthProfile (bwLeft z)
  have h := squaredDepth_bwGamma_le_profile (bwLeft z) (bwRight z) q
  rw [hq] at h
  linarith [squaredDepth_bwM_le (bwLeft z), bwDepthProfile_le_one (bwRight z) q]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.setGaussian_bwGamma_eq_sum_profiles
#print axioms PaperVerification.ColdSpots.le_squaredDepth_bwGamma_iff
#print axioms PaperVerification.ColdSpots.squaredDepth_bwGamma_le
end
end Source_BWGluing
-- END ORIGINAL PaperVerification.BWGluing


-- BEGIN ORIGINAL PaperVerification.BWEligibility
section Source_BWEligibility

-- original header: module
-- original header: public import PaperVerification.BWGluing
-- original header: @[expose] public section
/-! # Complete geometric eligibility for Barnes–Wall gluing

The full real-coordinate argument uses the complete E8 hole classification.
Every eligible M-hole has E8-coset squared distances only one half and one.
This is enough for the equality theorem; no orbit enumeration is needed.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def IntegerSum8 (x : Fin 8 → ℝ) : Prop := ∃ k : ℤ, (∑ i, x i) = (k : ℝ)
def QuarterGrid8 (x : Fin 8 → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = (k : ℝ) / 2 + 1 / 4

theorem squaredDepth_sub_of_subgroup {n : ℕ} (L : AddSubgroup (Fin n → ℝ))
    (x g : Fin n → ℝ) (hg : g ∈ L) : squaredDepth (L : Set _) (x - g) = squaredDepth (L : Set _) x := by
  simpa only [sub_eq_add_neg] using squaredDepth_add_of_subgroup L x (-g) (L.neg_mem hg)

theorem squaredDepth_zero_of_mem {n : ℕ} {L : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ L) :
    squaredDepth L x = 0 := by
  apply le_antisymm
  · simpa [sqDist] using squaredDepth_le x hx
  · exact squaredDepth_nonneg L ⟨x, hx⟩ x

theorem bwM_integerSum {x : Fin 8 → ℝ} (hx : x ∈ bwMSet) : IntegerSum8 x := by
  rcases hx with ⟨w, hw, rfl⟩
  have he : Even (∑ i, w i) := by
    apply ZMod.intCast_eq_zero_iff_even.mp
    rw [Int.cast_sum, binary_sum_eq_weight]
    exact (inRM3_even_weight hw).natCast_zmod_two
  obtain ⟨k, hk⟩ := he
  refine ⟨k, ?_⟩
  rw [← Finset.sum_div, ← Int.cast_sum, hk]
  push_cast
  ring

theorem integerSum_sub {x y : Fin 8 → ℝ} (hx : IntegerSum8 x) (hy : IntegerSum8 y) :
    IntegerSum8 (x - y) := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha, hb, Int.cast_sub]

theorem quarterGrid_iff_folded (x : Fin 8 → ℝ) :
    QuarterGrid8 x ↔ ∀ i, foldedRadius x i = 1 / 4 := by
  constructor
  · intro hx i
    obtain ⟨k, hk⟩ := hx i
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · have hi : x i = (m : ℝ) + 1 / 4 := by rw [hk, hm]; push_cast; ring
      have hr : round (1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
      have hxround : round (x i) = m := by
        rw [hi, round_intCast_add, hr, add_zero]
      change |x i - (round (x i) : ℝ)| = 1 / 4
      rw [hxround, hi, add_sub_cancel_left]
      norm_num
    · have hi : x i = ((m + 1 : ℤ) : ℝ) - 1 / 4 := by rw [hk, hm]; push_cast; ring
      have hr : round (-1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
      have hi' : x i = ((m + 1 : ℤ) : ℝ) + (-1 / 4 : ℝ) := by linarith
      have hxround : round (x i) = m + 1 := by
        rw [hi', round_intCast_add, hr, add_zero]
      change |x i - (round (x i) : ℝ)| = 1 / 4
      rw [hxround, hi', add_sub_cancel_left]
      norm_num
  · intro hx i
    have hi := hx i
    unfold foldedRadius at hi
    by_cases h : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg h] at hi
      refine ⟨2 * roundedInt x i, ?_⟩
      push_cast
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at hi
      refine ⟨2 * roundedInt x i - 1, ?_⟩
      push_cast
      linarith

theorem quarterGrid_sub_bwM {x g : Fin 8 → ℝ}
    (hx : QuarterGrid8 x) (hg : g ∈ bwMSet) : QuarterGrid8 (x - g) := by
  rcases hg with ⟨w, hw, rfl⟩
  intro i
  obtain ⟨k, hk⟩ := hx i
  refine ⟨k - w i, ?_⟩
  simp only [Pi.sub_apply, hk, Int.cast_sub]
  ring

/-- The two nearest integer parities of a quarter vector are linked to its sum. -/
theorem quarter_coordinate_sum_identity {x : Fin 8 → ℝ}
    (hx : ∀ i, foldedRadius x i = 1 / 4) :
    2 * (∑ i, x i) = ((∑ i, roundedInt x i) : ℝ) +
      ((∑ i, halfRoundedInt x i) : ℝ) + 4 := by
  have hi (i : Fin 8) : 2 * x i = (roundedInt x i : ℝ) + (halfRoundedInt x i : ℝ) + 1 / 2 := by
    have hr := hx i
    unfold foldedRadius at hr
    by_cases h : 0 ≤ x i - (roundedInt x i : ℝ)
    · rw [abs_of_nonneg h] at hr
      simp only [halfRoundedInt, if_pos h, add_zero]
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)] at hr
      simp only [halfRoundedInt, if_neg h, Int.cast_add, Int.cast_neg, Int.cast_one]
      linarith
  calc
    _ = ∑ i, 2 * x i := Finset.mul_sum ..
    _ = ∑ i, ((roundedInt x i : ℝ) + (halfRoundedInt x i : ℝ) + 1 / 2) :=
      Finset.sum_congr rfl (fun i _ => hi i)
    _ = _ := by norm_num [Finset.sum_add_distrib]

theorem quarter_integerSum_of_both_odd {x : Fin 8 → ℝ}
    (hx : ∀ i, foldedRadius x i = 1 / 4)
    (hi : ¬Even (∑ i, roundedInt x i)) (hh : ¬Even (∑ i, halfRoundedInt x i)) : IntegerSum8 x := by
  have he : Even ((∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i) + 4) :=
    ((Int.not_even_iff_odd.mp hi).add_odd (Int.not_even_iff_odd.mp hh)).add (by decide)
  obtain ⟨k, hk⟩ := he
  refine ⟨k, ?_⟩
  have hs := quarter_coordinate_sum_identity hx
  have hcast : ((∑ i, roundedInt x i) : ℝ) + ((∑ i, halfRoundedInt x i) : ℝ) + 4 =
      (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
  linarith

theorem quarter_parities_equiv {x : Fin 8 → ℝ} (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    Even (∑ i, roundedInt x i) ↔ Even (∑ i, halfRoundedInt x i) := by
  have hr := (quarterGrid_iff_folded x).mp hx
  rcases hs with ⟨k, hk⟩
  have hsum : 2 * k = (∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i) + 4 := by
    exact_mod_cast (show 2 * (k : ℝ) = ((∑ i, roundedInt x i) : ℝ) +
      ((∑ i, halfRoundedInt x i) : ℝ) + 4 by rw [← hk]; exact quarter_coordinate_sum_identity hr)
  have h : Even ((∑ i, roundedInt x i) + (∑ i, halfRoundedInt x i)) := by
    have he : Even (2 * k - 4) := (even_two.mul_right k).sub (by decide)
    convert he using 1 <;> omega
  exact Int.even_add.mp h

theorem quarter_two_depths {x : Fin 8 → ℝ} (hx : QuarterGrid8 x) (hs : IntegerSum8 x) :
    squaredDepth (dPlusSet 8) x = 1 / 2 ∨ squaredDepth (dPlusSet 8) x = 1 := by
  have hr := (quarterGrid_iff_folded x).mp hx
  have hp := quarter_parities_equiv hx hs
  have hd := squaredDepth_dPlus_of_constant x 0 (1 / 4) hr
  by_cases he : Even (∑ i, roundedInt x i)
  · left
    norm_num [he, hp.mp he] at hd
    exact hd
  · right
    have he' : ¬Even (∑ i, halfRoundedInt x i) := fun h => he (hp.mpr h)
    norm_num [he, he'] at hd
    exact hd

theorem foldedRadius_integer_halfWord (m : Fin 8 → ℤ) (c : BinaryWord8) (i : Fin 8) :
    foldedRadius (intVec m + halfWord c) i = (halfWord c) i := by
  rcases binary_eq_zero_or_one (c i) with h | h
  · have hc := halfWord_apply_of_eq_zero h
    have hx : (intVec m + halfWord c) i = (m i : ℝ) := by
      simp only [Pi.add_apply, intVec, hc, add_zero]
    have hr := (foldedRadius_eq_zero_iff _ i).mpr ⟨m i, hx⟩
    simpa only [hc] using hr
  · have hc := halfWord_apply_of_eq_one h
    have hx : (intVec m + halfWord c) i = (m i : ℝ) + 1 / 2 := by
      simp only [Pi.add_apply, intVec, hc]
    have hr := (foldedRadius_eq_half_iff _ i).mpr ⟨m i, hx⟩
    simpa only [hc] using hr

theorem nonintegerCount_integer_halfWord (m : Fin 8 → ℤ) (c : BinaryWord8) :
    nonintegerCount (intVec m + halfWord c) = binaryWeight c := by
  classical
  unfold nonintegerCount binaryWeight
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [← foldedRadius_eq_zero_iff, foldedRadius_integer_halfWord]
  rcases binary_eq_zero_or_one (c i) with h | h
  · norm_num [halfWord_apply_of_eq_zero h, h]
  · norm_num [halfWord_apply_of_eq_one h, h]

/-- Every point of the full half-grid has an actual integer part and binary word. -/
theorem halfGrid_integer_halfWord {x : Fin 8 → ℝ} (hx : HalfIntegerGrid x) :
    ∃ m : Fin 8 → ℤ, ∃ c : BinaryWord8, x = intVec m + halfWord c := by
  choose w hw using hx
  let c : BinaryWord8 := fun i => (w i : Binary)
  let m : Fin 8 → ℤ := fun i => (w i - (c i).val) / 2
  have hi (i : Fin 8) : 2 * m i = w i - (c i).val := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, c, sub_self]
  refine ⟨m, c, ?_⟩
  funext i
  change x i = (m i : ℝ) + ((c i).val : ℝ) / 2
  rw [hw i]
  have h : 2 * (m i : ℝ) = (w i : ℝ) - ((c i).val : ℝ) := by exact_mod_cast hi i
  linarith

theorem halfWord_sub_representation (c d : BinaryWord8) :
    ∃ m : Fin 8 → ℤ, halfWord c - halfWord d = intVec m + halfWord (fun i => c i - d i) := by
  let e : BinaryWord8 := fun i => c i - d i
  let m : Fin 8 → ℤ := fun i => ((c i).val - (d i).val - (e i).val : ℤ) / 2
  have hi (i : Fin 8) : 2 * m i = ((c i).val - (d i).val - (e i).val : ℤ) := by
    apply Int.mul_ediv_cancel'
    apply even_iff_two_dvd.mp
    apply ZMod.intCast_eq_zero_iff_even.mp
    simp only [Int.cast_sub, binary_val_cast, e, sub_self]
  refine ⟨m, ?_⟩
  funext i
  change ((c i).val : ℝ) / 2 - ((d i).val : ℝ) / 2 = (m i : ℝ) + ((e i).val : ℝ) / 2
  have h : 2 * (m i : ℝ) = ((c i).val : ℝ) - ((d i).val : ℝ) - ((e i).val : ℝ) := by exact_mod_cast hi i
  linarith

theorem halfWord_depth (m : Fin 8 → ℤ) (c : BinaryWord8)
    (hc0 : 0 < binaryWeight c) (hc8 : binaryWeight c < 8) :
    squaredDepth (dPlusSet 8) (intVec m + halfWord c) =
      min ((binaryWeight c : ℝ) / 4) ((8 - (binaryWeight c : ℝ)) / 4) := by
  classical
  have h0 : ∃ i, c i = 0 := by
    by_contra h
    push_neg at h
    have hh : ∀ i, c i = 1 := fun i => (binary_eq_zero_or_one _).resolve_left (h i)
    have hw := (binary_weight_eight_iff c).mpr hh
    omega
  have h1 : ∃ i, c i = 1 := by
    by_contra h
    push_neg at h
    have hh : ∀ i, c i = 0 := fun i => (binary_eq_zero_or_one _).resolve_right (h i)
    have hw := (binary_weight_zero_iff c).mpr hh
    omega
  obtain ⟨lo, hlo⟩ := h0
  obtain ⟨hi, hhi⟩ := h1
  have hr0 : foldedRadius (intVec m + halfWord c) lo = 0 := by
    rw [foldedRadius_integer_halfWord]
    exact halfWord_apply_of_eq_zero hlo
  have hr1 : foldedRadius (intVec m + halfWord c) hi = 1 / 2 := by
    rw [foldedRadius_integer_halfWord]
    exact halfWord_apply_of_eq_one hhi
  have hd := squaredDepth_dPlus_eq (intVec m + halfWord c) lo hi
    (fun i => by rw [hr0]; exact foldedRadius_nonneg _ i)
    (fun i => by rw [hr1]; exact foldedRadius_le_half _ i)
  have hbase : integerBaseCost (intVec m + halfWord c) = (binaryWeight c : ℝ) / 4 := by
    have hs (i : Fin 8) : (foldedRadius (intVec m + halfWord c) i) ^ 2 =
        if c i = 1 then 1 / 4 else 0 := by
      rw [foldedRadius_integer_halfWord]
      rcases binary_eq_zero_or_one (c i) with h | h
      · norm_num [halfWord_apply_of_eq_zero h, h]
      · norm_num [halfWord_apply_of_eq_one h, h]
    simp only [integerBaseCost, hs]
    simp [Finset.sum_ite, binaryWeight, div_eq_mul_inv]
  have hsum : (∑ i, foldedRadius (intVec m + halfWord c) i) = (binaryWeight c : ℝ) / 2 := by
    rw [folded_sum_eq_nonintegerCount]
    · rw [nonintegerCount_integer_halfWord]
    · intro i
      rw [foldedRadius_integer_halfWord]
      rcases binary_eq_zero_or_one (c i) with h | h
      · norm_num [halfWord_apply_of_eq_zero h, h]
      · norm_num [halfWord_apply_of_eq_one h, h]
  rw [integerRepairCost, halfRepairCost, hr0, hr1] at hd
  norm_num at hd
  rw [hbase, halfBaseCost_eq, hbase, hsum] at hd
  convert hd using 1 <;> congr 1 <;> ring

theorem balanced_outside_bwM_translates_two_depths {x g : Fin 8 → ℝ}
    (hx : BalancedHalfGrid x) (hxM : x ∉ bwMSet) (hg : g ∈ bwMSet) :
    squaredDepth (dPlusSet 8) (x - g) = 1 / 2 ∨ squaredDepth (dPlusSet 8) (x - g) = 1 := by
  have hgrid := (balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8) x).mp hx
  obtain ⟨m, c, rfl⟩ := halfGrid_integer_halfWord hgrid.1
  have hc : binaryWeight c = 4 := by
    have hcount := hgrid.2
    norm_num [nonintegerCount_integer_halfWord] at hcount
    exact hcount
  have hnc : ¬InRM3 c := fun h => hxM (bwMSet_add (intVec_mem_bwM m) (halfWord_mem_bwM h))
  obtain ⟨k, d, hd, rfl⟩ := (bwMSet_iff_integer_halfCode g).mp hg
  obtain ⟨a, ha⟩ := halfWord_sub_representation c d
  have heq : (intVec m + halfWord c) - (intVec k + halfWord d) =
      intVec (m - k + a) + halfWord (fun i => c i - d i) := by
    have hsplit : (intVec m + halfWord c) - (intVec k + halfWord d) =
        intVec (m - k) + (halfWord c - halfWord d) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, intVec, Int.cast_sub]
      ring
    rw [hsplit, ha, ← add_assoc, ← intVec_add]
  rw [heq]
  rcases eligible_word_difference_weights hc hnc hd with hw | hw | hw
  all_goals
    have hv := halfWord_depth (m - k + a) (fun i => c i - d i)
      (by rw [hw]; norm_num) (by rw [hw]; norm_num)
  · left
    norm_num [hw] at hv
    exact hv
  · right
    norm_num [hw] at hv
    exact hv
  · left
    norm_num [hw] at hv
    exact hv

/-- All translates of an eligible E8 hole have one of the two exact depths. -/
theorem e8_hole_bwMdeep_translates_two_depths {x g : Fin 8 → ℝ}
    (hx : E8FoldedHole x) (hM : squaredDepth bwMSet x = 1 / 2) (hg : g ∈ bwMSet) :
    squaredDepth (dPlusSet 8) (x - g) = 1 / 2 ∨ squaredDepth (dPlusSet 8) (x - g) = 1 := by
  have hxM : x ∉ bwMSet := by
    intro hxM
    have hzero := squaredDepth_zero_of_mem hxM
    linarith
  rcases hx with ⟨hr, hp⟩ | ⟨hr, hp⟩ | hb | ⟨hr, hp, hq⟩
  · have heq : x = intVec (roundedInt x) := by
      funext i
      exact sub_eq_zero.mp (abs_eq_zero.mp (hr i))
    exact (hxM (heq.symm ▸ intVec_mem_bwM (roundedInt x))).elim
  · have heq : x = fun i => (halfRoundedInt x i : ℝ) + 1 / 2 := by
      funext i
      have h := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp h)
    have hm : x ∈ bwMSet := by
      rw [heq]
      refine ⟨fun i => 2 * halfRoundedInt x i + 1, ?_, ?_⟩
      · simpa using (inRM3_one : InRM3 (fun _ : Fin 8 => (1 : Binary)))
      · funext i
        push_cast
        ring
    exact (hxM hm).elim
  · exact balanced_outside_bwM_translates_two_depths hb hxM hg
  · exact quarter_two_depths (quarterGrid_sub_bwM ((quarterGrid_iff_folded x).mpr hr) hg)
      (integerSum_sub (quarter_integerSum_of_both_odd hr hp hq) (bwM_integerSum hg))

def BWEligible (x : Fin 8 → ℝ) : Prop :=
  squaredDepth bwMSet x = 1 / 2 ∧ ∃ q : BWQuotient, bwDepthProfile x q = 1

theorem bwEligible_profile_two_depths {x : Fin 8 → ℝ} (hx : BWEligible x) (q : BWQuotient) :
    bwDepthProfile x q = 1 / 2 ∨ bwDepthProfile x q = 1 := by
  obtain ⟨q₀, hq₀⟩ := hx.2
  have hh : E8FoldedHole (x - bwRepresentative q₀) :=
    (squaredDepth_E8_eq_one_iff _).mp hq₀
  have hM : squaredDepth bwMSet (x - bwRepresentative q₀) = 1 / 2 := by
    change squaredDepth (bwMAddSubgroup : Set (Fin 8 → ℝ))
      (x - bwRepresentative q₀) = 1 / 2
    rw [squaredDepth_sub_of_subgroup bwMAddSubgroup x (bwRepresentative q₀) (bwRepresentative_mem q₀)]
    exact hx.1
  have hg : bwRepresentative q - bwRepresentative q₀ ∈ bwMSet :=
    bwMAddSubgroup.sub_mem (bwRepresentative_mem q) (bwRepresentative_mem q₀)
  have h := e8_hole_bwMdeep_translates_two_depths hh hM hg
  have heq : x - bwRepresentative q₀ - (bwRepresentative q - bwRepresentative q₀) =
      x - bwRepresentative q := by abel
  simpa only [heq, bwDepthProfile] using h

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8_hole_bwMdeep_translates_two_depths
#print axioms PaperVerification.ColdSpots.bwEligible_profile_two_depths
end
end Source_BWEligibility
-- END ORIGINAL PaperVerification.BWEligibility


-- Kernel-environment audit: every mathematical source body precedes this command.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let kenv := env.checked.get
  let entries := kenv.constants.foldStage2
    (fun rows name ci => rows.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let kind : ConstantInfo → String := fun ci => match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut failures : Array Json := #[]
  for (name, ci) in entries do
    if ci.isUnsafe then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unsafe_declaration", toJson true)])
    let deps := ci.getUsedConstantsAsSet.toArray.qsort Name.lt
    let mut dependencyRows : Array Json := #[]
    for dep in deps do
      match kenv.find? dep with
      | none =>
        failures := failures.push (Json.mkObj [
          ("declaration", toJson name.toString),
          ("missing_dependency", toJson dep.toString)])
      | some info =>
        let origin := match env.getModuleIdxFor? dep with
          | some idx => env.header.moduleNames[idx]!.toString
          | none => env.mainModule.toString
        dependencyRows := dependencyRows.push (Json.mkObj [
          ("name", toJson dep.toString), ("kind", toJson (kind info)),
          ("module", toJson origin)])
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (fun ax => !allowed.contains ax)
    if !bad.isEmpty then
      failures := failures.push (Json.mkObj [
        ("declaration", toJson name.toString),
        ("unapproved_axioms", toJson (bad.map Name.toString))])
    rows := rows.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind ci)),
      ("unsafe", toJson ci.isUnsafe),
      ("type", toJson (toString ci.type)),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("has_body", toJson (ci.value? (allowOpaque := true)).isSome),
      ("dependencies", Json.arr dependencyRows),
      ("axioms", toJson (axioms.map Name.toString))])
  let sourceHash ← IO.getEnv "PAPER_VERIFICATION_SOURCE_SHA256"
  let fingerprint ← IO.getEnv "PAPER_VERIFICATION_FINGERPRINT"
  let document := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("module", toJson env.mainModule.toString),
    ("source_sha256", toJson sourceHash),
    ("fingerprint", toJson fingerprint),
    ("kernel_environment", toJson true),
    ("declarations", Json.arr rows),
    ("failures", Json.arr failures),
    ("passed", toJson failures.isEmpty)]
  let target := (← IO.getEnv "PAPER_VERIFICATION_AUDIT_PATH").getD ".lake/build/paper-audit/PaperVerification_Lattice004.json"
  let path : System.FilePath := target
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path (document.compress ++ "\n")
  if !failures.isEmpty then
    throwError "Kernel declaration audit rejected {failures.size} dependency/axiom findings; see {target}"
  logInfo m!"Kernel declaration audit passed for {rows.size} declarations; see {target}"
