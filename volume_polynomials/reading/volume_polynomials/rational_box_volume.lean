module

public import VolumePolynomials.RationalPolytopeRepresentation
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false

/-!
# Certified rational volume approximation

Closed rational halfspaces are tested on the extremal vertices of rational
grid boxes. The inner and outer counts are rational bounds on actual Lebesgue
volume. Their difference tends to zero, including for empty or degenerate
polytopes, because a convex set has null frontier. Searching the decidable
rational gap test therefore gives a terminating executable approximation.
-/

open Set Filter Metric MeasureTheory
open scoped BigOperators Topology

namespace VolumePolynomials.RationalElimination

namespace Inequality

def rationalValue {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) : ℚ :=
  ∑ i, p.coefficient i * x i

theorem value_cast {n : ℕ} (p : Inequality n) (x : Fin n → ℚ) :
    p.value (fun i => (x i : ℝ)) = (p.rationalValue x : ℝ) := by
  first
  | simp [value, rationalValue]

theorem continuous_value {n : ℕ} (p : Inequality n) : Continuous p.value := by
  first
  | change Continuous (fun x : Fin n → ℝ => ∑ i, (p.coefficient i : ℝ) * x i)
    fun_prop

def upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  fun i => if 0 ≤ p.coefficient i then ((ν i : ℚ) + 1) / (k + 1) else (ν i : ℚ) / (k + 1)

def lowerCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) : Fin n → ℚ :=
  (negative p).upperCorner k ν

end Inequality

noncomputable abbrev cell {n : ℕ} (k : ℕ) (ν : Fin n → ℤ) : BoxIntegral.Box (Fin n) :=
  BoxIntegral.unitPartition.box (k + 1) ν

noncomputable def ambientBox (n R : ℕ) : BoxIntegral.Box (Fin n) :=
  ⟨fun _ => -((R : ℝ) + 1), fun _ => (R : ℝ) + 1,
    fun _ => by linarith [Nat.cast_nonneg (α := ℝ) R]⟩

theorem ambientBox_integral (n R : ℕ) : BoxIntegral.hasIntegralVertices (ambientBox n R) := by
  first
  | exact ⟨fun _ => -((R : ℤ) + 1), fun _ => (R : ℤ) + 1,
      fun _ => by simp [ambientBox], fun _ => by simp [ambientBox]⟩

/-- The explicit finite integer index set; no real-set membership is computed. -/
def gridIndices (n R k : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Ico (-((R : ℤ) + 1) * ((k : ℤ) + 1))
    (((R : ℤ) + 1) * ((k : ℤ) + 1)))

theorem mem_gridIndices_iff {n R k : ℕ} (ν : Fin n → ℤ) :
    ν ∈ gridIndices n R k ↔ cell k ν ≤ ambientBox n R := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [gridIndices, Fintype.mem_piFinset, BoxIntegral.Box.le_iff_bounds]
    simp only [Finset.mem_Ico, Pi.le_def, ambientBox, cell,
      BoxIntegral.unitPartition.box_lower, BoxIntegral.unitPartition.box_upper, Nat.cast_add,
      Nat.cast_one]
    constructor
    · intro h
      constructor
      · intro i
        apply (le_div_iff₀ hk).mpr
        exact_mod_cast (h i).1
      · intro i
        apply (div_le_iff₀ hk).mpr
        exact_mod_cast (Int.add_one_le_iff.mpr (h i).2)
    · rintro ⟨hl, hu⟩ i
      constructor
      · exact_mod_cast (le_div_iff₀ hk).mp (hl i)
      · apply Int.add_one_le_iff.mp
        exact_mod_cast (div_le_iff₀ hk).mp (hu i)

theorem index_mem_gridIndices {n R k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ ambientBox n R) :
    BoxIntegral.unitPartition.index (k + 1) x ∈ gridIndices n R k := by
  first
  | rw [mem_gridIndices_iff]
    exact BoxIntegral.unitPartition.mem_admissibleIndex_iff.mp
      (BoxIntegral.unitPartition.mem_admissibleIndex_of_mem_box (k + 1)
        (ambientBox_integral n R) hx)

theorem upperCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.upperCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) := by
  first
  | have hk : 0 < (k : ℝ) + 1 := by positivity
    rw [BoxIntegral.Box.Icc_eq_pi]
    intro i _
    simp only [Inequality.upperCorner, cell, BoxIntegral.unitPartition.box_lower,
      BoxIntegral.unitPartition.box_upper, Set.mem_Icc, Nat.cast_add, Nat.cast_one]
    split_ifs <;> push_cast <;> constructor <;> first | rfl | gcongr <;> linarith

theorem lowerCorner_mem {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ) :
    (fun i => (p.lowerCorner k ν i : ℝ)) ∈ BoxIntegral.Box.Icc (cell k ν) :=
  upperCorner_mem (negative p) k ν

theorem value_le_upperCorner {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    p.value x ≤ (p.rationalValue (p.upperCorner k ν) : ℝ) := by
  first
  | rw [← p.value_cast]
    apply Finset.sum_le_sum
    intro i hi
    have hxi : (cell k ν).lower i ≤ x i ∧ x i ≤ (cell k ν).upper i :=
      ⟨hx.1 i, hx.2 i⟩
    by_cases ha : 0 ≤ p.coefficient i
    · have ha' : 0 ≤ (p.coefficient i : ℝ) := by exact_mod_cast ha
      simpa only [Inequality.upperCorner, if_pos ha, Rat.cast_div, Rat.cast_add,
        Rat.cast_intCast, Rat.cast_natCast, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_upper, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left hxi.2 ha'
    · have ha' : (p.coefficient i : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge ha))
      simpa only [Inequality.upperCorner, if_neg ha, Rat.cast_div, Rat.cast_intCast,
        Rat.cast_natCast, Rat.cast_add, Rat.cast_one, cell,
        BoxIntegral.unitPartition.box_lower, Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonpos_left hxi.1 ha'

theorem lowerCorner_le_value {n : ℕ} (p : Inequality n) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) :
    (p.rationalValue (p.lowerCorner k ν) : ℝ) ≤ p.value x := by
  first
  | have h := value_le_upperCorner (negative p) k ν hx
    rw [← Inequality.value_cast, negative_value, negative_value] at h
    rw [← p.value_cast]
    exact neg_le_neg_iff.mp h

def solutionSet {n : ℕ} (S : List (Inequality n)) : Set (Fin n → ℝ) :=
  {x | Satisfies S x}

theorem isClosed_solutionSet {n : ℕ} (S : List (Inequality n)) :
    IsClosed (solutionSet S) := by
  first
  | have heq : solutionSet S =
        ⋂ p : Inequality n, ⋂ (_ : p ∈ S), {x | p.value x ≤ (p.bound : ℝ)} := by
      first
      | ext x
        simp only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun p => isClosed_iInter fun _ : p ∈ S =>
      isClosed_le p.continuous_value (continuous_const : Continuous (fun _ : Fin n → ℝ => (p.bound : ℝ)))

theorem convex_solutionSet {n : ℕ} (S : List (Inequality n)) :
    Convex ℝ (solutionSet S) := by
  first
  | intro x hx y hy a b ha hb hab p hp
    have hpX := hx p hp
    have hpY := hy p hp
    have heq : p.value (a • x + b • y) = a * p.value x + b * p.value y := by
      first
      | simp only [Inequality.value, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change p.value (a • x + b • y) ≤ (p.bound : ℝ)
    rw [heq]
    calc
      _ ≤ a * (p.bound : ℝ) + b * (p.bound : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hpX ha) (mul_le_mul_of_nonneg_left hpY hb)
      _ = (p.bound : ℝ) := by rw [← add_mul, hab, one_mul]

def innerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.upperCorner k ν) ≤ p.bound

def outerTest {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) : Prop :=
  ∀ p ∈ S, p.rationalValue (p.lowerCorner k ν) ≤ p.bound

instance innerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (innerTest S k ν) := by unfold innerTest; infer_instance

instance outerTest_decidable {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    Decidable (outerTest S k ν) := by unfold outerTest; infer_instance

theorem innerTest_iff {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ) :
    innerTest S k ν ↔ BoxIntegral.Box.Icc (cell k ν) ⊆ solutionSet S := by
  first
  | constructor
    · intro h x hx p hp
      apply (value_le_upperCorner p k ν hx).trans
      exact_mod_cast h p hp
    · intro h p hp
      have hv := h (upperCorner_mem p k ν) p hp
      rw [Inequality.Holds, Inequality.value_cast] at hv
      exact_mod_cast hv

theorem outerTest_of_mem {n : ℕ} (S : List (Inequality n)) (k : ℕ) (ν : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ BoxIntegral.Box.Icc (cell k ν)) (hs : x ∈ solutionSet S) :
    outerTest S k ν := by
  first
  | intro p hp
    have h := (lowerCorner_le_value p k ν hx).trans (hs p hp)
    exact_mod_cast h

def innerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (innerTest S k)

def outerIndices {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : Finset (Fin n → ℤ) :=
  (gridIndices n R k).filter (outerTest S k)

noncomputable def gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) : Set (Fin n → ℝ) :=
  ⋃ ν ∈ A, (cell k ν : Set (Fin n → ℝ))

theorem measurableSet_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    MeasurableSet (gridUnion k A) := by
  first
  | exact Finset.measurableSet_biUnion A (fun ν _ => (cell k ν).measurableSet_coe)

theorem mem_gridUnion_iff {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) (x : Fin n → ℝ) :
    x ∈ gridUnion k A ↔ BoxIntegral.unitPartition.index (k + 1) x ∈ A := by
  first
  | simp only [gridUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨ν, hν, hx⟩
      have heq := BoxIntegral.unitPartition.mem_box_iff_index.mp hx
      rw [heq]
      exact hν
    · intro h
      exact ⟨_, h, BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl⟩

theorem gridUnion_subset_ambient {n R k : ℕ} {A : Finset (Fin n → ℤ)}
    (hA : A ⊆ gridIndices n R k) : gridUnion k A ⊆ ambientBox n R := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (mem_gridIndices_iff ν).mp (hA hν) hx

theorem volume_gridUnion {n : ℕ} (k : ℕ) (A : Finset (Fin n → ℤ)) :
    volume.real (gridUnion k A) = (A.card : ℝ) / ((k : ℝ) + 1) ^ n := by
  first
  | rw [gridUnion, measureReal_biUnion_finset
      (h := fun ν _ ↦ (cell k ν).isBounded.measure_lt_top.ne)]
    · simp [measureReal_def, cell, BoxIntegral.unitPartition.volume_box,
        div_eq_mul_inv, ENNReal.toReal_add]
    · intro ν hν ν' hν' hne
      exact BoxIntegral.unitPartition.disjoint.mp hne
    · intro ν hν
      exact (cell k ν).measurableSet_coe

def lowerVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((innerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

def upperVolume {n : ℕ} (S : List (Inequality n)) (R k : ℕ) : ℚ :=
  ((outerIndices S R k).card : ℚ) / ((k : ℚ) + 1) ^ n

theorem lowerVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (lowerVolume S R k : ℝ) = volume.real (gridUnion k (innerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [lowerVolume]

theorem upperVolume_eq {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    (upperVolume S R k : ℝ) = volume.real (gridUnion k (outerIndices S R k)) := by
  first
  | rw [volume_gridUnion]
    simp [upperVolume]

theorem innerUnion_subset {n : ℕ} (S : List (Inequality n)) (R k : ℕ) :
    gridUnion k (innerIndices S R k) ⊆ solutionSet S := by
  first
  | intro x hx
    simp only [gridUnion, Set.mem_iUnion] at hx
    obtain ⟨ν, hν, hx⟩ := hx
    exact (innerTest_iff S k ν).mp (Finset.mem_filter.mp hν).2
      (BoxIntegral.Box.coe_subset_Icc hx)

theorem subset_outerUnion {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    solutionSet S ⊆ gridUnion k (outerIndices S R k) := by
  first
  | intro x hx
    rw [mem_gridUnion_iff]
    exact Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound hx),
      outerTest_of_mem S k _ (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl)) hx⟩

theorem volume_bounds {n : ℕ} (S : List (Inequality n)) (R k : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    (lowerVolume S R k : ℝ) ≤ volume.real (solutionSet S) ∧
      volume.real (solutionSet S) ≤ (upperVolume S R k : ℝ) := by
  first
  | rw [lowerVolume_eq, upperVolume_eq]
    constructor
    · exact measureReal_mono (innerUnion_subset S R k)
        ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    · exact measureReal_mono (subset_outerUnion S R k hbound)
        ((ambientBox n R).isBounded.subset
          (gridUnion_subset_ambient (Finset.filter_subset _ _))).measure_lt_top.ne

theorem eventually_mem_innerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) {x : Fin n → ℝ}
    (hx : x ∈ interior (solutionSet S)) :
    ∀ᶠ k in atTop, x ∈ gridUnion k (innerIndices S R k) := by
  first
  | obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)
    filter_upwards [hevent] with k hk
    rw [mem_gridUnion_iff]
    refine Finset.mem_filter.mpr ⟨index_mem_gridIndices (hbound (interior_subset hx)), ?_⟩
    rw [innerTest_iff]
    intro y hy
    apply interior_subset (hball ?_)
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) hy
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hk)

theorem lowerCorner_index_tendsto {n : ℕ} (p : Inequality n) (x : Fin n → ℝ) :
    Tendsto (fun k => fun i =>
      (p.lowerCorner k (BoxIntegral.unitPartition.index (k + 1) x) i : ℝ)) atTop (𝓝 x) := by
  first
  | apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε))
    refine ⟨N, fun k hk => ?_⟩
    apply (dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc _) (lowerCorner_mem p k _)
      (BoxIntegral.Box.coe_subset_Icc
        (BoxIntegral.unitPartition.mem_box_iff_index.mpr rfl))).trans_lt
    exact (BoxIntegral.unitPartition.diam_boxIcc (k + 1) _).trans_lt (by simpa using hN k hk)

theorem eventually_notMem_outerUnion {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    {x : Fin n → ℝ} (hx : x ∉ solutionSet S) :
    ∀ᶠ k in atTop, x ∉ gridUnion k (outerIndices S R k) := by
  first
  | obtain ⟨p, hp, hpx⟩ : ∃ p ∈ S, (p.bound : ℝ) < p.value x := by
      first
      | simpa only [solutionSet, Set.mem_setOf_eq, Satisfies, Inequality.Holds,
          not_forall, not_le, exists_prop] using hx
    have hevent := (p.continuous_value.tendsto x |>.comp (lowerCorner_index_tendsto p x)).eventually
      (lt_mem_nhds hpx)
    filter_upwards [hevent] with k hk hxk
    rw [mem_gridUnion_iff] at hxk
    have htest := (Finset.mem_filter.mp hxk).2 p hp
    dsimp only [Function.comp_def] at hk
    rw [Inequality.value_cast] at hk
    exact (not_lt_of_ge (by exact_mod_cast htest)) hk

theorem tendsto_volume_bounds {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) :
    Tendsto (fun k => (lowerVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) ∧
    Tendsto (fun k => (upperVolume S R k : ℝ)) atTop (𝓝 (volume.real (solutionSet S))) := by
  first
  | have hfinite : volume (solutionSet S) ≠ ⊤ :=
      ((ambientBox n R).isBounded.subset hbound).measure_lt_top.ne
    have hnull := (convex_solutionSet S).addHaar_frontier volume
    have hae : ∀ᵐ x ∂volume, x ∉ frontier (solutionSet S) :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    have hinner : Tendsto (fun k => volume (gridUnion k (innerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · have hxi := (mem_interior_iff_notMem_frontier hxS).mpr hx
            filter_upwards [eventually_mem_innerUnion S R hbound hxi] with k hk
            exact iff_of_true hk hxS
          · exact Eventually.of_forall (fun k => iff_of_false
              (fun h => hxS (innerUnion_subset S R k h)) hxS)
    have houter : Tendsto (fun k => volume (gridUnion k (outerIndices S R k)))
        atTop (𝓝 (volume (solutionSet S))) := by
      first
      | apply tendsto_measure_of_ae_tendsto_indicator atTop (isClosed_solutionSet S).measurableSet
          (fun k => measurableSet_gridUnion k _) (ambientBox n R).measurableSet_coe
          (ambientBox n R).isBounded.measure_lt_top.ne
        · exact Eventually.of_forall (fun k => gridUnion_subset_ambient (Finset.filter_subset _ _))
        · filter_upwards [hae] with x hx
          by_cases hxS : x ∈ solutionSet S
          · exact Eventually.of_forall (fun k => iff_of_true (subset_outerUnion S R k hbound hxS) hxS)
          · filter_upwards [eventually_notMem_outerUnion S R hxS] with k hk
            exact iff_of_false hk hxS
    constructor
    · simpa only [Function.comp_def, lowerVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp hinner
    · simpa only [Function.comp_def, upperVolume_eq, measureReal_def] using
        (ENNReal.tendsto_toReal hfinite).comp houter

theorem exists_gap_lt {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    ∃ k, upperVolume S R k - lowerVolume S R k < ε := by
  first
  | have he : 0 < (ε : ℝ) := by exact_mod_cast hε
    have h := (tendsto_volume_bounds S R hbound).2.sub (tendsto_volume_bounds S R hbound).1
    rw [sub_self] at h
    obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds he)).exists
    exact ⟨k, by exact_mod_cast hk⟩

/-- A terminating rational-arithmetic search, using only the proved existence
of an accepted index as its termination certificate. -/
def approximateVolume {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  lowerVolume S R (Nat.find (exists_gap_lt S R hbound ε hε))

theorem approximateVolume_correct {n : ℕ} (S : List (Inequality n)) (R : ℕ)
    (hbound : solutionSet S ⊆ ambientBox n R) (ε : ℚ) (hε : 0 < ε) :
    |(approximateVolume S R hbound ε hε : ℝ) - volume.real (solutionSet S)| < (ε : ℝ) := by
  first
  | let k := Nat.find (exists_gap_lt S R hbound ε hε)
    have hk := Nat.find_spec (exists_gap_lt S R hbound ε hε)
    have hb := volume_bounds S R k hbound
    have hg : (upperVolume S R k : ℝ) - (lowerVolume S R k : ℝ) < (ε : ℝ) := by
      first
      | exact_mod_cast hk
    change |(lowerVolume S R k : ℝ) - volume.real (solutionSet S)| < (ε : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hb.1)]
    linarith

end VolumePolynomials.RationalElimination
