module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Exact shared canonical source, owned here for both the real and field branches. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/ENNRealTruncation.lean -/



/-! # Exact finite truncation of nonnegative extended-valued functions

These reusable order and monotone-integral facts retain both zero and infinity.
They contain no matrix-law or association assertion.
-/

noncomputable section
open MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace WishartVerification

def ennrealTruncation {E : Type*} (n : ℕ) (f : E → ℝ≥0∞) (x : E) : ℝ :=
  (min (f x) (n : ℝ≥0∞)).toReal

theorem ennrealTruncation_nonneg {E : Type*} (n : ℕ) (f : E → ℝ≥0∞) (x : E) :
    0 ≤ ennrealTruncation n f x := ENNReal.toReal_nonneg

theorem ofReal_ennrealTruncation {E : Type*} (n : ℕ) (f : E → ℝ≥0∞) (x : E) :
    ENNReal.ofReal (ennrealTruncation n f x) = min (f x) (n : ℝ≥0∞) := by
  apply ENNReal.ofReal_toReal
  exact ne_of_lt ((min_le_right _ _).trans_lt (by simp))

theorem measurable_ennrealTruncation {E : Type*} [MeasurableSpace E]
    (n : ℕ) {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (ennrealTruncation n f) :=
  (hf.min measurable_const).ennreal_toReal

theorem monotoneOn_ennrealTruncation {E : Type*} [Preorder E]
    (n : ℕ) {f : E → ℝ≥0∞} {s : Set E} (hf : MonotoneOn f s) :
    MonotoneOn (ennrealTruncation n f) s := by
  intro x hx y hy hxy
  exact ENNReal.toReal_mono
    (ne_of_lt ((min_le_right _ _).trans_lt (by simp)))
    (min_le_min_right _ (hf hx hy hxy))

theorem antitoneOn_ennrealTruncation {E : Type*} [Preorder E]
    (n : ℕ) {f : E → ℝ≥0∞} {s : Set E} (hf : AntitoneOn f s) :
    AntitoneOn (ennrealTruncation n f) s := by
  intro x hx y hy hxy
  exact ENNReal.toReal_mono
    (ne_of_lt ((min_le_right _ _).trans_lt (by simp)))
    (min_le_min_right _ (hf hx hy hxy))

theorem iSup_ennreal_min_nat (a : ℝ≥0∞) : (⨆ n : ℕ, min a (n : ℝ≥0∞)) = a := by
  apply iSup_eq_of_tendsto
  · intro n m hnm
    exact min_le_min_left _ (by exact_mod_cast hnm)
  · simpa only [min_eq_left le_top] using
      (tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top :
        Tendsto (fun n : ℕ => min a (n : ℝ≥0∞)) atTop (𝓝 (min a ∞)))

theorem lintegral_eq_iSup_ennrealTruncation {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (ennrealTruncation n f x) ∂μ := by
  simp_rw [ofReal_ennrealTruncation]
  rw [← lintegral_iSup (fun _ => hf.min measurable_const)]
  · simp only [iSup_ennreal_min_nat]
  · intro n m hnm x
    exact min_le_min_left _ (by exact_mod_cast hnm)

/-- Finite products commute with the diagonal supremum of increasing
nonnegative sequences, including zero and infinity. -/
theorem ennreal_prod_iSup_nat {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (f : ι → ℕ → ℝ≥0∞) (hf : ∀ i ∈ J, Monotone (f i)) :
    (∏ i ∈ J, ⨆ n : ℕ, f i n) = ⨆ n : ℕ, ∏ i ∈ J, f i n := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
      have hi' : Monotone (f i) := hf i (Finset.mem_insert_self _ _)
      have hJ : ∀ j ∈ J, Monotone (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, ih hJ, ENNReal.iSup_mul]
      simp_rw [ENNReal.mul_iSup, Finset.prod_insert hi]
      apply le_antisymm
      · apply iSup_le
        intro n
        apply iSup_le
        intro m
        calc
          f i n * (∏ j ∈ J, f j m) ≤
              f i (max n m) * (∏ j ∈ J, f j (max n m)) := by
            exact mul_le_mul' (hi' (le_max_left _ _))
              (Finset.prod_le_prod' fun j hj => hJ j hj (le_max_right _ _))
          _ ≤ ⨆ l : ℕ, f i l * (∏ j ∈ J, f j l) :=
            le_iSup (fun l : ℕ => f i l * (∏ j ∈ J, f j l)) (max n m)
      · apply iSup_le
        intro n
        exact le_iSup_of_le n (le_iSup_of_le n le_rfl)

end WishartVerification
end
end CanonicalSource0
