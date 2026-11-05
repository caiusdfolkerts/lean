module

public import VolumePolynomials.ShapeConditions
public import VolumePolynomials.BodyOperations
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.SplitIfs

@[expose] public section
noncomputable section

open scoped Pointwise

namespace VolumePolynomials.ShapeConditions

theorem unitWeight_nonneg (i : Label) : ∀ j, (0 : ℝ) ≤ unitWeight i j := by
  first
  | intro j
    simp only [unitWeight]
    split <;> norm_num

theorem unitWeight_eq_single (i : Label) :
    (unitWeight i : Label → ℝ) = Pi.single i 1 := by
  first
  | funext j
    simp [unitWeight, Pi.single_apply]

theorem lastNumericalWeight_nonneg (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ i, 0 ≤ lastNumericalWeight lam i := by
  first
  | intro i
    exact add_nonneg (mul_nonneg hlam (unitWeight_nonneg bodyC i)) (unitWeight_nonneg e₁ i)

@[simp] theorem weightedSum_unitWeight (K : Label → Body 3) (i : Label) :
    weightedSum K (unitWeight i) = K i := by
  first
  | rw [unitWeight_eq_single, weightedSum_single, one_smul]

@[simp] theorem weightedSum_two (K : Label → Body 3) (i j : Label) :
    weightedSum K (unitWeight i + unitWeight j) = K i + K j := by
  first
  | rw [weightedSum_add K _ _ (unitWeight_nonneg i) (unitWeight_nonneg j),
      weightedSum_unitWeight, weightedSum_unitWeight]

@[simp] theorem weightedSum_three (K : Label → Body 3) (i j k : Label) :
    weightedSum K (unitWeight i + unitWeight j + unitWeight k) = K i + K j + K k := by
  first
  | rw [weightedSum_add K (unitWeight i + unitWeight j) (unitWeight k)
      (fun l => add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l))
      (unitWeight_nonneg k), weightedSum_two, weightedSum_unitWeight]

@[simp] theorem weightedSum_last (K : Label → Body 3) (lam : ℝ) (hlam : 0 ≤ lam) :
    weightedSum K (lastNumericalWeight lam) = lam • K bodyC + K e₁ := by
  first
  | have hweight : lastNumericalWeight lam =
        Pi.single bodyC lam + (unitWeight e₁ : Label → ℝ) := by
      funext i
      simp only [lastNumericalWeight, unitWeight, Pi.add_apply, Pi.single_apply]
      split <;> simp_all
    rw [hweight, weightedSum_add]
    · rw [weightedSum_single, weightedSum_unitWeight]
    · intro i
      simp only [Pi.single_apply]
      split <;> simp_all
    · exact unitWeight_nonneg e₁

theorem extrusionValue_volume (K : Label → Body 3) (w : Label → ℝ) (h : Label)
    (hw : ∀ i, 0 ≤ w i) :
    extrusionValue (volumeFunction K) w h =
      bodyVolume (weightedSum K w + K h) - bodyVolume (weightedSum K w) := by
  first
  | simp only [extrusionValue, volumeFunction]
    rw [weightedSum_add K _ _ hw (unitWeight_nonneg h), weightedSum_unitWeight]

theorem OrdinaryConditions.congr_nonnegative {lam a : ℝ}
    {V W : (Label → ℝ) → ℝ} (hlam : 0 ≤ lam)
    (hVW : ∀ w, (∀ i, 0 ≤ w i) → V w = W w) :
    OrdinaryConditions lam a V ↔ OrdinaryConditions lam a W := by
  first
  | have hunit (i : Label) : V (unitWeight i) = W (unitWeight i) :=
      hVW (unitWeight i) (unitWeight_nonneg i)
    have hpair (i j : Label) :
        V (unitWeight i + unitWeight j) = W (unitWeight i + unitWeight j) :=
      hVW (unitWeight i + unitWeight j)
        (fun k => add_nonneg (unitWeight_nonneg i k) (unitWeight_nonneg j k))
    have htriple (i j k : Label) :
        V (unitWeight i + unitWeight j + unitWeight k) =
          W (unitWeight i + unitWeight j + unitWeight k) :=
      hVW (unitWeight i + unitWeight j + unitWeight k)
        (fun l => add_nonneg
          (add_nonneg (unitWeight_nonneg i l) (unitWeight_nonneg j l))
          (unitWeight_nonneg k l))
    have hlast : V (lastNumericalWeight lam) = W (lastNumericalWeight lam) :=
      hVW (lastNumericalWeight lam) (lastNumericalWeight_nonneg lam hlam)
    have hlast_add (i : Label) :
        V (lastNumericalWeight lam + unitWeight i) =
          W (lastNumericalWeight lam + unitWeight i) :=
      hVW (lastNumericalWeight lam + unitWeight i)
        (fun k => add_nonneg (lastNumericalWeight_nonneg lam hlam k)
          (unitWeight_nonneg i k))
    have hadd_last (i : Label) :
        V (unitWeight i + lastNumericalWeight lam) =
          W (unitWeight i + lastNumericalWeight lam) :=
      hVW (unitWeight i + lastNumericalWeight lam)
        (fun k => add_nonneg (unitWeight_nonneg i k)
          (lastNumericalWeight_nonneg lam hlam k))
    have hadd_last_add (i j : Label) :
        V (unitWeight i + lastNumericalWeight lam + unitWeight j) =
          W (unitWeight i + lastNumericalWeight lam + unitWeight j) :=
      hVW (unitWeight i + lastNumericalWeight lam + unitWeight j)
        (fun k => add_nonneg
          (add_nonneg (unitWeight_nonneg i k) (lastNumericalWeight_nonneg lam hlam k))
          (unitWeight_nonneg j k))
    simp only [OrdinaryConditions, extrusionValue, hunit, hpair, htriple,
      hlast, hlast_add, hadd_last, hadd_last_add]

/-- Exact equivalence of symbolic coefficient tests and their literal geometric
volume evaluations, proved using only weights in the nonnegative orthant. -/
theorem holds_iff_ordinary_volume {lam a : ℝ} {c : Coefficients 9 3}
    {K : Label → Body 3} (hlam : 0 ≤ lam) (hK : Realizes K c) :
    Holds lam a c ↔ OrdinaryConditions lam a (volumeFunction K) := by
  first
  | rw [holds_iff_ordinary]
    exact OrdinaryConditions.congr_nonnegative hlam hK

theorem Holds.ordinary_volume {lam a : ℝ} {c : Coefficients 9 3}
    {K : Label → Body 3} (h : Holds lam a c) (hK : Realizes K c) :
    OrdinaryConditions lam a (volumeFunction K) :=
  (holds_iff_ordinary_volume h.parameter_range.1.le hK).mp h

end VolumePolynomials.ShapeConditions
