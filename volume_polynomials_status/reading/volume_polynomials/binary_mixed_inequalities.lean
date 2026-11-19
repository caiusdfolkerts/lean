module

public import VolumePolynomials.BinaryMixedCoefficients
public import VolumePolynomials.MixedVolumeOrder
public import VolumePolynomials.AlexandrovFenchel
public import VolumePolynomials.BinarySequences
public import VolumePolynomials.OneBody
public import VolumePolynomials.RealizationContinuity

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Necessity of all binary coefficient inequalities

Alexandrov--Fenchel gives the adjacent inequalities for the exact repeated
mixed-volume coefficients. Adding a positive multiple of the unit cube
makes every coefficient positive, with positivity proved by inclusion and
actual diagonal volume. The separated-index inequalities pass to the
Hausdorff limit, so no internal-zero assumption is imposed on a realizing
tuple.
-/

open Set MeasureTheory Module Filter
open scoped Pointwise BigOperators Topology

namespace VolumePolynomials.BinaryMixed

open BinarySequences

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem coefficient_adjacent {n i : ℕ} (hdim : finrank ℝ E = n + 2)
    (A B : ConvexBody E) (hi : i ≤ n) :
    coefficient μ (n + 2) A B i * coefficient μ (n + 2) A B (i + 2) ≤
      coefficient μ (n + 2) A B (i + 1) ^ 2 := by
  first
  | let p := firstPattern n i
    let K := patternBody A B p
    have hAA : Fin.cons A (Fin.cons A K) = patternBody A B (Fin.cons false (Fin.cons false p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have hBB : Fin.cons B (Fin.cons B K) = patternBody A B (Fin.cons true (Fin.cons true p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have hAB : Fin.cons A (Fin.cons B K) = patternBody A B (Fin.cons false (Fin.cons true p)) := by
      first
      | funext j
        cases j using Fin.cases with
        | zero => simp [patternBody]
        | succ j =>
            cases j using Fin.cases with
            | zero => simp [patternBody]
            | succ j => rfl
    have h := mixedVolume_alexandrovFenchel μ hdim K A B
    rw [hAA, hBB, hAB, mixedVolume_pattern, mixedVolume_pattern, mixedVolume_pattern] at h
    simpa only [patternCount_cons, Bool.false_eq_true, if_false, if_true, zero_add,
      p, patternCount_first hi, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem coefficient_logconcave {d : ℕ} (hdim : finrank ℝ E = d)
    (A B : ConvexBody E) {i : ℕ} (hi : 1 ≤ i) (hid : i < d) :
    coefficient μ d A B (i - 1) * coefficient μ d A B (i + 1) ≤
      coefficient μ d A B i ^ 2 := by
  first
  | cases d with
    | zero => omega
    | succ d =>
        cases d with
        | zero => omega
        | succ n =>
            have h := coefficient_adjacent μ hdim A B (i := i - 1) (by omega)
            have h1 : i - 1 + 1 = i := by omega
            have h2 : i - 1 + 2 = i + 1 := by omega
            simpa only [h1, h2] using h

end Measure

def thickened {d : ℕ} (eps : ℝ) (A : Body d) : Body d := A + eps • unitCube d

theorem coefficient_pos_thickened {d : ℕ} (hd : 0 < d)
    (A B : Body d) {eps : ℝ} (heps : 0 < eps) (i : ℕ) :
    0 < coefficient volume d (thickened eps A) (thickened eps B) i := by
  first
  | cases d with
    | zero => omega
    | succ n =>
        obtain ⟨a, ha⟩ := A.nonempty
        obtain ⟨b, hb⟩ := B.nonempty
        let S : Body (n + 1) := eps • unitCube (n + 1)
        have hS : 0 < volume.real (S : Set (Space (n + 1))) := by
          first
          | change 0 < bodyVolume (eps • unitCube (n + 1))
            rw [bodyVolume_smul _ heps.le, bodyVolume_unitCube, mul_one]
            exact pow_pos heps _
        let p : Fin (n + 1) → Space (n + 1) :=
          fun j => if firstPattern (n + 1) i j = true then b else a
        apply mixedVolume_pos_of_common_body volume (by simp [Space])
          (patternBody (thickened eps A) (thickened eps B) (firstPattern (n + 1) i)) S hS p
        intro j
        by_cases hj : firstPattern (n + 1) i j = true
        · change translateBody (if firstPattern (n + 1) i j = true then b else a) S ≤ _
          rw [if_pos hj]
          simp only [patternBody, if_pos hj, thickened]
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hub : u = b := hu
          subst u
          exact ⟨b, hb, v, hv, rfl⟩
        · change translateBody (if firstPattern (n + 1) i j = true then b else a) S ≤ _
          rw [if_neg hj]
          simp only [patternBody, if_neg hj, thickened]
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hua : u = a := hu
          subst u
          exact ⟨a, ha, v, hv, rfl⟩

theorem thickened_criterion {d : ℕ} (hd : 0 < d) (A B : Body d)
    {eps : ℝ} (heps : 0 < eps) :
    Criterion d (coefficient volume d (thickened eps A) (thickened eps B)) := by
  first
  | apply criterion_iff.mpr
    refine ⟨fun i _ => coefficient_nonnegative volume d _ _ i, ?_, ?_⟩
    · intro i hi hid
      exact coefficient_logconcave volume (by simp [Space]) _ _ hi hid
    · intro i j k hij hjk hkd hi hk
      exact coefficient_pos_thickened hd A B heps j

theorem coefficient_thickened_tendsto (d i : ℕ) (A B : Body d) :
    Tendsto (fun eps : ℝ => coefficient volume d (thickened eps A) (thickened eps B) i)
      (𝓝[>] (0 : ℝ)) (𝓝 (coefficient volume d A B i)) := by
  first
  | have hc : Continuous (fun eps : ℝ => (thickened eps A, thickened eps B)) := by
      first
      | unfold thickened
        fun_prop
    have h := (((continuous_coefficient (volume : Measure (Space d)) d i).comp' hc).continuousAt (x := (0 : ℝ))).tendsto
    simpa only [Function.comp_def, thickened, body_zero_smul, add_zero] using h.mono_left nhdsWithin_le_nhds

/-- Every actual binary mixed-volume sequence satisfies all of (A.1),
including the separated-index inequalities at degenerate limits. -/
theorem coefficient_criterion {d : ℕ} (hd : 0 < d) (A B : Body d) :
    Criterion d (coefficient volume d A B) := by
  first
  | refine ⟨fun i _ => coefficient_nonnegative volume d A B i, ?_⟩
    intro i j hi hij hjd
    have hleft := (coefficient_thickened_tendsto d (i - 1) A B).mul
      (coefficient_thickened_tendsto d (j + 1) A B)
    have hright := (coefficient_thickened_tendsto d i A B).mul
      (coefficient_thickened_tendsto d j A B)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact (thickened_criterion hd A B heps).2 i j hi hij hjd

theorem criterion_of_realizes {d : ℕ} (hd : 0 < d) {a : ℕ → ℝ} {A B : Body d}
    (h : BinarySimplex.Realizes d a A B) : Criterion d a := by
  first
  | have heq := realizing_sequence_eq h
    have hc := coefficient_criterion hd A B
    constructor
    · intro i hid
      rw [heq i hid]
      exact hc.1 i hid
    · intro i j hi hij hjd
      rw [heq (i - 1) (by omega), heq (j + 1) (by omega),
        heq i (by omega), heq j (by omega)]
      exact hc.2 i j hi hij hjd

end VolumePolynomials.BinaryMixed
