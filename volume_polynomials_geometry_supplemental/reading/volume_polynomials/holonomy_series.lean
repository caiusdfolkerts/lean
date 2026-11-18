module

public import VolumePolynomials.Holonomy
public import VolumePolynomials.MinkowskiSeries
public import VolumePolynomials.AffineAttractor
public import VolumePolynomials.ExposedSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section

/-! The actual compact convex Minkowski series of Theorem 7.3. -/

namespace VolumePolynomials.Holonomy

open scoped Topology Pointwise
open Set Filter

/-- The contraction times the prescribed return map. -/
def scaledReturn (lam : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := lam • returnContinuous

/-- Generating vectors of the infinite Minkowski sum in equation (7.10). -/
def weightedOrbit (lam : ℝ) (n : ℕ) : ℝ × ℝ := lam ^ n • orbit n

theorem weightedOrbit_recurrence (lam : ℝ) (n : ℕ) :
    weightedOrbit lam (n + 1) = scaledReturn lam (weightedOrbit lam n) := by
  first
  | simp only [weightedOrbit, scaledReturn, ContinuousLinearMap.smul_apply,
      map_smul, returnContinuous_apply, orbit_succ, pow_succ, smul_smul]

theorem weightedOrbit_summable (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    Summable fun n => ‖weightedOrbit lam n‖ := by
  first
  | apply ((summable_geometric_of_lt_one hlam₀ hlam₁).mul_left 2).of_norm_bounded
    intro n
    rw [norm_norm, weightedOrbit, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlam₀ n)]
    exact (mul_le_mul_of_nonneg_left (orbit_norm_le n) (pow_nonneg hlam₀ n)).trans_eq
      (mul_comm _ _)

theorem return_pow_apply (n : ℕ) (p : ℝ × ℝ) :
    (returnContinuous ^ n) p = p.1 • orbit n - p.2 • orbit (n + 1) := by
  first
  | induction n with
    | zero =>
        ext <;> simp [orbit, returnMap]
    | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_sub, map_smul, map_smul]
        rfl

theorem return_pow_norm_le (n : ℕ) : ‖returnContinuous ^ n‖ ≤ 4 := by
  first
  | apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro p
    rw [return_pow_apply]
    calc
      ‖p.1 • orbit n - p.2 • orbit (n + 1)‖
        ≤ ‖p.1 • orbit n‖ + ‖p.2 • orbit (n + 1)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖p.1‖ + 2 * ‖p.2‖ := by
        simp only [norm_smul]
        have h₁ := mul_le_mul_of_nonneg_left (orbit_norm_le n) (norm_nonneg p.1)
        have h₂ := mul_le_mul_of_nonneg_left (orbit_norm_le (n + 1)) (norm_nonneg p.2)
        nlinarith
      _ ≤ 4 * ‖p‖ := by
        have h₁ : ‖p.1‖ ≤ ‖p‖ := le_max_left _ _
        have h₂ : ‖p.2‖ ≤ ‖p‖ := le_max_right _ _
        linarith

theorem scaledReturn_pow_norm_le (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    ‖scaledReturn lam ^ n‖ ≤ 4 * lam ^ n := by
  first
  | rw [scaledReturn, smul_pow, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlam n)]
    exact (mul_le_mul_of_nonneg_left (return_pow_norm_le n) (pow_nonneg hlam n)).trans_eq
      (mul_comm _ _)

theorem scaledReturn_powers_tendsto_zero (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    Tendsto (fun n : ℕ => ‖scaledReturn lam ^ n‖) atTop (𝓝 0) := by
  first
  | apply squeeze_zero (fun n => norm_nonneg _) (scaledReturn_pow_norm_le lam hlam₀)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam₀ hlam₁).const_mul 4

/-- The compact convex set Kλ, defined by the actual infinite segment sum. -/
noncomputable def forcedBody (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) : ConvexBody (ℝ × ℝ) :=
  segmentSeriesBody (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁)

@[simp] theorem forcedBody_carrier (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) = segmentSeries (weightedOrbit lam) := rfl

/-- The exact functional equation of equation (7.10), on actual subsets of the plane. -/
theorem forcedBody_fixed (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) =
      centeredSegment (1, 0) + scaledReturn lam '' (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) := by
  first
  | simpa [weightedOrbit] using segmentSeries_fixed (scaledReturn lam) (weightedOrbit lam)
      (weightedOrbit_summable lam hlam₀ hlam₁) (weightedOrbit_recurrence lam)

/-- Uniqueness holds even among all nonempty compact sets, without assuming convexity. -/
theorem forcedBody_unique (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1)
    (K : Set (ℝ × ℝ)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hK : K = centeredSegment (1, 0) + scaledReturn lam '' K) :
    K = (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) :=
  compact_affine_fixed_unique (scaledReturn lam)
    (scaledReturn_powers_tendsto_zero lam hlam₀ hlam₁)
    (centeredSegment (1, 0)) K (forcedBody lam hlam₀ hlam₁)
    hKcompact (forcedBody lam hlam₀ hlam₁).isCompact
    hKnonempty (forcedBody lam hlam₀ hlam₁).nonempty
    hK (forcedBody_fixed lam hlam₀ hlam₁)

theorem det_smul (a b : ℝ) (p q : ℝ × ℝ) :
    det (a • p) (b • q) = a * b * det p q := by
  first
  | dsimp [det]
    ring

theorem weightedOrbit_nonparallel (lam : ℝ) (hlam : 0 < lam) (i j : ℕ) (hij : i ≠ j) :
    det (weightedOrbit lam i) (weightedOrbit lam j) ≠ 0 := by
  first
  | rw [weightedOrbit, weightedOrbit, det_smul]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero i hlam.ne') (pow_ne_zero j hlam.ne'))
      (det_orbit_ne_zero hij)

theorem weightedOrbit_ne_zero (lam : ℝ) (hlam : 0 < lam) (j : ℕ) : weightedOrbit lam j ≠ 0 := by
  first
  | intro hz
    have hn := weightedOrbit_nonparallel lam hlam j (j + 1) (by omega)
    simp [hz, det] at hn

/-- A support functional perpendicular to the j-th generating vector. -/
def orbitNormal (lam : ℝ) (j : ℕ) : (ℝ × ℝ) →L[ℝ] ℝ where
  toFun x := det (weightedOrbit lam j) x
  map_add' := by intro x y; dsimp [det]; ring
  map_smul' := by intro c x; dsimp [det]; ring
  cont := by dsimp [det]; fun_prop

@[simp] theorem orbitNormal_self (lam : ℝ) (j : ℕ) :
    orbitNormal lam j (weightedOrbit lam j) = 0 := by
  change det (weightedOrbit lam j) (weightedOrbit lam j) = 0
  dsimp [det]
  ring

theorem orbitNormal_positive_direction (lam : ℝ) (hlam : 0 < lam) (j : ℕ) :
    0 < orbitNormal lam j (-(weightedOrbit lam j).2, (weightedOrbit lam j).1) := by
  first
  | have hu : weightedOrbit lam j ≠ 0 := by
      exact weightedOrbit_ne_zero lam hlam j
    have hp : (weightedOrbit lam j).1 ≠ 0 ∨ (weightedOrbit lam j).2 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (Prod.ext h.1 h.2)
    change 0 < (weightedOrbit lam j).1 * (weightedOrbit lam j).1 -
      (weightedOrbit lam j).2 * (-(weightedOrbit lam j).2)
    rcases hp with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (weightedOrbit lam j).2]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (weightedOrbit lam j).1]

/-- For every j, an entire nontrivial segment in direction lam^j M^j e₁ lies in the frontier. -/
theorem forcedBody_boundary_segments (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃ a : ℕ → ℝ × ℝ, ∀ j t, t ∈ Icc (- (1/2 : ℝ)) (1/2 : ℝ) →
      a j + t • weightedOrbit lam j ∈ frontier (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
  first
  | have hseg (j : ℕ) := translated_segment_mem_frontier (orbitNormal lam j)
      (weightedOrbit lam) (weightedOrbit_summable lam hlam₀.le hlam₁) j (orbitNormal_self lam j)
      (-(weightedOrbit lam j).2, (weightedOrbit lam j).1)
      (orbitNormal_positive_direction lam hlam₀ j)
    choose a ha using hseg
    exact ⟨a, fun j t ht => ha j t ht.1 ht.2⟩

/-- Each displayed boundary segment is the entire exposed face. Its generator is nonzero,
and the generators are pairwise nonparallel by `weightedOrbit_nonparallel`. -/
theorem forcedBody_exposed_faces (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ∃ a : ℕ → ℝ × ℝ, ∀ j,
      (orbitNormal lam j).toExposed (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) =
        {x | ∃ t : Icc (- (1/2 : ℝ)) (1/2 : ℝ),
          x = a j + (t : ℝ) • weightedOrbit lam j} := by
  first
  | have hface (j : ℕ) := exposed_face_eq_centered_segment (orbitNormal lam j)
      (weightedOrbit lam) (weightedOrbit_summable lam hlam₀.le hlam₁) j (orbitNormal_self lam j)
      (fun n hn => weightedOrbit_nonparallel lam hlam₀ j n hn.symm)
    choose a ha using hface
    exact ⟨a, ha⟩

end VolumePolynomials.Holonomy
