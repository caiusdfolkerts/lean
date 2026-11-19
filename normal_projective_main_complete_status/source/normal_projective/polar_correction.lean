module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! A counterexample to the stated hypothesis of the auxiliary polar-recentering
identity, not a counterexample to any principal theorem. The corrected identity
requires the origin to lie in the interior of the original body. -/

@[expose] public section
noncomputable section

namespace NormalProjective.PolarCorrection

def polar (K : Set ℝ) : Set ℝ := {y | ∀ x ∈ K, x * y ≤ 1}

def recentered (K : Set ℝ) (o : ℝ) : Set ℝ := (fun x => x - o) '' K

def fractionalRecenter (o x : ℝ) : ℝ := x / (1 - x * o)

theorem interval_polar_upper {x : ℝ} (hx : x ∈ polar (Set.Icc 0 1)) : x ≤ 1 := by
  have h := hx 1 (by norm_num)
  simpa using h

theorem missing_endpoint_mem :
    (-2 : ℝ) ∈ polar (recentered (Set.Icc 0 1) (1 / 2)) := by
  rintro x ⟨y, hy, rfl⟩
  rcases hy with ⟨hy0, hy1⟩
  nlinarith

theorem missing_endpoint_not_mem :
    (-2 : ℝ) ∉ fractionalRecenter (1 / 2) '' polar (Set.Icc 0 1) := by
  rintro ⟨x, hx, heq⟩
  have hx1 := interval_polar_upper hx
  have hd : (1 : ℝ) - x * (1 / 2) ≠ 0 := by linarith
  have h := (div_eq_iff hd).mp heq
  nlinarith

/-- A compact full-dimensional convex interval containing zero, with an interior
recentering point, violates the auxiliary identity if zero is allowed on its boundary. -/
theorem boundary_origin_counterexample :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧ Convex ℝ (Set.Icc (0 : ℝ) 1) ∧
    (0 : ℝ) ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ∈ interior (Set.Icc 0 1) ∧
    polar (recentered (Set.Icc 0 1) (1 / 2)) ≠
      fractionalRecenter (1 / 2) '' polar (Set.Icc 0 1) := by
  refine ⟨isCompact_Icc, convex_Icc _ _, by norm_num, ?_, ?_⟩
  · rw [interior_Icc]
    norm_num
  · intro heq
    exact missing_endpoint_not_mem (heq ▸ missing_endpoint_mem)

end NormalProjective.PolarCorrection
