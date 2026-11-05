module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega

/-!
# Selecting a scale from maximal minors

This is the finite scalar step in the maximal-minor alternative to the proof of
Theorem 3.1. The sequence `d j` is intended to be the largest absolute `j`-minor;
the theorem only needs its nonnegativity and `d 0 = 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
open Finset

namespace ProjectionVolumes

/-- A finite family of minor bounds admits a scale and an active order below
`k`, with exact equality at that order and weak bounds at every smaller order. -/
theorem exists_minor_scale {k : ℕ} (hk : 0 < k)
    (d : ℕ → ℝ) (hd : ∀ j < k, 0 ≤ d j) (hzero : d 0 = 1) :
    ∃ r < k, ∃ g : ℝ, 1 ≤ g ∧
      d r = g ^ (k - r) ∧
      (∀ j < k, d j ≤ g ^ (k - j)) := by
  let root : ℕ → ℝ := fun j => (d j) ^ ((k - j : ℕ) : ℝ)⁻¹
  obtain ⟨r, hr, hmax⟩ :=
    Finset.exists_max_image (Finset.range k) root (Finset.nonempty_range_iff.mpr hk.ne')
  have hrk : r < k := Finset.mem_range.mp hr
  have hg : 1 ≤ root r := by
    have h := hmax 0 (Finset.mem_range.mpr hk)
    simpa only [root, hzero, Real.one_rpow] using h
  refine ⟨r, hrk, root r, hg, ?_, ?_⟩
  · exact (Real.rpow_inv_natCast_pow (hd r hrk) (by omega)).symm
  · intro j hj
    calc
      d j = root j ^ (k - j) :=
        (Real.rpow_inv_natCast_pow (hd j hj) (by omega)).symm
      _ ≤ root r ^ (k - j) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (hd j hj) _) (hmax j (Finset.mem_range.mpr hj)) _

/-- The chosen pivot determinant is strictly positive, even if some other
minor maxima vanish. -/
lemma active_minor_pos {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hg : 1 ≤ g) (hexact : d r = g ^ (k - r)) : 0 < d r := by
  rw [hexact]
  exact pow_pos (lt_of_lt_of_le zero_lt_one hg) _

/-- The cofactor bound needed for the inverse pivot block. -/
lemma previous_minor_le {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hr : 0 < r) (hrk : r < k)
    (hexact : d r = g ^ (k - r))
    (hmax : ∀ j < k, d j ≤ g ^ (k - j)) : d (r - 1) ≤ g * d r := by
  have h := hmax (r - 1) (by omega)
  have he : k - (r - 1) = (k - r) + 1 := by omega
  simpa only [he, pow_succ, ← hexact, mul_comm] using h

/-- The bordered-minor bound needed for the Schur complement, away from its
last possible order. -/
lemma next_minor_le {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hg : 0 ≤ g) (hrk : r + 1 < k)
    (hexact : d r = g ^ (k - r))
    (hmax : ∀ j < k, d j ≤ g ^ (k - j)) : g * d (r + 1) ≤ d r := by
  have h := mul_le_mul_of_nonneg_left (hmax (r + 1) hrk) hg
  have he : k - r = (k - (r + 1)) + 1 := by omega
  calc
    g * d (r + 1) ≤ g * g ^ (k - (r + 1)) := h
    _ = g ^ (k - r) := by rw [he, pow_succ, mul_comm]
    _ = d r := hexact.symm

/-- At the last possible pivot order, the pivot determinant equals the scale. -/
lemma last_active_minor_eq_scale {k r : ℕ} {d : ℕ → ℝ} {g : ℝ}
    (hr : r + 1 = k) (hexact : d r = g ^ (k - r)) : d r = g := by
  have he : k - r = 1 := by omega
  simpa only [he, pow_one] using hexact

end ProjectionVolumes
