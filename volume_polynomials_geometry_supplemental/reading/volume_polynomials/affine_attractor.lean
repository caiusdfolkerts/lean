module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Abel

@[expose] public section
noncomputable section

/-! Uniqueness of compact attractors for a linear map whose powers tend to zero.
The argument retains the exact set-valued affine equation; it uses no convexity,
no support-function representation, and no unproved contraction assumption. -/

namespace VolumePolynomials

open scoped Topology Pointwise
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem fixed_sets_finite_matching (A : E →L[ℝ] E)
    (S K L : Set E) (hK : K = S + A '' K) (hL : L = S + A '' L)
    (z₀ : E) (hz₀ : z₀ ∈ L) :
    ∀ n : ℕ, ∀ x ∈ K, ∃ z ∈ L, ∃ y ∈ K, x = z + (A ^ n) (y - z₀) := by
  first
  | intro n
    induction n with
    | zero =>
        intro x hx
        refine ⟨z₀, hz₀, x, hx, ?_⟩
        simp
    | succ n ih =>
        intro x hx
        rw [hK] at hx
        obtain ⟨s, hs, w, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_add.mp hx
        obtain ⟨z, hz, q, hq, heq⟩ := ih y hy
        refine ⟨s + A z, ?_, q, hq, ?_⟩
        · rw [hL]
          exact Set.mem_add.mpr ⟨s, hs, A z, ⟨z, hz, rfl⟩, rfl⟩
        · rw [heq, map_add, pow_succ', ContinuousLinearMap.mul_apply]
          abel

private theorem compact_fixed_subset (A : E →L[ℝ] E)
    (hA : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0))
    (S K L : Set E) (hKcompact : IsCompact K) (hLclosed : IsClosed L)
    (hLnonempty : L.Nonempty) (hK : K = S + A '' K) (hL : L = S + A '' L) :
    K ⊆ L := by
  first
  | obtain ⟨z₀, hz₀⟩ := hLnonempty
    obtain ⟨R, hRpos, hR⟩ := hKcompact.isBounded.exists_pos_norm_le
    intro x hx
    choose z hz y hy heq using
      fun n => fixed_sets_finite_matching A S K L hK hL z₀ hz₀ n x hx
    have hbound (n : ℕ) : ‖x - z n‖ ≤ ‖A ^ n‖ * (R + ‖z₀‖) := by
      calc
        ‖x - z n‖ = ‖(A ^ n) (y n - z₀)‖ := by rw [heq n]; simp
        _ ≤ ‖A ^ n‖ * ‖y n - z₀‖ := (A ^ n).le_opNorm _
        _ ≤ ‖A ^ n‖ * (R + ‖z₀‖) :=
          mul_le_mul_of_nonneg_left
            ((norm_sub_le _ _).trans (add_le_add (hR _ (hy n)) le_rfl)) (norm_nonneg _)
    have hzero : Tendsto (fun n => x - z n) atTop (𝓝 0) :=
      squeeze_zero_norm hbound (by simpa using hA.mul_const (R + ‖z₀‖))
    have hzconv : Tendsto z atTop (𝓝 x) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hzero)
    exact hLclosed.mem_of_tendsto hzconv (Eventually.of_forall hz)

/-- Two nonempty compact solutions to the same affine Minkowski equation coincide
when the powers of its linear part converge to zero in operator norm. -/
theorem compact_affine_fixed_unique (A : E →L[ℝ] E)
    (hA : Tendsto (fun n : ℕ => ‖A ^ n‖) atTop (𝓝 0))
    (S K L : Set E) (hKcompact : IsCompact K) (hLcompact : IsCompact L)
    (hKnonempty : K.Nonempty) (hLnonempty : L.Nonempty)
    (hK : K = S + A '' K) (hL : L = S + A '' L) : K = L := by
  first
  | apply Set.Subset.antisymm
    · exact compact_fixed_subset A hA S K L hKcompact hLcompact.isClosed hLnonempty hK hL
    · exact compact_fixed_subset A hA S L K hLcompact hKcompact.isClosed hKnonempty hL hK

end VolumePolynomials
