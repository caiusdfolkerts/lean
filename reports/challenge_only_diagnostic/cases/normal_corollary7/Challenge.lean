module
public import Mathlib
/-! Exact standalone statement of Corollary7, paper.pdf p7.
A labelled crosspolytope is specified by its actual extreme points and every
nonempty proper exposed face. This is its full labelled face lattice, including
which two labels are opposite. No central symmetry or distinctness is assumed.
This report candidate is not a submitted or verified entry. -/
@[expose] public section
noncomputable section
namespace PalomarNormalCorollary7
abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Label (d : ℕ) := Fin d ⊕ Fin d
/-- The actual convex hull of all the supplied paired points. -/
def hull {d : ℕ} (v : Label d → Space d) : Set (Space d) :=
  convexHull ℝ (Set.range v)
/-- No subset contains both labels from a prescribed opposite pair. -/
def PairFree {d : ℕ} (S : Finset (Label d)) : Prop :=
  ∀ i : Fin d, ¬(Sum.inl i ∈ S ∧ Sum.inr i ∈ S)
/-- A nonempty proper exposed face of the actual convex body. -/
def ProperExposedFace {d : ℕ} (K F : Set (Space d)) : Prop :=
  F.Nonempty ∧ F ≠ K ∧
    ∃ (ℓ : Space d →ₗ[ℝ] ℝ) (a : ℝ), ℓ ≠ 0 ∧
      (∀ x ∈ K, ℓ x ≤ a) ∧ F = {x ∈ K | ℓ x = a}
/-- The exact labelled crosspolytope conclusion: all and only the displayed
vertices, with every proper face choosing at most one point from each pair. -/
def LabelledCrosspolytope {d : ℕ} (v : Label d → Space d) : Prop :=
  Function.Injective v ∧ (hull v).extremePoints ℝ = Set.range v ∧
    ∀ F : Set (Space d), ProperExposedFace (hull v) F ↔
      ∃ S : Finset (Label d), S.Nonempty ∧ PairFree S ∧
        F = convexHull ℝ (v '' (S : Set (Label d)))
/-- Corollary7, with literal full dimensionality and open paired segments.
The dimension-zero case is retained; its hypotheses are inconsistent. -/
theorem paired_segment_crosspolytope (d : ℕ) (v : Label d → Space d)
    (hfull : (interior (hull v)).Nonempty)
    (hpair : ∀ i : Fin d,
      (openSegment ℝ (v (Sum.inl i)) (v (Sum.inr i)) ∩ interior (hull v)).Nonempty) :
    LabelledCrosspolytope v := by
  sorry
end PalomarNormalCorollary7
