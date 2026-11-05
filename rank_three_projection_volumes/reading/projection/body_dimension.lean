module

public import Projection.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual affine dimension and ambient interior

These statements connect the affine-span definition used in the
compactification theorem to the nonempty-interior hypothesis required by the
full-dimensional obstruction. Nonemptiness comes from the actual convex body;
no additional dimension or interior predicate is assumed.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set Module

namespace RankThreeProjection

/-- For an actual nonempty compact convex body, full affine dimension is
equivalent to nonempty ambient interior. -/
theorem affineSpan_direction_finrank_eq_iff_interior_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : ConvexBody E) :
    finrank ℝ (affineSpan ℝ (K : Set E)).direction = finrank ℝ E ↔
      (interior (K : Set E)).Nonempty := by
  have hspan : ((affineSpan ℝ (K : Set E)) : Set E).Nonempty :=
    K.nonempty.mono (subset_affineSpan ℝ (K : Set E))
  calc
    finrank ℝ (affineSpan ℝ (K : Set E)).direction = finrank ℝ E ↔
        (affineSpan ℝ (K : Set E)).direction = ⊤ :=
      Submodule.eq_top_iff_finrank_eq.symm
    _ ↔ affineSpan ℝ (K : Set E) = ⊤ :=
      AffineSubspace.direction_eq_top_iff_of_nonempty hspan
    _ ↔ (interior (K : Set E)).Nonempty :=
      K.convex.interior_nonempty_iff_affineSpan_eq_top.symm

/-- The affine dimension cannot exceed the actual coordinate-space dimension. -/
theorem bodyDimension_le {n : ℕ} (K : Body n) : bodyDimension K ≤ n := by
  have h := Submodule.finrank_le (affineSpan ℝ (K : Set (Space n))).direction
  simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

/-- The exact bridge from the compactification's dimension to the interior
hypothesis of the full-dimensional branch. -/
theorem bodyDimension_eq_iff_interior_nonempty {n : ℕ} (K : Body n) :
    bodyDimension K = n ↔ (interior (K : Set (Space n))).Nonempty := by
  simpa only [bodyDimension, Space, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using
      affineSpan_direction_finrank_eq_iff_interior_nonempty K

/-- Its complementary form supplies precisely the dimension deficit used to
translate a body into the kernel of a nonzero continuous linear functional. -/
theorem bodyDimension_lt_iff_interior_empty {n : ℕ} (K : Body n) :
    bodyDimension K < n ↔ interior (K : Set (Space n)) = ∅ := by
  constructor
  · intro hdim
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hfull
    exact (ne_of_lt hdim) ((bodyDimension_eq_iff_interior_nonempty K).mpr hfull)
  · intro hempty
    apply lt_of_le_of_ne (bodyDimension_le K)
    intro hdim
    have hfull := (bodyDimension_eq_iff_interior_nonempty K).mp hdim
    rw [hempty] at hfull
    exact Set.not_nonempty_empty hfull

end RankThreeProjection
