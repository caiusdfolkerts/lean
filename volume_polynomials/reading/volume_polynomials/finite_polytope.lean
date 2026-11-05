module

public import VolumePolynomials.PolytopeFaces
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Algebra.Group.Pointwise.Set.Finite

@[expose] public section
set_option autoImplicit false

/-!
# Finite convex hulls and their exposed faces

All operations below preserve the existence of an actual finite generating set.
Exposed faces remain finite convex hulls by Krein--Milman and the fact that an
extreme point of an exposed face is an extreme point of the original hull.
No general-position or full-dimensional hypothesis is needed.
-/

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsFiniteHull (C : Set E) : Prop := ∃ S : Set E, S.Finite ∧ C = convexHull ℝ S

theorem IsFiniteHull.isCompact {C : Set E} (hC : IsFiniteHull C) : IsCompact C := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact hS.isCompact_convexHull ℝ

theorem IsFiniteHull.convex {C : Set E} (hC : IsFiniteHull C) : Convex ℝ C := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact convex_convexHull ℝ S

theorem IsFiniteHull.finite_extremePoints {C : Set E} (hC : IsFiniteHull C) :
    (C.extremePoints ℝ).Finite := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact hS.subset extremePoints_convexHull_subset

theorem IsFiniteHull.singleton (x : E) : IsFiniteHull ({x} : Set E) := by
  first
  | exact ⟨{x}, finite_singleton x, (convexHull_singleton (𝕜 := ℝ) x).symm⟩

theorem IsFiniteHull.zero : IsFiniteHull (0 : Set E) := IsFiniteHull.singleton 0

theorem IsFiniteHull.affine_image {C : Set E} (hC : IsFiniteHull C)
    (f : E →ᵃ[ℝ] F) : IsFiniteHull (f '' C) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact ⟨f '' S, hS.image f, f.image_convexHull S⟩

theorem IsFiniteHull.linear_image {C : Set E} (hC : IsFiniteHull C)
    (f : E →ₗ[ℝ] F) : IsFiniteHull (f '' C) :=
  hC.affine_image f.toAffineMap

theorem IsFiniteHull.add {A B : Set E} (hA : IsFiniteHull A) (hB : IsFiniteHull B) :
    IsFiniteHull (A + B) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hA
    obtain ⟨T, hT, rfl⟩ := hB
    exact ⟨S + T, hS.add hT, (convexHull_add S T).symm⟩

theorem IsFiniteHull.smul {C : Set E} (hC : IsFiniteHull C) (r : ℝ) :
    IsFiniteHull (r • C) := by
  first
  | obtain ⟨S, hS, rfl⟩ := hC
    exact ⟨r • S, hS.image (fun x => r • x), (convexHull_smul r S).symm⟩

theorem IsFiniteHull.sum {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hC : ∀ i ∈ s, IsFiniteHull (C i)) : IsFiniteHull (∑ i ∈ s, C i) := by
  first
  | exact Finset.sum_induction C IsFiniteHull (fun _ _ ha hb => ha.add hb)
      IsFiniteHull.zero hC

theorem IsFiniteHull.weighted_sum {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hC : ∀ i ∈ s, IsFiniteHull (C i)) (t : ι → ℝ) :
    IsFiniteHull (∑ i ∈ s, t i • C i) :=
  IsFiniteHull.sum s _ (fun i hi => (hC i hi).smul (t i))

/-- A face may be empty or lower dimensional; both cases are included. -/
theorem IsFiniteHull.exposed {C : Set E} (hC : IsFiniteHull C) (l : E →L[ℝ] ℝ) :
    IsFiniteHull (l.toExposed C) := by
  first
  | have he : IsExposed ℝ C (l.toExposed C) := ContinuousLinearMap.toExposed.isExposed
    have hf : ((l.toExposed C).extremePoints ℝ).Finite :=
      hC.finite_extremePoints.subset he.isExtreme.extremePoints_subset_extremePoints
    have hclosed : IsClosed (convexHull ℝ ((l.toExposed C).extremePoints ℝ)) :=
      hf.isClosed_convexHull ℝ
    refine ⟨(l.toExposed C).extremePoints ℝ, hf, ?_⟩
    have h := closure_convexHull_extremePoints (he.isCompact hC.isCompact) (he.convex hC.convex)
    rw [hclosed.closure_eq] at h
    exact h.symm

theorem IsFiniteHull.exists_finset {C : Set E} (hC : IsFiniteHull C) :
    ∃ S : Finset E, C = convexHull ℝ (S : Set E) := by
  first
  | classical
    obtain ⟨S, hS, hC⟩ := hC
    exact ⟨hS.toFinset, by simpa using hC⟩

section Volume

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- A convex body with empty interior has zero ambient volume. -/
theorem volume_eq_zero_of_empty_interior {C : Set E} (hc : Convex ℝ C)
    (hC : interior C = ∅) : volume C = 0 := by
  first
  | have hspan : affineSpan ℝ C ≠ ⊤ := by
      intro h
      have hn := hc.interior_nonempty_iff_affineSpan_eq_top.mpr h
      rw [hC] at hn
      exact Set.not_nonempty_empty hn
    exact measure_mono_null (subset_affineSpan ℝ C)
      (Measure.addHaar_affineSubspace volume _ hspan)

end Volume
end VolumePolynomials.PolytopeGeometry
