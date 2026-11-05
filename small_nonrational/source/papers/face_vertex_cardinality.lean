module
public import Papers.HomogeneousSpanDimension
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Dimension bounds from the actual vertices of a face

A nonempty set of affine dimension r cannot lie in the convex hull of
fewer than r + 1 points.  The result is also provided for injective affine
images, which is the form needed when an exposed Minkowski face contains
a translated face of a summand.  The containing finite set is explicit;
it must be identified with the actual face vertices in the application.
-/

namespace Papers.FaceVertexCardinality

open Set Module
open Papers.HomogeneousSpanDimension

variable {E F : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

theorem liftSpan_mono {S T : Set E} (h : S ⊆ T) :
    liftSpan S ≤ liftSpan T :=
  Submodule.span_mono (Set.image_mono h)

theorem liftSpan_convexHull (S : Set E) :
    liftSpan (convexHull ℝ S) = liftSpan S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    have hconv : Convex ℝ {y : E | liftPoint y ∈ liftSpan S} := by
      intro y hy z hz a b ha hb hab
      change liftPoint (a • y + b • z) ∈ liftSpan S
      have heq : liftPoint (a • y + b • z) =
          a • liftPoint y + b • liftPoint z := by
        apply Prod.ext
        · rfl
        · change (1 : ℝ) = a * 1 + b * 1
          simpa only [mul_one] using hab.symm
      rw [heq]
      exact (liftSpan S).add_mem ((liftSpan S).smul_mem a hy)
        ((liftSpan S).smul_mem b hz)
    exact convexHull_min (fun y hy => liftPoint_mem hy) hconv hx
  · exact liftSpan_mono (subset_convexHull ℝ S)

theorem finrank_vectorSpan_affineImage
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f.linear) (S : Set E) :
    finrank ℝ (vectorSpan ℝ (f '' S)) =
      finrank ℝ (vectorSpan ℝ S) := by
  rw [← AffineMap.map_vectorSpan f]
  have hinj : Function.Injective
      (f.linear.comp (vectorSpan ℝ S).subtype) :=
    hf.comp Subtype.val_injective
  have h := LinearMap.finrank_range_of_inj hinj
  have hrange : (f.linear.comp (vectorSpan ℝ S).subtype).range =
      (vectorSpan ℝ S).map f.linear := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange] at h
  exact h

variable [FiniteDimensional ℝ E]

theorem finrank_liftSpan_finset_le_card (X : Finset E) :
    finrank ℝ (liftSpan (X : Set E)) ≤ X.card := by
  classical
  have h := finrank_span_finset_le_card (R := ℝ) (X.image liftPoint)
  change finrank ℝ (Submodule.span ℝ ((X.image liftPoint : Finset (E × ℝ)) : Set (E × ℝ))) ≤
    (X.image liftPoint).card at h
  have hset : ((X.image liftPoint : Finset (E × ℝ)) : Set (E × ℝ)) =
      liftPoint '' (X : Set E) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  rw [hset] at h
  have h' : finrank ℝ (liftSpan (X : Set E)) ≤
      (X.image liftPoint).card := by
    exact h
  exact h'.trans Finset.card_image_le

theorem dimension_add_one_le_card_of_subset_hull
    {S : Set E} (hS : S.Nonempty) (X : Finset E)
    (hSX : S ⊆ convexHull ℝ (X : Set E)) :
    finrank ℝ (vectorSpan ℝ S) + 1 ≤ X.card := by
  calc
    finrank ℝ (vectorSpan ℝ S) + 1 =
        finrank ℝ (liftSpan S) := (finrank_liftSpan hS).symm
    _ ≤ finrank ℝ (liftSpan (convexHull ℝ (X : Set E))) :=
      Submodule.finrank_mono (liftSpan_mono hSX)
    _ = finrank ℝ (liftSpan (X : Set E)) := by rw [liftSpan_convexHull]
    _ ≤ X.card := finrank_liftSpan_finset_le_card X

variable [FiniteDimensional ℝ F]

theorem dimension_add_one_le_card_of_affineImage_subset_hull
    {S : Set E} (hS : S.Nonempty)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f.linear)
    (X : Finset F) (hSX : f '' S ⊆ convexHull ℝ (X : Set F)) :
    finrank ℝ (vectorSpan ℝ S) + 1 ≤ X.card := by
  have h := dimension_add_one_le_card_of_subset_hull
    (hS.image f) X hSX
  simpa only [finrank_vectorSpan_affineImage f hf] using h

end Papers.FaceVertexCardinality
