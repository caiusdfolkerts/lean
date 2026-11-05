module

public import Projection.Rigidity.EuclideanWeakHull
public import Projection.Rigidity.WeakHullTransfer
public import Projection.ClosureObstruction

/-!
# Full-dimensional equality rigidity in the original coordinate model

The analytic theorem is proved in Euclidean coordinates. Only its actual
scalar mixed-volume conclusion is transported to the coordinate maximum-norm
space. The positive Haar conversion factor is explicit in the transfer
theorem. Strong support equality is then deduced for the original area
measures. No normal spheres or norms are silently identified.

The project's build and endpoint-audit reports record verification of this
source and its complete dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace RankThreeProjection
open VolumePolynomials Rigidity

/-- The actual weak hull conclusion for every full-dimensional coordinate
body. Neither interior of comparison bodies nor genericity of marked vectors
is required. -/
theorem weakHullReference_of_nonempty_interior {n d : ℕ}
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty) :
    WeakHullReference volume (d := d) K := by
  have hn : n = d + 2 := by
    simpa only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  subst n
  obtain ⟨p, hp⟩ := hK
  let K₀ : Body (d + 2) := translateBody (-p) K
  have hK₀ : (0 : Space (d + 2)) ∈ interior (K₀ : Set (Space (d + 2))) :=
    zero_mem_interior_translateBody_neg K p hp
  let T : Space (d + 2) ≃L[ℝ] OAI.PettyProjection.Space (d + 2) :=
    (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
  let L : ConvexBody (OAI.PettyProjection.Space (d + 2)) :=
    mapBody T.toContinuousLinearMap K₀
  have hL : (0 : OAI.PettyProjection.Space (d + 2)) ∈
      interior (L : Set (OAI.PettyProjection.Space (d + 2))) := by
    change (0 : OAI.PettyProjection.Space (d + 2)) ∈
      interior (T.toHomeomorph '' (K₀ : Set (Space (d + 2))))
    rw [← T.toHomeomorph.image_interior]
    exact ⟨0, hK₀, map_zero T⟩
  have hweakL : WeakHullReference volume (d := d) L := by
    apply weakHullReference_of_origin_comparisons volume L
    intro A C hA hC a ha hAA hAC hCC
    exact OAI.PettyProjection.euclidean_origin_weak_hull L A C hL hA hC
      a ha hAA hAC hCC
  have hweakK₀ : WeakHullReference volume (d := d) K₀ :=
    weakHullReference_of_frame volume volume T K₀ hweakL
  exact weakHullReference_of_translate volume K (-p) hweakK₀

/-- Full-dimensional segment-area rigidity, with the complete analytic and
convex-hull proof chain supplied. The only body hypothesis is actual nonempty
interior of the repeated body. -/
theorem segmentAreaRigidity_of_nonempty_interior {n d : ℕ} [NeZero n]
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty) :
    SegmentAreaRigidity K hdim :=
  segmentAreaRigidity_of_weakHullReference_of_interior K hdim hK
    (weakHullReference_of_nonempty_interior K hdim hK)

theorem fullDimensionalRigidity (n : ℕ) [NeZero n] :
    FullDimensionalRigidity (n := n) := by
  intro K d hdim hK
  exact segmentAreaRigidity_of_nonempty_interior K hdim hK

/-- Proposition 4.2 for the actual marked mixed-volume array. Full
dimensionality is the only geometric assumption on the repeated body, and
the marked vectors are arbitrary. The equality-rigidity theorem is supplied
by the complete proof chain rather than retained as a hypothesis. -/
theorem full_dimensional_obstruction {n d : ℕ} (hn : 5 ≤ n)
    (K : Body n) (hdim : finrank ℝ (Space n) = d + 2)
    (hK : (interior (K : Set (Space n))).Nonempty)
    (U : Fin n → Space n)
    (hpos : ∀ i j, i ≠ j → 0 < complementaryMixedMatrix (d := d) K U i j)
    (hrank : (complementaryMixedMatrix (d := d) K U).rank = 3) : False := by
  letI : NeZero n := ⟨by omega⟩
  exact full_dimensional_obstruction_from_segment_rigidity K hdim hn U hpos hrank
    (segmentAreaRigidity_of_nonempty_interior K hdim hK)

end RankThreeProjection
