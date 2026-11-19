/-
The active-constraint proof is generalized from
vendor/openai-math/ProjectionVolume/FiniteVertices.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, already vendored in this project.
Released under the Apache License 2.0; see vendor/openai-math/LICENSE.
The generalization removes unit-normal, distinctness and strict-interior
assumptions, retaining the same finite active-pattern argument.
-/
module

public import VolumePolynomials.GeneralInteractionBody
public import VolumePolynomials.PolyhedralSupport

@[expose] public section
set_option autoImplicit false

/-! # Finite edge representations give actual polygons

An extreme point of a finite system of linear inequalities is determined by
its active constraints, even when the system has empty interior. This proves
that the compact Minkowski summands used in the edge construction are finite
convex hulls. No polygonality of an erosion is assumed.
-/

noncomputable section
open Set MeasureTheory Filter Metric Module
open scoped Topology Pointwise BigOperators RealInnerProductSpace

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def finiteInequalities {ι : Type*} (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : Set E :=
  {x | ∀ i, l i x ≤ b i}

theorem finiteInequalities_extreme_unique {ι : Type*} [Fintype ι]
    (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) {x y : E}
    (hx : x ∈ (finiteInequalities l b).extremePoints ℝ)
    (ha : ∀ i, l i x = b i → l i y = b i) : y = x := by
  first
  | classical
    exact PolyhedralSupport.extreme_active_unique l b hx ha

theorem compact_finiteInequalities_isFiniteHull {ι : Type*} [Fintype ι]
    (l : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (hc : IsCompact (finiteInequalities l b)) :
    IsFiniteHull (finiteInequalities l b) := by
  first
  | classical
    let active (x : E) : Finset ι := Finset.univ.filter (fun i => l i x = b i)
    have hinj : Set.InjOn active ((finiteInequalities l b).extremePoints ℝ) := by
      first
      | intro x hx y _ hxy
        apply (finiteInequalities_extreme_unique l b hx ?_).symm
        intro i hix
        have hm : i ∈ active x := by simp [active, hix]
        rw [hxy] at hm
        exact (Finset.mem_filter.mp hm).2
    have hfinite : ((finiteInequalities l b).extremePoints ℝ).Finite :=
      (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn (fun _ _ => Set.mem_univ _) hinj
    have hconv : Convex ℝ (finiteInequalities l b) := by
      first
      | simp only [finiteInequalities, Set.ofPred_forall]
        exact convex_iInter (fun i => (convex_Iic (b i)).linear_preimage (l i).toLinearMap)
    refine ⟨_, hfinite, ?_⟩
    have h := closure_convexHull_extremePoints hc hconv
    rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at h
    exact h.symm

/-- A compact convex summand of a full-dimensional polytope is a polytope.
The summand itself may have arbitrary affine dimension. -/
theorem finiteHull_of_fullDimensional_sum (Q R : ConvexBody E)
    (hpoly : IsFiniteHull ((Q + R : ConvexBody E) : Set E))
    (hint : (interior ((Q + R : ConvexBody E) : Set E)).Nonempty) : IsFiniteHull (Q : Set E) := by
  first
  | let T : E ≃L[ℝ] Euclidean (finrank ℝ E) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have hmap := hpoly.linear_image T.toLinearMap
    have himage : (interior (T '' ((Q + R : ConvexBody E) : Set E))).Nonempty := by
      first
      | have hi : T '' interior ((Q + R : ConvexBody E) : Set E) =
            interior (T '' ((Q + R : ConvexBody E) : Set E)) := by
          simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
            T.toHomeomorph.image_interior ((Q + R : ConvexBody E) : Set E)
        rw [← hi]
        exact hint.image T
    obtain ⟨m, P, hP⟩ := hmap.has_halfspaces himage
    let l : Fin m → E →L[ℝ] ℝ := fun i => (innerSL ℝ (P.normal i)).comp T.toContinuousLinearMap
    have hC (x : E) : x ∈ Q + R ↔ ∀ i, l i x ≤ P.offset i := by
      first
      | change x ∈ (Q + R : ConvexBody E) ↔ T x ∈ P.body
        rw [hP]
        constructor
        · exact fun hx => ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, hxy⟩
          exact T.injective hxy ▸ hy
    have heq : (Q : Set E) = finiteInequalities l
        (fun i => P.offset i - SupportGeometry.support (R : Set E) (l i)) := by
      first
      | ext x
        constructor
        · intro hx i
          obtain ⟨r, hr, hmax⟩ := SupportGeometry.exists_support R.isCompact R.nonempty (l i)
          have h := (hC (x + r)).mp (Set.mem_add.mpr ⟨x, hx, r, hr, rfl⟩) i
          rw [map_add, hmax] at h
          linarith
        · intro hx
          apply Iff.mpr (BodySupport.mem_iff_le_support Q)
          intro f
          obtain ⟨r, hr, hmax⟩ := SupportGeometry.exists_support R.isCompact R.nonempty f
          have hxr : x + r ∈ Q + R := (hC (x + r)).mpr (fun i => by
            have hi := hx i
            have hs := SupportGeometry.le_support R.isCompact (l i) hr
            rw [map_add]
            linarith)
          have hs := SupportGeometry.le_support (Q + R).isCompact f hxr
          change f (x + r) ≤ SupportGeometry.support ((Q : Set E) + (R : Set E)) f at hs
          rw [map_add, hmax, SupportGeometry.support_add Q.isCompact Q.nonempty R.isCompact R.nonempty] at hs
          change f x ≤ SupportGeometry.support (Q : Set E) f
          linarith
    rw [heq]
    apply compact_finiteInequalities_isFiniteHull
    rw [← heq]
    exact Q.isCompact

end VolumePolynomials.PolytopeGeometry

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarInteraction PolytopeGeometry OAI.Paper092

theorem triangleSum_finiteHull {ι : Type*} [Fintype ι] (e : ι → Plane) :
    IsFiniteHull (triangleSum e : Set Plane) := by
  first
  | rw [triangleSum, coe_sum_body]
    exact IsFiniteHull.sum Finset.univ (fun i => (triangleFromEdge (e i) : Set Plane))
      (fun i _ => rightTriangle_finiteHull _ _)

theorem finiteHull_translateBody {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) (hK : IsFiniteHull (K : Set E)) :
    IsFiniteHull (translateBody v K : Set E) := (IsFiniteHull.singleton v).add hK

theorem interior_nonempty_of_area_pos (K : ConvexBody Plane)
    (ha : 0 < volume.real (K : Set Plane)) : (interior (K : Set Plane)).Nonempty := by
  first
  | by_contra hn
    have hempty := Set.not_nonempty_iff_eq_empty.mp hn
    have hzero := K.convex.addHaar_frontier (volume : Measure Plane)
    rw [frontier, K.isClosed.closure_eq, hempty, Set.diff_empty] at hzero
    rw [measureReal_def, hzero, ENNReal.toReal_zero] at ha
    exact lt_irrefl 0 ha

/-- Every unit-width body with an actual finite mixed-area representation
is a finite convex hull, including degenerate cases. -/
theorem Represents.finiteHull_of_unit_widths {ι : Type*} [Fintype ι]
    {Q : ConvexBody Plane} {e : ι → Plane} (hQ : Represents Q e)
    (hw : width Q = 1) (hh : height Q = 1) : IsFiniteHull (Q : Set Plane) := by
  first
  | obtain ⟨v, hv⟩ := hQ.triangleSum_eq_translate
    have hrect : boundingRectangle Q = unitSquare := by
      first
      | simp only [boundingRectangle, hw, hh, one_smul, unitSquare]
    rw [hrect] at hv
    have hpoly := finiteHull_translateBody (triangleSum e) (-v) (triangleSum_finiteHull e)
    rw [hv, translateBody_translate, neg_add_cancel, translateBody_zero] at hpoly
    have harea : 0 < volume.real ((Q + unitSquare : ConvexBody Plane) : Set Plane) := by
      first
      | rw [area_add volume plane_finrank, unitSquare_area]
        have hQarea : 0 ≤ volume.real (Q : Set Plane) := measureReal_nonneg
        have hmix := mixedArea_nonnegative volume Q unitSquare
        linarith
    exact finiteHull_of_fullDimensional_sum Q unitSquare hpoly (interior_nonempty_of_area_pos _ harea)

end VolumePolynomials.PlanarEdges
