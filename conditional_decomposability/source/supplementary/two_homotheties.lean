module
public import consolidated_dev.conditional_complete_integration

set_option Elab.async false

@[expose] public section

/-!
# Small homothety covers without a dimension premise

Lemma 5 of the paper does not state a separate lower bound on the ambient
dimension. Under its vertex budget, a nonhomothetic parallel map already
forces that dimension to be at least three. Dense actual-graph rigidity
excludes the remaining dimensions.

The persistence statements below derive this dimension bound. The
two-homothety and segment statements allow targets in any Euclidean
ambient dimension. The three-homothety statement uses the existing
same-dimensional realization interface, with no separate dimension
lower bound.
-/

noncomputable section

namespace Papers.Polytopes

open Set
open Papers.ActualFaceOrder
open Papers.PolytopeFourRegularTail Papers.PolytopeSimpleTailFace
open Papers.PolytopeVertexCone Papers.WeakSummandScaling
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {d e : ℕ}

/-- Below the paper's vertex threshold, a nonhomothetic parallel map
cannot occur in ambient dimension zero, one, or two. The minimum-degree
bound concerns the actual edge graph of the full-dimensional polytope. -/
theorem three_le_dimension_of_small_nonhomothetic_parallel_map
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    3 ≤ d := by
  by_contra hd
  have hcard_pos : 0 < P.vertices.card := Finset.card_pos.mpr P.vertices_nonempty
  have hsmall : P.vertices.card < 2 * d := by omega
  have hdegree : ∀ x ∈ P.vertices,
      d ≤ (P.vertices.filter (fun y => GeneralVertexStep P x y)).card := by
    intro x hx
    change d ≤ (actualNeighbors P x).card
    have hdim : P.dim = d := hP
    simpa only [hdim] using intrinsic_dim_le_neighbor_card P hx
  have hrigid := rigid_tail_of_min_degree_card_lt_twice
    P P.vertices (fun _ hx => hx) d hdegree hsmall
  exact hnon (hrigid f hf)

/-- Lemma 5 for an arbitrary finite cover by at most two homotheties.
Essentiality, private vertices, and the dimension bound are all derived.
The target is any actual realization of the same face order. -/
theorem decomposable_after_face_iso_of_at_most_two_homotheties
    {I : Type*} [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (p : I → ℝ × E d) (hcard : Fintype.card I ≤ 2)
    (hcover : ∀ x ∈ P.vertices, ∃ i : I,
      f x = (p i).1 • x + (p i).2)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope e) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hd := three_le_dimension_of_small_nonhomothetic_parallel_map
    P hP f hf hnon hN
  obtain ⟨m, hmlo, hmhi, q, color, hvalues, hprivate⟩ :=
    Papers.ActualEssentialCovers.essential_cover_of_homothety_cover
      P f p hcover hnon
  have hm : m = 2 := by omega
  subst m
  exact Papers.ActualTwoCoverReductions.decomposable_after_iso_of_essential_two_cover
    P hP hd f q hf color hvalues hprivate hN Q φ

/-- Proposition 11 for an arbitrary finite cover by at most three
homotheties, deriving the dimension bound before applying the established
three-cover reconstruction. This does not use the main sharp theorem. -/
theorem decomposable_after_face_iso_of_at_most_three_homotheties
    {I : Type*} [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    (p : I → ℝ × E d) (hcard : Fintype.card I ≤ 3)
    (hcover : ∀ x ∈ P.vertices, ∃ i : I,
      f x = (p i).1 • x + (p i).2)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope d) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hd := three_le_dimension_of_small_nonhomothetic_parallel_map
    P hP f hf hnon hN
  exact decomposable_after_iso_of_at_most_three_homotheties
    P hP hd f hf hnon p hcard hcover hN Q ⟨φ⟩

/-- The segment weak-summand consequence of Lemma 5, with no separate
dimension premise. Positive scaling is absorbed into the actual summand,
and its nonhomothetic vertex map supplies the derived dimension bound. -/
theorem decomposable_after_face_iso_of_segment_weak_summand
    (P A : ConvexPolytope d) (hP : P.IsFullDim)
    (hweak : IsWeakSummand P A) (hA : A.dim = 1)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope e) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨ε, hε, B, hbody⟩ := hweak
  let S := scalePolytope A ε
  have hS : S.dim = 1 := by
    dsimp only [S]
    rw [scalePolytope_dim A ε hε.ne', hA]
  have hsum : P.toSet = S.toSet + B.toSet := by
    dsimp only [S]
    rwa [scalePolytope_body]
  have htwo : 2 ≤ d := by
    have hcard_pos : 0 < P.vertices.card := Finset.card_pos.mpr P.vertices_nonempty
    omega
  obtain ⟨f, hf, hnon, _⟩ :=
    Papers.ProperMinkowskiMap.actual_vertex_map_of_proper_summand
      P S B hsum (by rw [hS]; omega) (by rw [hS, hP]; omega)
  have hd := three_le_dimension_of_small_nonhomothetic_parallel_map
    P hP f hf hnon hN
  exact Papers.SegmentSummandPersistence.segment_summand_persists
    P S B hP hd hsum hS hN Q φ

end Papers.Polytopes

end
