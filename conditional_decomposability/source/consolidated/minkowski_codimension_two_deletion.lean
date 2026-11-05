module
public import consolidated_dev.minkowski_fiber_geometry
public import consolidated.minkowski_deletion_summand

set_option Elab.async false

section BundlePart0
/- Source: Papers/MinkowskiCodimensionTwoDeletion.lean -/







@[expose] public section

/-!
# The single-extra-vertex case in codimension two

Deleting the unique vertex outside the vertex fibres preserves the actual
quotient and the actual Minkowski summand.  The deleted polytope has a
Shephard facet.  Its combinatorial deletion is intrinsic, and every parallel
map extends across the restored simple vertex.  This proves persistence in
every realization, without assuming any geometric compatibility of that
realization with the original quotient.
-/

noncomputable section
namespace Papers.MinkowskiCodimensionTwoDeletion

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder Papers.PolytopeVertexCone
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiCodimensionTwoCounts Papers.MinkowskiUniqueExtraSimple
open Papers.MinkowskiDeletionSummand Papers.MinkowskiShephardNoExtras
open Papers.LinearImageFibers Papers.FiniteHullPolytope
open Papers.ExactShephardCriterion Papers.ActualPaperCoverReduction
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem polytope_eq_of_body_eq (P Q : ConvexPolytope n)
    (h : P.toSet = Q.toSet) : P = Q := by
  have hv : P.vertices = Q.vertices := by
    apply Finset.coe_injective
    calc
      (P.vertices : Set (E n)) = P.toSet.extremePoints ℝ := P.vertices_eq_extremePoints
      _ = Q.toSet.extremePoints ℝ := congrArg (Set.extremePoints ℝ) h
      _ = (Q.vertices : Set (E n)) := Q.vertices_eq_extremePoints.symm
  cases P
  cases Q
  cases hv
  rfl

theorem image_unchanged_after_deleting_nonvertex_image
    (P : ConvexPolytope n) (π : E n →L[ℝ] E n)
    (x : E n) (hxextra : π x ∉ (imagePolytope P π).vertices)
    (hne : (P.vertices.erase x).Nonempty) :
    imagePolytope (deleteVertex P x hne) π = imagePolytope P π := by
  let D := deleteVertex P x hne
  apply polytope_eq_of_body_eq
  apply Set.Subset.antisymm
  · rw [linear_imagePolytope_toSet, linear_imagePolytope_toSet]
    apply Set.image_mono
    exact convexHull_mono (Finset.erase_subset x P.vertices)
  · change convexHull ℝ ((imagePolytope P π).vertices : Set (E n)) ⊆ _
    apply convexHull_min ?_ (convex_convexHull ℝ _)
    intro q hq
    obtain ⟨z,hz,hzq⟩ := image_vertex_has_vertex_preimage P π ⟨q,hq⟩
    have hzx : z ≠ x := by
      intro heq
      subst z
      exact hxextra (hzq.symm ▸ hq)
    change q ∈ (imagePolytope (deleteVertex P x hne) π).toSet
    rw [linear_imagePolytope_toSet]
    exact ⟨z,subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hzx,hz⟩),hzq⟩

theorem codimension_two_no_extras_shephard
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hsum : P.toSet = A.toSet + B.toSet)
    (hr : 2 ≤ A.dim) (hq : (quotientPolytope P A).dim = 2)
    (hN : P.vertices.card ≤ 4*n-5)
    (hcover : ∀ x ∈ P.vertices,
      summandProjection A x ∈ (quotientPolytope P A).vertices) :
    ExactShephardFacet P := by
  have hdim := quotient_dimension_add_summand_dimension P A hP
  have hc := quotient_has_three_vertices_of_codimension_two P A B hP hsum hr hq hN
  obtain ⟨q,hh⟩ := exists_homothetic_summand_fiber P A B hP hsum
    (by omega) (by omega) hN
  exact shephardFacet_of_simplex_quotient_no_extras P A B hP hsum
    (by omega) (by omega) (by omega) hcover q hh

theorem nonhomothetic_codimension_two_persists
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hsum : P.toSet = A.toSet + B.toSet)
    (hr : 2 ≤ A.dim) (hq : (quotientPolytope P A).dim = 2)
    (hN : P.vertices.card ≤ 4*n-5)
    (q0 : (quotientPolytope P A).vertices)
    (hbad : ¬SummandHomotheticFiber P A B hsum q0)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  by_cases hex : (extraVertices P A).Nonempty
  · obtain ⟨hAc,hec,hfc,hotherfib,hPc⟩ :=
      nonhomothetic_with_extra_saturation P A B hP hsum hr hq hN q0 hbad hex
    obtain ⟨x,hxset⟩ := Finset.card_eq_one.mp hec
    have hxextra : x ∈ extraVertices P A := by rw [hxset]; simp
    have hxP := (Finset.mem_filter.mp hxextra).1
    have hximage := (Finset.mem_filter.mp hxextra).2
    let v : VertexType P := ⟨x,hxP⟩
    have hdim := quotient_dimension_add_summand_dimension P A hP
    have hn : 2 ≤ n := by omega
    have hcard : n+1 < P.vertices.card := by omega
    have hs : IsSimpleVertex P v := by
      change (polytopeGraph P).degree v = P.dim
      rw [← Papers.SimpleFour.actualNeighbors_card_eq_graph_degree P v,hP]
      exact unique_extra_neighbor_card P A B hP hsum hr hq hN q0 hbad hxset
    let hne := simpleDeletion_nonempty P hP v hs hcard
    let D := deleteVertex P x hne
    have hD : D.IsFullDim := deleteVertex_fullDim_of_simple P hP v hs hcard hne
    have hother : ∀ y ∈ P.vertices, y ≠ x →
        summandProjection A y ∈ (quotientPolytope P A).vertices := by
      intro y hy hyx
      by_contra hybad
      have hmem : y ∈ extraVertices P A := Finset.mem_filter.mpr ⟨hy,hybad⟩
      rw [hxset] at hmem
      exact hyx (Finset.mem_singleton.mp hmem)
    obtain ⟨B',hDB⟩ := summand_persists_after_unique_extra_deletion P A B hsum
      (summandProjection A) (by rw [summandProjection_kernel]) x hxP hximage hother hne
    have hquot : quotientPolytope D A = quotientPolytope P A :=
      image_unchanged_after_deleting_nonvertex_image P (summandProjection A) x hximage hne
    have hDN : D.vertices.card ≤ 4*n-5 :=
      (Finset.card_le_card (Finset.erase_subset x P.vertices)).trans hN
    have hDCover : ∀ y ∈ D.vertices,
        summandProjection A y ∈ (quotientPolytope D A).vertices := by
      intro y hy
      rw [hquot]
      exact hother y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
    have hDS := codimension_two_no_extras_shephard D A B' hD hDB hr
      (by rw [hquot]; exact hq) hDN hDCover
    let w := imageVertex φ v
    have hsQ : IsSimpleVertex Q w := isSimple_imageVertex φ v hs
    have hcardQ : n+1 < Q.vertices.card := by
      rw [← faceOrderIso_vertex_card φ]
      exact hcard
    let hneQ := simpleDeletion_nonempty Q hQ w hsQ hcardQ
    let DQ := deleteVertex Q w.val hneQ
    have hDQ : DQ.IsFullDim := deleteVertex_fullDim_of_simple Q hQ w hsQ hcardQ hneQ
    obtain ⟨ψ⟩ := simpleDeletion_combinatoriallyEquivalent φ hP v hs hcard hne hneQ
    have hDQdecomp : MinkowskiDecomposable DQ :=
      decomposable_after_iso_of_exact_shephard_facet D hDS DQ hDQ ψ
    exact decomposable_of_simple_deletion Q hQ hn w hsQ hcardQ hneQ hDQdecomp
  · have hcover : ∀ x ∈ P.vertices,
        summandProjection A x ∈ (quotientPolytope P A).vertices := by
      intro x hx
      by_contra hbad
      exact hex ⟨x,Finset.mem_filter.mpr ⟨hx,hbad⟩⟩
    exact decomposable_after_iso_of_exact_shephard_facet P
      (codimension_two_no_extras_shephard P A B hP hsum hr hq hN hcover) Q hQ φ

end Papers.MinkowskiCodimensionTwoDeletion

end
end
end BundlePart0

