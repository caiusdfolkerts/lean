module
public import Papers.TwoExceptionalRowOverlap

@[expose] public section
noncomputable section

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus Papers.PolytopeFaceNonedges
open Papers.PolytopeSmallFacetBounds

namespace Papers.RationalityTen.ChirotopeDensity

/-- A supplement with the exact dimension count has no redundant row
 modulo the space it extends. -/
theorem finiteSpaceSupplement_row_not_mem {n : ℕ}
    {U V : Submodule ℝ (Fin n → ℝ)} (D : FiniteSpaceSupplement U V)
    (i : Fin D.count) : D.rows i ∉ U := by
  intro hi
  let T : Finset (Fin n → ℝ) := (Finset.univ.erase i).image D.rows
  have hle : V ≤ U ⊔ Submodule.span ℝ (↑T : Set (Fin n → ℝ)) := by
    rw [← D.spans]
    apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    by_cases hj : j = i
    · subst j
      exact (show U ≤ U ⊔ Submodule.span ℝ (↑T : Set (Fin n → ℝ)) from le_sup_left) hi
    · apply (show Submodule.span ℝ (↑T : Set (Fin n → ℝ)) ≤
          U ⊔ Submodule.span ℝ (↑T : Set (Fin n → ℝ)) from le_sup_right)
      apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,rfl⟩
  have hdim := Submodule.finrank_mono hle
  have hsup := Submodule.finrank_add_le_finrank_add_finrank U
    (Submodule.span ℝ (↑T : Set (Fin n → ℝ)))
  have hspan : finrank ℝ (Submodule.span ℝ (↑T : Set (Fin n → ℝ))) ≤ T.card :=
    finrank_span_finset_le_card T
  have hcard : T.card ≤ D.count - 1 := by
    have h := Finset.card_image_le (f := D.rows) (s := Finset.univ.erase i)
    simpa only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] using h
  have hcount := D.dimension
  have hipos := i.isLt
  omega

/-- A nonzero polygon relation supported on another face forces that
 entire polygon into the face. This uses actual extreme-vertex geometry. -/
theorem actual_polygon_relation_supported_face {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (R : Face P 2) (F : PolytopeFace P) (v : Fin n → ℝ)
    (hvR : v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e R.val))
    (hvF : v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F))
    (hv0 : v ≠ 0) : R.val.carrier ⊆ F.carrier := by
  let T := actualFaceLabels P e R.val ∩ actualFaceLabels P e F
  have hvT : v ∈ globalRelationSpace (vertexCoordinates P e) T := by
    rw [← globalRelationSpace_inter_support]
    exact ⟨hvR,hvF⟩
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hfour := four_le_card_of_nonzero_relation (vertexCoordinates P e)
    (vertexCoordinates_small_independent P e hPcard) T v hvT hv0
  have hlo : 2 ≤ faceDim (R.val.carrier ∩ F.carrier) := by
    apply three_actual_labels_dimension P e T (by omega)
    intro i hi
    exact ⟨(mem_actualFaceLabels P e R.val i).mp (Finset.mem_inter.mp hi).1,
      (mem_actualFaceLabels P e F i).mp (Finset.mem_inter.mp hi).2⟩
  have hnonempty : (R.val.carrier ∩ F.carrier).Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    exact ⟨(e i).val,(mem_actualFaceLabels P e R.val i).mp (Finset.mem_inter.mp hi).1,
      (mem_actualFaceLabels P e F i).mp (Finset.mem_inter.mp hi).2⟩
  have hI : P.IsFace (R.val.carrier ∩ F.carrier) :=
    ⟨R.val.isFace.1.inter F.isFace.1,hnonempty⟩
  have heq : R.val.carrier ∩ F.carrier = R.val.carrier := by
    by_contra h
    have hlt := faceDim_lt_of_ssubset P hI R.val.isFace
      (Set.inter_subset_left.ssubset_of_ne h)
    rw [R.property] at hlt
    omega
  intro x hx
  exact (heq.symm ▸ hx).2

/-- A facet relation that is also supported on a distinct facet belongs
 to the first facet's polygon relation span. -/
theorem actual_shared_facet_relation_in_polygon_span {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F G : Face P 3) (hFG : F ≠ G) (v : Fin n → ℝ)
    (hvF : v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val))
    (hvG : v ∈ globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e G.val)) :
    v ∈ polygonRelationSpan (vertexCoordinates P e) (polygonLabelsBelow P e F) := by
  by_cases hv0 : v = 0
  · rw [hv0]
    exact Submodule.zero_mem _
  let T := actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val
  have hvT : v ∈ globalRelationSpace (vertexCoordinates P e) T := by
    rw [← globalRelationSpace_inter_support]
    exact ⟨hvF,hvG⟩
  have hPcard : 3 ≤ P.vertices.card := by
    have h := vertices_card_ge_dim_add_one P
    rw [hP] at h
    omega
  have hfour := four_le_card_of_nonzero_relation (vertexCoordinates P e)
    (vertexCoordinates_small_independent P e hPcard) T v hvT hv0
  obtain ⟨R,hR,hRl⟩ := actual_three_face_intersection_labels P e F G hFG (by change 3 ≤ T.card; omega)
  have hRF : R.val.carrier ⊆ F.val.carrier := by rw [hR]; exact Set.inter_subset_left
  apply globalRelationSpace_le_polygonRelationSpan (vertexCoordinates P e)
    (Finset.mem_image.mpr ⟨⟨R,hRF⟩,Finset.mem_univ _,rfl⟩)
  rw [hRl]
  exact hvT

/-- Every complementary row has an actual nonzero entry outside its
 exceptional facet; no zero or redundant supplement can fake this. -/
theorem actualReducedSparseMatrix_outside_row_witness {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (H : Finset (Face P 3)) (F : Face P 3) (hF : F ∈ H)
    (i : Fin (Fintype.card (ReducedSparseRowIndex P e H)))
    (hi : i ∈ reducedOutsideRows P e H F) :
    ∃ j : Fin n, j ∉ actualFaceLabels P e F.val ∧ actualReducedSparseMatrix P e H i j ≠ 0 := by
  by_contra h
  have hout : ∀ j, j ∉ actualFaceLabels P e F.val → actualReducedSparseMatrix P e H i j = 0 := by
    intro j hj
    by_contra hz
    exact h ⟨j,hj,hz⟩
  let z := (Fintype.equivFin (ReducedSparseRowIndex P e H)).symm i
  have hiz : Fintype.equivFin (ReducedSparseRowIndex P e H) z = i :=
    (Fintype.equivFin (ReducedSparseRowIndex P e H)).apply_symm_apply i
  have hrow : actualReducedSparseMatrix P e H i = actualReducedSparseRow P e H z := rfl
  have hvF : actualReducedSparseRow P e H z ∈
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) :=
    (mem_globalRelationSpace_iff _ _ _).mpr
      ⟨hout,actualReducedSparseRow_relation P e H z⟩
  generalize hz : z = x at hvF hiz
  rcases x with ⟨R,a⟩ | ⟨G,a⟩
  · have hv0 : (actualPolygonSparseBasis P e R).rows a ≠ 0 := by
      intro heq
      have hn := finiteSpaceSupplement_row_not_mem (actualPolygonSparseBasis P e R).toFiniteSpaceSupplement a
      apply hn
      rw [heq]
      exact Submodule.zero_mem _
    have hRF := actual_polygon_relation_supported_face P hP e R F.val
      ((actualPolygonSparseBasis P e R).rows a) ((actualPolygonSparseBasis P e R).mem a) hvF hv0
    have hin : i ∈ reducedInsideRows P e H F := by
      apply Finset.mem_map.mpr
      refine ⟨⟨⟨R,hRF⟩,a⟩,Finset.mem_univ _,?_⟩
      exact hiz
    exact (Finset.mem_compl.mp hi) hin
  · have hGF : G.val ≠ F := by
      intro heq
      exact G.property (heq ▸ hF)
    have hmem := actual_shared_facet_relation_in_polygon_span P hP e G.val F hGF
      ((actualFacetSparseSupplement P e G.val).rows a)
      ((actualFacetSparseSupplement P e G.val).mem a) hvF
    exact finiteSpaceSupplement_row_not_mem
      (actualFacetSparseSupplement P e G.val).toFiniteSpaceSupplement a hmem

/-- If the complementary row set is empty, the polygon contribution alone
 already gives the stronger thirty-two-entry bound. -/
theorem actualReducedSparseMatrix_nonzeros_of_outside_empty {n : ℕ}
    (P : ConvexPolytope 4) (e : Fin n ≃ P.vertices)
    (H : Finset (Face P 3)) (F : Face P 3)
    (hc : Fintype.card (ReducedSparseRowIndex P e H) ≤ 8)
    (hO : reducedOutsideRows P e H F = ∅) :
    totalNonzeros (actualReducedSparseMatrix P e H) ≤ 32 := by
  have hin := reducedInsideRows_card P e H F
  have hsum := Finset.card_compl_add_card (reducedInsideRows P e H F)
  change (reducedOutsideRows P e H F).card + (reducedInsideRows P e H F).card =
    Fintype.card (Fin (Fintype.card (ReducedSparseRowIndex P e H))) at hsum
  rw [hO,Finset.card_empty,Fintype.card_fin] at hsum
  have hg := facetPolygonExcess_le_polygonExcess P e F
  have hnnz := actualReducedSparseMatrix_nonzeros P e H
  omega

end Papers.RationalityTen.ChirotopeDensity
