module
public import Papers.ReducedOutsideRowWitnesses

@[expose] public section
noncomputable section

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus

namespace Papers.RationalityTen.ChirotopeDensity

/-- The exact finite matrix input supplied by the actual polytope geometry.
 The two optional facets require only outside-column rank preservation. -/
structure ReducedFacetMatrixData {n : ℕ} (p : Fin n → Fin 5 → ℝ) (g : ℤ) where
  rowCount : ℕ
  exceptionCount : ℕ
  matrix : Matrix (Fin rowCount) (Fin n) ℝ
  masks : Fin exceptionCount → Finset (Fin n)
  outsideRows : Fin exceptionCount → Finset (Fin rowCount)
  rowCount_le : rowCount ≤ 8
  exceptionCount_le : exceptionCount ≤ 2
  annihilates : matrix * Matrix.of p = 0
  masks_injective : Function.Injective masks
  masks_facets : ∀ a, FacetMask p (masks a)
  spans_other_facets : ∀ S, FacetMask p S → (∀ a, masks a ≠ S) →
    SpansFacetRelations matrix p S
  outsideRows_card : ∀ a, (outsideRows a).card ≤ 4
  outsideRows_support : ∀ a j, j ∉ masks a → ∀ i, i ∉ outsideRows a → matrix i j = 0
  outsideRows_inter : ∀ a b, a ≠ b → ((outsideRows a) ∩ (outsideRows b)).card ≤ 1
  outsideRows_occupied : ∀ a i, i ∈ outsideRows a →
    ∃ j, j ∉ masks a ∧ matrix i j ≠ 0
  outsideRows_empty_nonzero_count : ∀ a, outsideRows a = ∅ → totalNonzeros matrix ≤ 32
  nonzero_count : (totalNonzeros matrix : ℤ) ≤ 5 * rowCount - g
  polygon_excess_ge_four : 0 < exceptionCount → 4 ≤ g
  two_exception_nonzero_count : exceptionCount = 2 → totalNonzeros matrix ≤ 32

theorem reduced_actualFaceLabels_facetMask {n : ℕ}
    (Q : ConvexPolytope 4) (e : Fin n ≃ Q.vertices) (F : Face Q 3) :
    FacetMask (vertexCoordinates Q e) (actualFaceLabels Q e F.val) := by
  have hrank := actualFaceLabels_rank Q e F.val
  rw [F.property] at hrank
  refine ⟨?_, actualFaceLabels_has_strictSupport Q e F.val, ?_⟩
  · apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, subsetRank_empty] at hrank
    omega
  · omega

/-- A single eight-row realization provides the reduced matrix data at
 every realization of the same face lattice. No local-rank constancy is
 presumed for an exceptional facet. -/
def actualReducedFacetMatrixData {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card) :
    ReducedFacetMatrixData (vertexCoordinates Q (e.trans (vertexEquivOfFaceOrder φ)))
      (polygonExcess Q) := by
  let eQ := e.trans (vertexEquivOfFaceOrder φ)
  let H := rankDroppingFacets P Q e φ
  let c := Fintype.card (ReducedSparseRowIndex Q eQ H)
  let k := Fintype.card H
  let f : Fin k ≃ H := (Fintype.equivFin H).symm
  let C := actualReducedSparseMatrix Q eQ H
  let masks := fun a : Fin k => actualFaceLabels Q eQ (f a).val.val
  let outside := fun a : Fin k => reducedOutsideRows Q eQ H (f a).val
  have hc' : c ≤ 8 := (rankDropping_reduced_row_count_le P Q e φ).trans hc
  have hk : k ≤ 2 := by
    simpa only [k, Fintype.card_coe] using rankDroppingFacets_card_le_two P Q hP e φ hc hN
  have hnnz : (totalNonzeros C : ℤ) ≤ 5 * c - polygonExcess Q :=
    actualReducedSparseMatrix_nonzeros Q eQ H
  refine
    { rowCount := c
      exceptionCount := k
      matrix := C
      masks := masks
      outsideRows := outside
      rowCount_le := hc'
      exceptionCount_le := hk
      annihilates := actualReducedSparseMatrix_mul_zero Q eQ H
      masks_injective := ?_
      masks_facets := ?_
      spans_other_facets := ?_
      outsideRows_card := ?_
      outsideRows_support := ?_
      outsideRows_inter := ?_
      outsideRows_occupied := ?_
      outsideRows_empty_nonzero_count := ?_
      nonzero_count := hnnz
      polygon_excess_ge_four := ?_
      two_exception_nonzero_count := ?_ }
  · intro a b hab
    apply f.injective
    apply Subtype.ext
    apply Subtype.ext
    exact actualFaceLabels_injective Q eQ hab
  · intro a
    exact reduced_actualFaceLabels_facetMask Q eQ (f a).val
  · intro S hS hother
    obtain ⟨F,hF⟩ := facetMask_actual_three_face Q eQ S hS
    have hnot : F ∉ H := by
      intro hFH
      let a := f.symm ⟨F,hFH⟩
      have hmask : masks a = S := by
        change actualFaceLabels Q eQ (f (f.symm ⟨F,hFH⟩)).val.val = S
        rw [f.apply_symm_apply]
        exact hF
      exact hother a hmask
    rw [← hF]
    exact spansFacetRelations_of_supportedRowSpan _ _ _
      (actualReducedSparseMatrix_span_facet Q eQ H F hnot)
  · intro a
    exact rankDropping_reduced_outside_card_le_four P Q hP e φ hc (f a).val (f a).property
  · intro a j hj i hi
    exact reducedOutsideRows_support Q eQ H (f a).val j hj i hi
  · intro a b hab
    apply rankDropping_reduced_outside_inter_card_le_one P Q hP e φ hc hN
      (f a).val (f b).val
    · intro h
      exact hab (f.injective (Subtype.ext h))
    · exact (f a).property
    · exact (f b).property
  · intro a i hi
    exact actualReducedSparseMatrix_outside_row_witness Q
      ((faceOrderIso_polytope_dim φ).trans hP) eQ H (f a).val (f a).property i hi
  · intro a hO
    exact actualReducedSparseMatrix_nonzeros_of_outside_empty Q eQ H (f a).val hc' hO
  · intro hkpos
    let a : Fin k := ⟨0,hkpos⟩
    have hlo := rankDroppingFacet_local_excess_ge_four P Q hP e φ (f a).val (f a).property
    have hhi := facetPolygonExcess_le_polygonExcess Q eQ (f a).val
    omega
  · intro hk2
    have hH2 : 2 ≤ H.card := by
      have : Fintype.card H = H.card := Fintype.card_coe H
      change Fintype.card H = 2 at hk2
      omega
    have hg := two_rankDroppingFacets_polygonExcess P Q hP e φ hc hN hH2
    omega

/-- With no omitted facet, the reduced matrix is the ordinary canonical
 shared-row matrix up to its row enumeration. -/
theorem reducedSparseRowIndex_card_empty {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) :
    Fintype.card (ReducedSparseRowIndex P e ∅) = Fintype.card (SparseSharedRowIndex P e) := by
  let f := reducedSparseRowEmbedding P e ∅
  have hf : Function.Bijective f := by
    refine ⟨f.injective,?_⟩
    rintro (⟨R,i⟩ | ⟨F,i⟩)
    · exact ⟨Sum.inl ⟨R,i⟩,rfl⟩
    · exact ⟨Sum.inr ⟨⟨F,Finset.notMem_empty F⟩,i⟩,rfl⟩
  exact Fintype.card_congr (Equiv.ofBijective f hf)

theorem no_rankDroppingFacets_sparse_row_count_le {n : ℕ}
    (P Q : ConvexPolytope 4) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hH : (rankDroppingFacets P Q e φ).card = 0) :
    Fintype.card (SparseSharedRowIndex Q (e.trans (vertexEquivOfFaceOrder φ))) ≤ 8 := by
  have hred := (rankDropping_reduced_row_count_le P Q e φ).trans hc
  rw [Finset.card_eq_zero.mp hH, reducedSparseRowIndex_card_empty] at hred
  exact hred

end Papers.RationalityTen.ChirotopeDensity
