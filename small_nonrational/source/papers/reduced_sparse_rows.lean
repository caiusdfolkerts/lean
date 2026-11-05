module
public import Papers.ReducedRelationBudgets

@[expose] public section
noncomputable section

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus

namespace Papers.RationalityTen.ChirotopeDensity

/-- Keep every polygon circuit, omitting only supplements belonging to H. -/
def ReducedSparseRowIndex {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :=
  (Σ R : Face P 2, Fin (actualPolygonSparseBasis P e R).count) ⊕
  (Σ F : {F : Face P 3 // F ∉ H}, Fin (actualFacetSparseSupplement P e F.val).count)

instance {d n : ℕ} (P : ConvexPolytope d) (e : Fin n ≃ P.vertices)
    (H : Finset (Face P 3)) : Fintype (ReducedSparseRowIndex P e H) := by
  unfold ReducedSparseRowIndex
  infer_instance

def reducedSparseRowEmbedding {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    ReducedSparseRowIndex P e H ↪ SparseSharedRowIndex P e where
  toFun
    | Sum.inl i => Sum.inl i
    | Sum.inr ⟨F, i⟩ => Sum.inr ⟨F.val, i⟩
  inj' := by
    rintro (⟨R,i⟩ | ⟨⟨F,hF⟩,i⟩) (⟨S,j⟩ | ⟨⟨G,hG⟩,j⟩) h
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · have h' := Sum.inr.inj h
      cases h'
      rfl

def actualReducedSparseRow {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    ReducedSparseRowIndex P e H → Fin n → ℝ :=
  fun i => actualSparseSharedRow P e (reducedSparseRowEmbedding P e H i)

theorem actualReducedSparseRow_relation {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3))
    (i : ReducedSparseRowIndex P e H) :
    (Matrix.of (vertexCoordinates P e)).transpose.mulVec (actualReducedSparseRow P e H i) = 0 :=
  actualSparseSharedRow_relation P e (reducedSparseRowEmbedding P e H i)

theorem actualReducedSparseRows_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) (hF : F ∉ H) :
    supportedRowSpan (actualReducedSparseRow P e H) (actualFaceLabels P e F.val) =
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  let p := vertexCoordinates P e
  let S := actualFaceLabels P e F.val
  let T := supportedRowSpan (actualReducedSparseRow P e H) S
  have hle : T ≤ globalRelationSpace p S := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl, hi⟩
    exact (mem_globalRelationSpace_iff p S _).mpr
      ⟨hi, actualReducedSparseRow_relation P e H i⟩
  have hpoly : polygonRelationSpan p (polygonLabelsBelow P e F) ≤ T := by
    apply Finset.sup_le
    intro U hU
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hU
    rw [← actualPolygonSparseBasis_span P e R.val]
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.inl ⟨R.val, i⟩, rfl, ?_⟩
    have hm := globalRelationSpace_mono p (actualFaceLabels_mono P e R.property)
      ((actualPolygonSparseBasis P e R.val).mem i)
    exact ((mem_globalRelationSpace_iff p S _).mp hm).1
  have hsupp : Submodule.span ℝ (Set.range (actualFacetSparseSupplement P e F).rows) ≤ T := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨Sum.inr ⟨⟨F,hF⟩, i⟩, rfl, ?_⟩
    exact ((mem_globalRelationSpace_iff p S _).mp
      ((actualFacetSparseSupplement P e F).mem i)).1
  apply le_antisymm hle
  rw [← (actualFacetSparseSupplement P e F).spans]
  exact sup_le hpoly hsupp

def actualReducedSparseMatrix {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    Matrix (Fin (Fintype.card (ReducedSparseRowIndex P e H))) (Fin n) ℝ :=
  fun i => actualReducedSparseRow P e H ((Fintype.equivFin (ReducedSparseRowIndex P e H)).symm i)

theorem actualReducedSparseMatrix_mul_zero {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    actualReducedSparseMatrix P e H * Matrix.of (vertexCoordinates P e) = 0 := by
  ext i j
  have h := congrFun (actualReducedSparseRow_relation P e H
    ((Fintype.equivFin (ReducedSparseRowIndex P e H)).symm i)) j
  simpa [actualReducedSparseMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h

theorem actualReducedSparseMatrix_span_facet {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) (hF : F ∉ H) :
    supportedRowSpan (actualReducedSparseMatrix P e H) (actualFaceLabels P e F.val) =
      globalRelationSpace (vertexCoordinates P e) (actualFaceLabels P e F.val) := by
  rw [← actualReducedSparseRows_span_facet P e H F hF]
  apply congrArg (Submodule.span ℝ)
  ext v
  constructor
  · rintro ⟨i, hi, hs⟩
    exact ⟨(Fintype.equivFin (ReducedSparseRowIndex P e H)).symm i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    refine ⟨Fintype.equivFin (ReducedSparseRowIndex P e H) i, ?_, ?_⟩ <;>
      simpa only [actualReducedSparseMatrix, Equiv.symm_apply_apply]

theorem reducedSparseRowIndex_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    (Fintype.card (ReducedSparseRowIndex P e H) : ℤ) =
      polygonExcess P + ∑ F : {F : Face P 3 // F ∉ H},
        ((actualFacetSparseSupplement P e F.val).count : ℤ) := by
  simp only [ReducedSparseRowIndex, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, Nat.cast_add, Nat.cast_sum, actualPolygonSparseBasis_count,
    polygonExcess]

/-- Comparison with a possibly different realization uses only the
 supplement counts of retained facets; no rank constancy is assumed. -/
theorem reducedSparseRowIndex_card_le {d t n m : ℕ}
    (P : ConvexPolytope d) (Q : ConvexPolytope t)
    (eP : Fin n ≃ P.vertices) (eQ : Fin m ≃ Q.vertices)
    (H : Finset (Face Q 3)) (φ : Face Q 3 ≃ Face P 3)
    (hg : polygonExcess Q = polygonExcess P)
    (hcount : ∀ F : Face Q 3, F ∉ H →
      (actualFacetSparseSupplement Q eQ F).count ≤
        (actualFacetSparseSupplement P eP (φ F)).count) :
    Fintype.card (ReducedSparseRowIndex Q eQ H) ≤
      Fintype.card (SparseSharedRowIndex P eP) := by
  have hs : (∑ F : {F : Face Q 3 // F ∉ H},
      ((actualFacetSparseSupplement Q eQ F.val).count : ℤ)) ≤
      ∑ F : Face P 3, ((actualFacetSparseSupplement P eP F).count : ℤ) := by
    calc
      _ ≤ ∑ F : {F : Face Q 3 // F ∉ H},
          ((actualFacetSparseSupplement P eP (φ F.val)).count : ℤ) := by
        apply Finset.sum_le_sum
        intro F _
        exact_mod_cast hcount F.val F.property
      _ ≤ ∑ F : Face Q 3, ((actualFacetSparseSupplement P eP (φ F)).count : ℤ) := by
        have hsplit := Fintype.sum_subtype_add_sum_subtype
          (fun F : Face Q 3 => F ∉ H)
          (fun F => ((actualFacetSparseSupplement P eP (φ F)).count : ℤ))
        have hnonneg : (0 : ℤ) ≤ ∑ F : {F : Face Q 3 // ¬F ∉ H},
            ((actualFacetSparseSupplement P eP (φ F.val)).count : ℤ) :=
          Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
        omega
      _ = _ := Fintype.sum_equiv φ _ _ (fun _ => rfl)
  have hcard : (Fintype.card (SparseSharedRowIndex P eP) : ℤ) =
      polygonExcess P + ∑ F : Face P 3,
        ((actualFacetSparseSupplement P eP F).count : ℤ) := by
    simp only [SparseSharedRowIndex, Fintype.card_sum, Fintype.card_sigma,
      Fintype.card_fin, Nat.cast_add, Nat.cast_sum, actualPolygonSparseBasis_count,
      polygonExcess]
  have hred := reducedSparseRowIndex_card Q eQ H
  rw [hg] at hred
  omega

def localPolygonReducedRowEmbedding {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) :
    LocalPolygonSparseRowIndex P e F ↪ ReducedSparseRowIndex P e H where
  toFun i := Sum.inl ⟨i.1.val, i.2⟩
  inj' := by
    rintro ⟨⟨R,hR⟩,i⟩ ⟨⟨S,hS⟩,j⟩ h
    have h' := Sum.inl.inj h
    cases h'
    rfl

def reducedInsideRows {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) :
    Finset (Fin (Fintype.card (ReducedSparseRowIndex P e H))) :=
  Finset.univ.map ((localPolygonReducedRowEmbedding P e H F).trans
    (Fintype.equivFin (ReducedSparseRowIndex P e H)).toEmbedding)

def reducedOutsideRows {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) :
    Finset (Fin (Fintype.card (ReducedSparseRowIndex P e H))) :=
  (reducedInsideRows P e H F)ᶜ

theorem reducedInsideRows_card {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3) :
    ((reducedInsideRows P e H F).card : ℤ) = facetPolygonExcess P F := by
  rw [reducedInsideRows, Finset.card_map, Finset.card_univ]
  exact localPolygonSparseRowIndex_card P e F

/-- Columns outside a selected facet use only the complementary rows. -/
theorem reducedOutsideRows_support {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3)
    (j : Fin n) (hj : j ∉ actualFaceLabels P e F.val)
    (i : Fin (Fintype.card (ReducedSparseRowIndex P e H)))
    (hi : i ∉ reducedOutsideRows P e H F) :
    actualReducedSparseMatrix P e H i j = 0 := by
  have hin : i ∈ reducedInsideRows P e H F := by
    simpa only [reducedOutsideRows, Finset.mem_compl, not_not] using hi
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hin
  change actualReducedSparseRow P e H
    ((Fintype.equivFin (ReducedSparseRowIndex P e H)).symm
      (Fintype.equivFin (ReducedSparseRowIndex P e H)
        (localPolygonReducedRowEmbedding P e H F v))) j = 0
  rw [Equiv.symm_apply_apply]
  have hm := globalRelationSpace_mono (vertexCoordinates P e)
    (actualFaceLabels_mono P e v.1.property)
    ((actualPolygonSparseBasis P e v.1.val).mem v.2)
  exact ((mem_globalRelationSpace_iff _ _ _).mp hm).1 j hj

theorem reducedOutsideRows_card_le_four {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F : Face P 3)
    (hc : Fintype.card (ReducedSparseRowIndex P e H) ≤ 8)
    (hg : 4 ≤ facetPolygonExcess P F) :
    (reducedOutsideRows P e H F).card ≤ 4 := by
  have hin := reducedInsideRows_card P e H F
  have hsum := Finset.card_compl_add_card (reducedInsideRows P e H F)
  simp only [Fintype.card_fin] at hsum
  change (reducedOutsideRows P e H F).card + (reducedInsideRows P e H F).card = _ at hsum
  omega

/-- A finite-set identity turns the common-polygon bound into the
 required one-coordinate overlap bound. -/
theorem reducedOutsideRows_inter_card_le_one {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) (F G : Face P 3)
    (hc : Fintype.card (ReducedSparseRowIndex P e H) ≤ 8)
    (hF : 4 ≤ facetPolygonExcess P F) (hG : 4 ≤ facetPolygonExcess P G)
    (hinter : ((reducedInsideRows P e H F) ∩ (reducedInsideRows P e H G)).card ≤ 1) :
    ((reducedOutsideRows P e H F) ∩ (reducedOutsideRows P e H G)).card ≤ 1 := by
  have hcF := reducedInsideRows_card P e H F
  have hcG := reducedInsideRows_card P e H G
  have hu := Finset.card_union_add_card_inter
    (reducedInsideRows P e H F) (reducedInsideRows P e H G)
  have hcomp := Finset.card_compl_add_card
    (reducedInsideRows P e H F ∪ reducedInsideRows P e H G)
  simp only [Fintype.card_fin, Finset.compl_union] at hcomp
  change ((reducedOutsideRows P e H F) ∩ (reducedOutsideRows P e H G)).card + _ = _ at hcomp
  omega

/-- Four entries per polygon circuit and five per remaining supplement. -/
theorem actualReducedSparseMatrix_nonzeros {d n : ℕ} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (H : Finset (Face P 3)) :
    (totalNonzeros (actualReducedSparseMatrix P e H) : ℤ) ≤
      5 * Fintype.card (ReducedSparseRowIndex P e H) - polygonExcess P := by
  have heq : totalNonzeros (actualReducedSparseMatrix P e H) =
      totalNonzeros (actualReducedSparseRow P e H) :=
    Fintype.sum_equiv ((Fintype.equivFin (ReducedSparseRowIndex P e H)).symm)
      _ _ (fun _ => rfl)
  have hbound : totalNonzeros (actualReducedSparseRow P e H) ≤
      4 * (∑ R : Face P 2, (actualPolygonSparseBasis P e R).count) +
      5 * (∑ F : {F : Face P 3 // F ∉ H}, (actualFacetSparseSupplement P e F.val).count) := by
    unfold totalNonzeros
    change (∑ i : (Σ R : Face P 2, Fin (actualPolygonSparseBasis P e R).count) ⊕
      (Σ F : {F : Face P 3 // F ∉ H}, Fin (actualFacetSparseSupplement P e F.val).count),
      (vectorSupport (actualReducedSparseRow P e H i)).card) ≤ _
    rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_sigma, actualReducedSparseRow, reducedSparseRowEmbedding,
      Function.Embedding.coeFn_mk, actualSparseSharedRow]
    apply add_le_add
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro R _
      calc
        _ ≤ ∑ _i : Fin (actualPolygonSparseBasis P e R).count, 4 :=
          Finset.sum_le_sum (fun i _ => (actualPolygonSparseBasis P e R).sparse i)
        _ = _ := by simp [mul_comm]
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro F _
      calc
        _ ≤ ∑ _i : Fin (actualFacetSparseSupplement P e F.val).count, 5 :=
          Finset.sum_le_sum (fun i _ => (actualFacetSparseSupplement P e F.val).sparse i)
        _ = _ := by simp [mul_comm]
  have hZ : (totalNonzeros (actualReducedSparseRow P e H) : ℤ) ≤
      4 * (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) +
      5 * (∑ F : {F : Face P 3 // F ∉ H}, ((actualFacetSparseSupplement P e F.val).count : ℤ)) := by
    exact_mod_cast hbound
  have hg : (∑ R : Face P 2, ((actualPolygonSparseBasis P e R).count : ℤ)) =
      polygonExcess P := by simp only [actualPolygonSparseBasis_count, polygonExcess]
  have hc := reducedSparseRowIndex_card P e H
  rw [heq]
  linarith only [hZ, hg, hc]

end Papers.RationalityTen.ChirotopeDensity
