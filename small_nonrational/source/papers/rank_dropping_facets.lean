module
public import Papers.ReducedSparseRows
public import Papers.ActualSmallFacetRankConstancy
public import FaceOrderExcessInvariants

@[expose] public section
noncomputable section

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus

namespace Papers.RationalityTen.ChirotopeDensity

/-- Omit supplements precisely where the polygon rank has decreased from
 the realization witnessing the eight-row budget. -/
def rankDroppingFacets {n : ℕ} (P Q : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) (φ : FaceType P ≃o FaceType Q) : Finset (Face Q 3) :=
  Finset.univ.filter fun F =>
    actualPolygonRelationRank Q (e.trans (vertexEquivOfFaceOrder φ)) F <
      actualPolygonRelationRank P e ((rankedFaceEquivOfFaceOrder φ).symm F)

@[simp] theorem mem_rankDroppingFacets {n : ℕ} (P Q : ConvexPolytope 4)
    (e : Fin n ≃ P.vertices) (φ : FaceType P ≃o FaceType Q) (F : Face Q 3) :
    F ∈ rankDroppingFacets P Q e φ ↔
      actualPolygonRelationRank Q (e.trans (vertexEquivOfFaceOrder φ)) F <
        actualPolygonRelationRank P e ((rankedFaceEquivOfFaceOrder φ).symm F) := by
  simp [rankDroppingFacets]

theorem rankDroppingFacet_size_and_polygon_count {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q) (F : Face Q 3)
    (hF : F ∈ rankDroppingFacets P Q e φ) :
    8 ≤ facetVertexCount P ((rankedFaceEquivOfFaceOrder φ).symm F) ∧
      4 ≤ ((polygonLabelsBelow Q (e.trans (vertexEquivOfFaceOrder φ)) F).filter
        fun S => 4 ≤ S.card).card := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  have hl : actualFaceLabels P e (b.symm F).val =
      actualFaceLabels Q (e.trans (vertexEquivOfFaceOrder φ)) F.val := by
    simpa only [b, Equiv.apply_symm_apply] using
      (actualFaceLabels_of_faceOrder φ e (b.symm F)).symm
  have hp : polygonLabelsBelow P e (b.symm F) =
      polygonLabelsBelow Q (e.trans (vertexEquivOfFaceOrder φ)) F := by
    simpa only [b, Equiv.apply_symm_apply] using
      (polygonLabelsBelow_of_faceOrder φ e (b.symm F)).symm
  have hne : actualPolygonRelationRank P e (b.symm F) ≠
      actualPolygonRelationRank Q (e.trans (vertexEquivOfFaceOrder φ)) F :=
    Nat.ne_of_gt ((mem_rankDroppingFacets P Q e φ F).mp hF)
  have h := actual_rank_change_facet_size_and_polygon_count P Q hP hQ e
    (e.trans (vertexEquivOfFaceOrder φ)) (b.symm F) F hl hp hne
  rw [hp] at h
  exact h

theorem rankDroppingFacets_card_le_two {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card) :
    (rankDroppingFacets P Q e φ).card ≤ 2 := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  have hsub : (rankDroppingFacets P Q e φ).image b.symm ⊆ largeFacets P := by
    intro F hF
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hF
    exact (mem_largeFacets P _).mpr
      (rankDroppingFacet_size_and_polygon_count P Q hP e φ G hG).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ b.symm.injective] at hcard
  exact hcard.trans (large_facets_card_le_two P hP e hc hN)

theorem nonsimplicial_polygon_count_le_local_excess {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    (((polygonLabelsBelow P e F).filter fun S => 4 ≤ S.card).card : ℤ) ≤
      facetPolygonExcess P F := by
  have hp : ∀ S ∈ polygonLabelsBelow P e F,
      (if 4 ≤ S.card then (1 : ℕ) else 0) ≤ S.card - 3 := by
    intro S _
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum hp
  have hsum' : ((polygonLabelsBelow P e F).filter fun S => 4 ≤ S.card).card ≤
      ∑ S ∈ polygonLabelsBelow P e F, (S.card - 3) := by
    simp only [Finset.sum_boole, Nat.cast_id] at hsum
    omega
  have hcast : (((polygonLabelsBelow P e F).filter fun S => 4 ≤ S.card).card : ℤ) ≤
      ((∑ S ∈ polygonLabelsBelow P e F, (S.card - 3) : ℕ) : ℤ) := by
    exact_mod_cast hsum'
  rw [polygonLabelsBelow_excess] at hcast
  exact hcast

theorem rankDroppingFacet_local_excess_ge_four {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q) (F : Face Q 3)
    (hF : F ∈ rankDroppingFacets P Q e φ) :
    4 ≤ facetPolygonExcess Q F := by
  have hcount := (rankDroppingFacet_size_and_polygon_count P Q hP e φ F hF).2
  have hbound := nonsimplicial_polygon_count_le_local_excess Q
    (e.trans (vertexEquivOfFaceOrder φ)) F
  omega

/-- The reduced matrix at every other realization retains the original
 eight-row bound, despite arbitrary rank increases or exceptional drops. -/
theorem rankDropping_reduced_row_count_le {n : ℕ}
    (P Q : ConvexPolytope 4) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q) :
    Fintype.card (ReducedSparseRowIndex Q (e.trans (vertexEquivOfFaceOrder φ))
      (rankDroppingFacets P Q e φ)) ≤ Fintype.card (SparseSharedRowIndex P e) := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  apply reducedSparseRowIndex_card_le P Q e (e.trans (vertexEquivOfFaceOrder φ))
    (rankDroppingFacets P Q e φ) b.symm (polygonExcess_of_faceOrder φ).symm
  intro F hF
  have hr : actualPolygonRelationRank P e (b.symm F) ≤
      actualPolygonRelationRank Q (e.trans (vertexEquivOfFaceOrder φ)) F := by
    have h := mt (mem_rankDroppingFacets P Q e φ F).mpr hF
    exact Nat.le_of_not_gt h
  have hv : facetVertexCount P (b.symm F) = facetVertexCount Q F := by
    simpa only [b, Equiv.apply_symm_apply] using facetVertexCount_of_faceOrder φ (b.symm F)
  have hp := actualFacetSparseSupplement_count P e (b.symm F)
  have hq := actualFacetSparseSupplement_count Q (e.trans (vertexEquivOfFaceOrder φ)) F
  change ((actualFacetSparseSupplement P e (b.symm F)).count : ℤ) =
    (facetVertexCount P (b.symm F) : ℤ) - 4 - _ at hp
  change ((actualFacetSparseSupplement Q (e.trans (vertexEquivOfFaceOrder φ)) F).count : ℤ) =
    (facetVertexCount Q F : ℤ) - 4 - _ at hq
  rw [hv] at hp
  omega

theorem rankDropping_reduced_outside_card_le_four {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (F : Face Q 3) (hF : F ∈ rankDroppingFacets P Q e φ) :
    (reducedOutsideRows Q (e.trans (vertexEquivOfFaceOrder φ))
      (rankDroppingFacets P Q e φ) F).card ≤ 4 := by
  apply reducedOutsideRows_card_le_four
  · exact (rankDropping_reduced_row_count_le P Q e φ).trans hc
  · exact rankDroppingFacet_local_excess_ge_four P Q hP e φ F hF

/-- Local polygon rows are a subfamily of all global polygon rows. -/
theorem facetPolygonExcess_le_polygonExcess {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3) :
    facetPolygonExcess P F ≤ polygonExcess P := by
  let f := fun R : Face P 2 => ((actualPolygonSparseBasis P e R).count : ℤ)
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun R : Face P 2 => R.val.carrier ⊆ F.val.carrier) f
  have hn : (0 : ℤ) ≤ ∑ R : {R : Face P 2 // ¬R.val.carrier ⊆ F.val.carrier}, f R.val :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  have hlocal : (∑ R : {R : Face P 2 // R.val.carrier ⊆ F.val.carrier}, f R.val) =
      facetPolygonExcess P F := by
    have h := localPolygonSparseRowIndex_card P e F
    simpa only [LocalPolygonSparseRowIndex, Fintype.card_sigma, Fintype.card_fin,
      Nat.cast_sum] using h
  have hall : (∑ R : Face P 2, f R) = polygonExcess P := by
    simp only [f, actualPolygonSparseBasis_count, polygonExcess]
  omega

end Papers.RationalityTen.ChirotopeDensity
