module
public import Papers.RankDroppingFacets

@[expose] public section
noncomputable section

open Set Module Matrix
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus Papers.PolytopeFaceNonedges
open Papers.PolytopeNonedgeAllocation

namespace Papers.RationalityTen.ChirotopeDensity

/-- Distinct facets contain at most one common polygon face. -/
theorem common_polygon_of_distinct_facets_unique {d : ℕ}
    (P : ConvexPolytope d) (F G : Face P 3) (hFG : F ≠ G)
    (R S : Face P 2)
    (hRF : R.val.carrier ⊆ F.val.carrier) (hRG : R.val.carrier ⊆ G.val.carrier)
    (hSF : S.val.carrier ⊆ F.val.carrier) (hSG : S.val.carrier ⊆ G.val.carrier) : R = S := by
  have hI : P.IsFace (F.val.carrier ∩ G.val.carrier) :=
    ⟨F.val.isFace.1.inter G.val.isFace.1,
      R.val.isFace.2.mono (fun _ hx => ⟨hRF hx,hRG hx⟩)⟩
  have hproper : F.val.carrier ∩ G.val.carrier ⊂ F.val.carrier := by
    refine ⟨Set.inter_subset_left, ?_⟩
    intro h
    have hsub : F.val.carrier ⊆ G.val.carrier := fun _ hx => (h hx).2
    have heq := face_eq_of_subset_equal_dimension P F.val.isFace G.val.isFace
      hsub (F.property.trans G.property.symm)
    exact hFG (Subtype.ext (PolytopeFace.ext heq))
  have hhi := faceDim_lt_of_ssubset P hI F.val.isFace hproper
  rw [F.property] at hhi
  have hR : R.val.carrier = F.val.carrier ∩ G.val.carrier := by
    by_contra h
    have hsub : R.val.carrier ⊆ F.val.carrier ∩ G.val.carrier :=
      fun _ hx => ⟨hRF hx,hRG hx⟩
    have hlt := faceDim_lt_of_ssubset P R.val.isFace hI (hsub.ssubset_of_ne h)
    rw [R.property] at hlt
    omega
  have hS : S.val.carrier = F.val.carrier ∩ G.val.carrier := by
    by_contra h
    have hsub : S.val.carrier ⊆ F.val.carrier ∩ G.val.carrier :=
      fun _ hx => ⟨hSF hx,hSG hx⟩
    have hlt := faceDim_lt_of_ssubset P S.val.isFace hI (hsub.ssubset_of_ne h)
    rw [S.property] at hlt
    omega
  exact Subtype.ext (PolytopeFace.ext (hR.trans hS.symm))

/-- Excess four carried by at least four nonsimplicial polygons forces
 every such polygon to be a quadrilateral. -/
theorem local_excess_four_polygons_card_le_four {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hg : facetPolygonExcess P F = 4)
    (hcount : 4 ≤ ((polygonLabelsBelow P e F).filter fun S => 4 ≤ S.card).card)
    (R : FaceBelow P F.val.carrier 2) : Nat.card (VerticesOn P R.val.val.carrier) ≤ 4 := by
  let L := polygonLabelsBelow P e F
  have hs := polygonLabelsBelow_excess P e F
  have hsum : (∑ S ∈ L, (S.card - 3)) = 4 := by rw [hg] at hs; exact_mod_cast hs
  have hpoint : ∀ S ∈ L, (if 4 ≤ S.card then (1 : ℕ) else 0) ≤ S.card - 3 := by
    intro S _
    split_ifs <;> omega
  have hlo := Finset.sum_le_sum hpoint
  have hbool : (∑ S ∈ L, if 4 ≤ S.card then (1 : ℕ) else 0) =
      (L.filter fun S => 4 ≤ S.card).card := by simp only [Finset.sum_boole, Nat.cast_id]
  have heq : (∑ S ∈ L, if 4 ≤ S.card then (1 : ℕ) else 0) =
      ∑ S ∈ L, (S.card - 3) := by
    change 4 ≤ (L.filter fun S => 4 ≤ S.card).card at hcount
    omega
  have hm : actualFaceLabels P e R.val.val ∈ L :=
    Finset.mem_image.mpr ⟨R,Finset.mem_univ _,rfl⟩
  have hterm := (Finset.sum_eq_sum_iff_of_le hpoint).mp heq _ hm
  rw [actualFaceLabels_card] at hterm
  split_ifs at hterm <;> omega

theorem local_sparse_polygon_count_le_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (F : Face P 3)
    (hg : facetPolygonExcess P F = 4)
    (hcount : 4 ≤ ((polygonLabelsBelow P e F).filter fun S => 4 ≤ S.card).card)
    (R : FaceBelow P F.val.carrier 2) : (actualPolygonSparseBasis P e R.val).count ≤ 1 := by
  have hv := local_excess_four_polygons_card_le_four P e F hg hcount R
  have hc := actualPolygonSparseBasis_count P e R.val
  omega

private theorem mem_reducedInsideRows_common_polygon {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (H : Finset (Face P 3))
    (F G : Face P 3) (i : Fin (Fintype.card (ReducedSparseRowIndex P e H)))
    (hF : i ∈ reducedInsideRows P e H F) (hG : i ∈ reducedInsideRows P e H G) :
    ∃ R : Face P 2, R.val.carrier ⊆ F.val.carrier ∧ R.val.carrier ⊆ G.val.carrier ∧
      ∃ a : Fin (actualPolygonSparseBasis P e R).count,
        Fintype.equivFin (ReducedSparseRowIndex P e H) (Sum.inl ⟨R,a⟩) = i := by
  obtain ⟨v,_,hv⟩ := Finset.mem_map.mp hF
  obtain ⟨w,_,hw⟩ := Finset.mem_map.mp hG
  change Fintype.equivFin (ReducedSparseRowIndex P e H)
    (Sum.inl ⟨v.1.val,v.2⟩) = i at hv
  change Fintype.equivFin (ReducedSparseRowIndex P e H)
    (Sum.inl ⟨w.1.val,w.2⟩) = i at hw
  have hr := (Fintype.equivFin (ReducedSparseRowIndex P e H)).injective (hv.trans hw.symm)
  have hpoly : v.1.val = w.1.val := congrArg Sigma.fst (Sum.inl.inj hr)
  refine ⟨v.1.val,v.1.property,?_,v.2,hv⟩
  rw [hpoly]
  exact w.1.property

theorem reducedInsideRows_inter_card_le_one {d n : ℕ}
    (P : ConvexPolytope d) (e : Fin n ≃ P.vertices) (H : Finset (Face P 3))
    (F G : Face P 3) (hFG : F ≠ G)
    (hrows : ∀ R : FaceBelow P F.val.carrier 2, (actualPolygonSparseBasis P e R.val).count ≤ 1) :
    ((reducedInsideRows P e H F) ∩ (reducedInsideRows P e H G)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨R,hRF,hRG,a,ha⟩ := mem_reducedInsideRows_common_polygon P e H F G i
    (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hi).2
  obtain ⟨S,hSF,hSG,b,hb⟩ := mem_reducedInsideRows_common_polygon P e H F G j
    (Finset.mem_inter.mp hj).1 (Finset.mem_inter.mp hj).2
  have hRS := common_polygon_of_distinct_facets_unique P F G hFG R S hRF hRG hSF hSG
  subst S
  have hsmall : (actualPolygonSparseBasis P e R).count ≤ 1 := hrows ⟨R,hRF⟩
  have hab : a = b := Fin.ext (by have ha' := a.isLt; have hb' := b.isLt; omega)
  exact ha.symm.trans ((congrArg (fun z =>
    Fintype.equivFin (ReducedSparseRowIndex P e H) (Sum.inl ⟨R,z⟩)) hab).trans hb)

theorem two_rankDroppingFacet_local_excess_eq_four {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F G : Face Q 3) (hFG : F ≠ G)
    (hF : F ∈ rankDroppingFacets P Q e φ) (hG : G ∈ rankDroppingFacets P Q e φ) :
    facetPolygonExcess Q F = 4 := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  have hLF : b.symm F ∈ largeFacets P := (mem_largeFacets P _).mpr
    (rankDroppingFacet_size_and_polygon_count P Q hP e φ F hF).1
  have hLG : b.symm G ∈ largeFacets P := (mem_largeFacets P _).mpr
    (rankDroppingFacet_size_and_polygon_count P Q hP e φ G hG).1
  have hpre : b.symm F ≠ b.symm G := fun h => hFG (b.symm.injective h)
  have hL : 2 ≤ (largeFacets P).card := by
    have hs : ({b.symm F,b.symm G} : Finset (Face P 3)) ⊆ largeFacets P := by
      exact Finset.insert_subset hLF (Finset.singleton_subset_iff.mpr hLG)
    have ht := Finset.card_le_card hs
    simpa only [Finset.card_pair hpre] using ht
  obtain ⟨_,_,_,_,_,hsizes,_⟩ := two_large_facets_equality P hP e hc hN hL
  obtain ⟨hsupp,hrank⟩ := two_large_facets_no_supplements P hP e hc hN hL
  have hsize := hsizes (b.symm F) hLF
  have hcount := actualFacetSparseSupplement_count P e (b.symm F)
  change ((actualFacetSparseSupplement P e (b.symm F)).count : ℤ) =
    (facetVertexCount P (b.symm F) : ℤ) - 4 - _ at hcount
  rw [hsupp, hsize] at hcount
  have hlocal := hrank (b.symm F)
  have htransport := facetPolygonExcess_of_faceOrder φ (b.symm F)
  change facetPolygonExcess P (b.symm F) = facetPolygonExcess Q (b (b.symm F)) at htransport
  rw [b.apply_symm_apply] at htransport
  omega

/-- The two exceptional outside-row sets intersect in at most one row.
 All hypotheses are properties of the original realization and its face order. -/
theorem rankDropping_reduced_outside_inter_card_le_one {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (F G : Face Q 3) (hFG : F ≠ G)
    (hF : F ∈ rankDroppingFacets P Q e φ) (hG : G ∈ rankDroppingFacets P Q e φ) :
    ((reducedOutsideRows Q (e.trans (vertexEquivOfFaceOrder φ))
        (rankDroppingFacets P Q e φ) F) ∩
      (reducedOutsideRows Q (e.trans (vertexEquivOfFaceOrder φ))
        (rankDroppingFacets P Q e φ) G)).card ≤ 1 := by
  apply reducedOutsideRows_inter_card_le_one
  · exact (rankDropping_reduced_row_count_le P Q e φ).trans hc
  · exact rankDroppingFacet_local_excess_ge_four P Q hP e φ F hF
  · exact rankDroppingFacet_local_excess_ge_four P Q hP e φ G hG
  · apply reducedInsideRows_inter_card_le_one Q _ _ F G hFG
    apply local_sparse_polygon_count_le_one Q _ F
    · exact two_rankDroppingFacet_local_excess_eq_four P Q hP e φ hc hN F G hFG hF hG
    · exact (rankDroppingFacet_size_and_polygon_count P Q hP e φ F hF).2

theorem two_rankDroppingFacets_polygonExcess {n : ℕ}
    (P Q : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (φ : FaceType P ≃o FaceType Q)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hH : 2 ≤ (rankDroppingFacets P Q e φ).card) : polygonExcess Q = 8 := by
  let b : Face P 3 ≃ Face Q 3 := rankedFaceEquivOfFaceOrder φ
  have hsub : (rankDroppingFacets P Q e φ).image b.symm ⊆ largeFacets P := by
    intro F hF
    obtain ⟨G,hG,rfl⟩ := Finset.mem_image.mp hF
    exact (mem_largeFacets P _).mpr
      (rankDroppingFacet_size_and_polygon_count P Q hP e φ G hG).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ b.symm.injective] at hcard
  have hL : 2 ≤ (largeFacets P).card := hH.trans hcard
  have hg := (two_large_facets_equality P hP e hc hN hL).2.2.2.1
  rw [← polygonExcess_of_faceOrder φ]
  exact hg

end Papers.RationalityTen.ChirotopeDensity
