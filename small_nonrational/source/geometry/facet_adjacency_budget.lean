module
public import Consolidated.LargeFacetRelations

@[expose] public section

/-!
# Two actual incidence bounds used by the seven-vertex budgets

A polygon belongs to two different facets. Thus, if every facet except one
has at most six vertices, every polygon has at most five vertices. Conversely,
the ridges of a fixed facet have pairwise different other facet cofaces; their
number is at most the total facet count minus one.
-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Finset Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeSmallFacetBounds Papers.PolytopeFacetSurplus

theorem polygon_card_le_five_of_one_large_facet {d : Nat}
    (P : ConvexPolytope d) (hP : P.dim = 4) (F₀ : Face P 3)
    (hother : ∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 6)
    (R : Face P 2) : Nat.card (VerticesOn P R.val.carrier) ≤ 5 := by
  let T := Finset.univ.filter (fun F : Face P 3 => R.val.carrier ⊆ F.val.carrier)
  have hc : T.card = 2 := by
    simpa only [T, Coface, Nat.card_eq_fintype_card, Fintype.card_subtype]
      using ridge_coface_card P 2 hP R
  obtain ⟨F, hF⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (show ({F₀} : Finset (Face P 3)).card < T.card by simp [hc])
  obtain ⟨hFT, hFF₀⟩ := Finset.mem_sdiff.mp hF
  have hne : F ≠ F₀ := by simpa only [Finset.mem_singleton] using hFF₀
  have hlt := polygon_card_lt_containing_facet P R F (Finset.mem_filter.mp hFT).2
  have hbound := hother F hne
  omega

/-- Two distinct facets can have only one common ridge. -/
theorem common_ridge_unique {d n : Nat} (P : ConvexPolytope d)
    (e : Fin n ≃ P.vertices) (F G : Face P 3) (hFG : F ≠ G)
    (R S : Face P 2)
    (hRF : R.val.carrier ⊆ F.val.carrier) (hRG : R.val.carrier ⊆ G.val.carrier)
    (hSF : S.val.carrier ⊆ F.val.carrier) (hSG : S.val.carrier ⊆ G.val.carrier) :
    R = S := by
  have hlabels := Finset.card_le_card (Finset.subset_inter
    (actualFaceLabels_mono P e hRF) (actualFaceLabels_mono P e hRG))
  rw [actualFaceLabels_card] at hlabels
  have hlo := face_vertices_card_ge_dim_add_one P 2 R
  obtain ⟨T, hT, _⟩ := actual_three_face_intersection_labels P e F G hFG
    (show 3 ≤ (actualFaceLabels P e F.val ∩ actualFaceLabels P e G.val).card by omega)
  have hRT : R.val.carrier = T.val.carrier := by
    apply Papers.PolytopeNonedgeAllocation.face_eq_of_subset_equal_dimension
      P R.val.isFace T.val.isFace
    · rw [hT]
      exact Set.subset_inter hRF hRG
    · exact R.property.trans T.property.symm
  have hST : S.val.carrier = T.val.carrier := by
    apply Papers.PolytopeNonedgeAllocation.face_eq_of_subset_equal_dimension
      P S.val.isFace T.val.isFace
    · rw [hT]
      exact Set.subset_inter hSF hSG
    · exact S.property.trans T.property.symm
  exact Subtype.ext (PolytopeFace.ext (hRT.trans hST.symm))

/-- The other-facet map is injective, so a fixed facet has fewer ridges than
the total number of facets. This is the direction needed by the budget. -/
theorem facet_ridge_count_add_one_le_facets {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (F : Face P 3) :
    Nat.card (FaceBelow P F.val.carrier 2) + 1 ≤ Nat.card (Face P 3) := by
  have hex (R : FaceBelow P F.val.carrier 2) :
      ∃ G : Face P 3, G ≠ F ∧ R.val.val.carrier ⊆ G.val.carrier := by
    let T := Finset.univ.filter (fun G : Face P 3 =>
      R.val.val.carrier ⊆ G.val.carrier)
    have hc : T.card = 2 := by
      simpa only [T, Coface, Nat.card_eq_fintype_card, Fintype.card_subtype]
        using ridge_coface_card P 2 hP R.val
    obtain ⟨G, hG⟩ := Finset.sdiff_nonempty_of_card_lt_card
      (show ({F} : Finset (Face P 3)).card < T.card by simp [hc])
    obtain ⟨hGT, hGF⟩ := Finset.mem_sdiff.mp hG
    exact ⟨G, by simpa only [Finset.mem_singleton] using hGF,
      (Finset.mem_filter.mp hGT).2⟩
  choose G hGF hRG using hex
  have hG : Function.Injective G := by
    intro R S h
    apply Subtype.ext
    apply common_ridge_unique P e F (G R) (hGF R).symm R.val S.val
      R.property (hRG R) S.property
    rw [h]
    exact hRG S
  let image := (Finset.univ : Finset (FaceBelow P F.val.carrier 2)).image G
  have hnot : F ∉ image := by
    intro hF
    obtain ⟨R, _, hR⟩ := Finset.mem_image.mp hF
    exact hGF R hR
  have hc := Finset.card_le_card
    (Finset.subset_univ (insert F image))
  rw [Finset.card_insert_of_notMem hnot] at hc
  change image.card + 1 ≤ Fintype.card (Face P 3) at hc
  have hi : image.card = Fintype.card (FaceBelow P F.val.carrier 2) := by
    change ((Finset.univ : Finset (FaceBelow P F.val.carrier 2)).image G).card = _
    rw [Finset.card_image_of_injective _ hG, Finset.card_univ]
  rw [hi] at hc
  simpa only [Nat.card_eq_fintype_card] using hc

end Papers.RationalityTen.ChirotopeDensity
