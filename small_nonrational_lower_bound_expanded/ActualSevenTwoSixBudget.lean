module
public import SevenFacetBudgetIdentities

@[expose] public section

/-!
# The complete seven-vertex / two six-vertex corner

The finite verification includes this corner directly. It therefore needs no
additional geometric exclusion of its configurations. The exact budget is
one seven-vertex facet, two six-vertex facets, and seven five-vertex facets,
with every possible number of square pyramids retained.
-/

noncomputable section
namespace Papers.RationalityTen.ActualSevenTwoSixBudget

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open Papers.PolytopeRelationBudget
open ChirotopeDensity SevenFacetBudgetIdentities

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem actual_two_six_covered
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e))
    (F₀ : Face P 3) (hF₀ : facetVertexCount P F₀ = 7)
    (G : Fin 2 → Face P 3) (hG : Function.Injective G)
    (hGsix : ∀ j, facetVertexCount P (G j) = 6) :
    Nat.card (Face P 3) = 10 ∧ facetExcess P = 14 ∧
      (nonsimplicialFacets P).card = 10 ∧ (sixVertexFacets P).card = 2 ∧
      (∀ F : Face P 3, F ≠ F₀ → (∀ j, F ≠ G j) → facetVertexCount P F = 5) ∧
      ∃ sp : Fin 8, (smallSquareFacets P).card = sp.val ∧
        (smallBipyramidFacets P).card = 7 - sp.val ∧
        (tetrahedralFacets P).card = 0 := by
  obtain ⟨hother6, hLhi⟩ :=
    actual_ten_vertex_residual_unique_seven P hP e hn hN hc F₀ hF₀
  obtain ⟨hm, hE, hNexact, _, _⟩ :=
    actual_seven_and_two_six_residual_budget P hP e hn hN hc F₀ hF₀ G hG hGsix
  have hallfive := actual_seven_and_two_six_all_facets_nonsimplicial
    P hP e hn hN hc F₀ hF₀ G hG hGsix
  have hsub : Finset.univ.image G ⊆ sixVertexFacets P := by
    intro F hF
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hF
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGsix j⟩
  have himage : (Finset.univ.image G).card = 2 := by
    rw [Finset.card_image_of_injective _ hG, Finset.card_univ, Fintype.card_fin]
  have hL : (sixVertexFacets P).card = 2 := by
    have hlo := Finset.card_le_card hsub
    omega
  have hset : sixVertexFacets P = Finset.univ.image G := by
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hother5 (F : Face P 3) (hF : F ≠ F₀) (hFG : ∀ j, F ≠ G j) :
      facetVertexCount P F = 5 := by
    have hlo := hallfive F
    have hhi := hother6 F hF
    by_contra hne
    have hsix : facetVertexCount P F = 6 := by omega
    have hmem : F ∈ sixVertexFacets P :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsix⟩
    rw [hset] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    exact hFG j hj.symm
  have hsmall := nonsimplicial_count_eq P F₀ hF₀ hother6
  rw [hNexact, hL] at hsmall
  have hSP : (smallSquareFacets P).card ≤ 7 := by omega
  have hBP : (smallBipyramidFacets P).card = 7 - (smallSquareFacets P).card := by omega
  have htotal := facet_count_eq_tetrahedra_add_nonsimplicial P
  rw [hm, hNexact] at htotal
  refine ⟨hm, hE, hNexact, hL, hother5,
    ⟨(smallSquareFacets P).card, by omega⟩, rfl, hBP, ?_⟩
  omega

end Papers.RationalityTen.ActualSevenTwoSixBudget
