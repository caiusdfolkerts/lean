module
public import Consolidated.LargeFacetRelations

@[expose] public section

/-!
# Exhaustive actual facet-size partition

This is the geometric entry point to the finite verification. It covers an
arbitrary residual ten-vertex polytope; no facet-size or catalogue-coverage
assumption is supplied by the caller. The two-six branch keeps all possible
six-vertex types; its later surplus reduction and finite classification discharge
the complete branch.
-/

noncomputable section
namespace Papers.RationalityTen.ActualResidualFacetPartition

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus
open ChirotopeDensity

local instance faceFintype {d : Nat} (P : ConvexPolytope d) (k : Nat) :
    Fintype (Face P k) := Fintype.ofFinite _

theorem actual_residual_partition
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin 10 ≃ P.vertices)
    (hn : P.vertices.card = 10)
    (hN : 10 ≤ (nonsimplicialFacets P).card)
    (hc : 9 ≤ Fintype.card (SparseSharedRowIndex P e)) :
    (∀ F : Face P 3, facetVertexCount P F ≤ 5) ∨
      ((∀ F : Face P 3, facetVertexCount P F ≤ 6) ∧ (sixVertexFacets P).Nonempty) ∨
      ∃ F₀ : Face P 3, facetVertexCount P F₀ = 7 ∧
        ((∀ F : Face P 3, F ≠ F₀ → facetVertexCount P F ≤ 5) ∨
          (∃ G₀ : Face P 3, facetVertexCount P G₀ = 6 ∧
            ∀ F : Face P 3, F ≠ F₀ → F ≠ G₀ → facetVertexCount P F ≤ 5) ∨
          ∃ G : Fin 2 → Face P 3, Function.Injective G ∧
            ∀ j, facetVertexCount P (G j) = 6) := by
  obtain hsmall | ⟨F₀, hF₀, hother6, hL⟩ :=
    actual_ten_vertex_residual_large_facet_partition P hP e hn hN hc
  · by_cases hfive : ∀ F : Face P 3, facetVertexCount P F ≤ 5
    · exact Or.inl hfive
    · right
      left
      refine ⟨hsmall, ?_⟩
      push_neg at hfive
      obtain ⟨F, hF⟩ := hfive
      exact ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have h := hsmall F; omega⟩⟩
  · right
    right
    refine ⟨F₀, hF₀, ?_⟩
    by_cases hzero : (sixVertexFacets P).card = 0
    · left
      intro F hF
      have hmax := hother6 F hF
      have hnot : F ∉ sixVertexFacets P := by
        rw [Finset.card_eq_zero.mp hzero]
        exact Finset.notMem_empty F
      have hnot6 : facetVertexCount P F ≠ 6 := by
        intro hsix
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsix⟩)
      omega
    · right
      by_cases hone : (sixVertexFacets P).card = 1
      · left
        obtain ⟨G₀, hset⟩ := Finset.card_eq_one.mp hone
        have hG₀ : G₀ ∈ sixVertexFacets P := by rw [hset]; simp
        refine ⟨G₀, (Finset.mem_filter.mp hG₀).2, ?_⟩
        intro F hF hFG
        have hmax := hother6 F hF
        have hnot6 : facetVertexCount P F ≠ 6 := by
          intro hsix
          have hmem : F ∈ sixVertexFacets P :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsix⟩
          rw [hset] at hmem
          exact hFG (Finset.mem_singleton.mp hmem)
        omega
      · right
        obtain ⟨G, hG⟩ := Function.Embedding.exists_of_card_le_finset
          (α := Fin 2) (show Fintype.card (Fin 2) ≤ (sixVertexFacets P).card by
            rw [Fintype.card_fin]
            omega)
        exact ⟨G, G.injective, fun j => (Finset.mem_filter.mp (hG ⟨j, rfl⟩)).2⟩

end Papers.RationalityTen.ActualResidualFacetPartition
