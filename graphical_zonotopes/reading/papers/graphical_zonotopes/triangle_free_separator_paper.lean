module

public import Papers.GraphicalZonotopes.TriangleFreeSeparator
public import Papers.GraphicalZonotopes.PolytopalDimension
public import Papers.GraphicalZonotopes.SpanningTetrahedra

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset

/-- The literal connectivity conclusion includes nonemptiness of every
remaining vertex set. The cardinality hypothesis supplies that fact. -/
theorem SupportsFullIndecomposable.delete_lt_three_connected {n : ℕ} (hn : 4 ≤ n)
    {G : SimpleGraph (Fin n)} (hG : SupportsFullIndecomposable G)
    (B : Finset (Fin n)) (hB : B.card < 3) :
    (G.induce ((B : Set (Fin n))ᶜ)).Connected := by
  classical
  have hout : ∃ v : Fin n,v ∉ B := by
    by_contra h
    push_neg at h
    have he : B = univ := by
      ext v
      simp only [mem_univ,iff_true]
      exact h v
    have hc := congrArg Finset.card he
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨v,hv⟩ := hout
  letI : Nonempty {w : Fin n // w ∈ (B : Set (Fin n))ᶜ} := ⟨⟨v,hv⟩⟩
  exact ⟨hG.delete_lt_three_preconnected hn B hB⟩

/-- Corollary 5.2 with ordinary polytopal indecomposability and the full
three-vertex-connectivity conclusion, expressed directly by all deletions. -/
theorem paper_corollary_5_2 {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ∃ Q : Set (Fin n → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      (G.induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hs := (supportsFullIndecomposable_iff_polytopal_weak G).mpr hG
  exact ⟨fun B hB => hs.separator_contains_triangle (by omega) B hB,
    fun B hB => hs.delete_lt_three_connected hn B hB⟩

/-- The printed extension of Corollary 5.2 to the actual direction graph of
any full-dimensional indecomposable generalized permutahedron. -/
theorem full_generalized_permutahedron_triangle_separators {n : ℕ} (hn : 4 ≤ n)
    {Q : Set (Fin n → ℝ)} (hQ : IsGeneralizedPermutahedron Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card (((actualDirectionGraph Q).induce
        ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ (actualDirectionGraph Q).IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      ((actualDirectionGraph Q).induce ((B : Set (Fin n))ᶜ)).Connected) := by
  have hw : IsWeakMinkowskiSummand Q (graphicalZonotope (actualDirectionGraph Q)) := by
    obtain ⟨z,hzn,hzs,rfl⟩ := hQ
    exact (isWeakMinkowskiSummand_graphical_iff hzn hzs).mpr
      (graphical_actualDirectionGraph hzn hzs)
  exact paper_corollary_5_2 hn (actualDirectionGraph Q) ⟨Q,hQ.finitePolytope,hi,hd,hw⟩

end GraphicalZonotopes
