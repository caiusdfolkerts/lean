import cubical.polytope.facet_geometry

/-!
# Certifying that a list contains every geometric facet

A finite convex polytope has a connected facet adjacency graph, and each
ridge belongs to exactly two facets.  Consequently, a nonempty family of
genuine facets is exhaustive as soon as every ridge of every member has
its other incident facet in the family.

This criterion is used twice in the explicit construction: first inside
each proposed three-dimensional cube, and then for the complete boundary
of the four-dimensional polytope.  All facets and ridges in the statements
below are exposed faces of an actual convex hull.
-/

open Set

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- A nonempty family of geometric facets that contains both sides of each
of its ridges contains every facet of the polytope. -/
theorem facetFamily_eq_univ_of_ridge_pairing (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) (S : Set (FacetType P)) (hne : S.Nonempty)
    (hpair : ∀ F ∈ S, ∀ R : Set (E n), P.IsFace R →
      faceDim R + 2 = P.dim → R ⊆ F.val.val →
      ∃ G ∈ S, G ≠ F ∧ R ⊆ G.val.val) :
    S = Set.univ := by
  have hclosed : ∀ {F G : FacetType P}, F ∈ S → facetStep P F G → G ∈ S := by
    intro F G hFS hstep
    obtain ⟨R, hR, hRF, hRG, hdR⟩ := hstep
    obtain ⟨H, hHS, hHF, hRH⟩ := hpair F hFS R hR hdR hRF
    obtain ⟨J, _hJF, _hRJ, hall⟩ := facet_ridge_diamond P hR hdR F hRF
    have hHJ : H = J := (hall H hRH).resolve_left hHF
    rcases hall G hRG with hGF | hGJ
    · exact hGF.symm ▸ hFS
    · exact hGJ.symm ▸ (hHJ ▸ hHS)
  obtain ⟨F, hFS⟩ := hne
  apply Set.eq_univ_of_forall
  intro G
  have hpath := facetStep_connected P hdim F G
  induction hpath with
  | refl => exact hFS
  | tail _ hstep ih => exact hclosed ih hstep

/-- An indexed list of genuine facets is exhaustive if it is nonempty
and every ridge of every listed facet has a different listed neighbor. -/
theorem facets_surjective_of_ridge_pairing (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) {ι : Type*} [Nonempty ι]
    (facets : ι → FacetType P)
    (hpair : ∀ i, ∀ R : Set (E n), P.IsFace R →
      faceDim R + 2 = P.dim → R ⊆ (facets i).val.val →
      ∃ j, facets j ≠ facets i ∧ R ⊆ (facets j).val.val) :
    Function.Surjective facets := by
  have hnonempty : (Set.range facets).Nonempty := Set.range_nonempty facets
  have hfull := facetFamily_eq_univ_of_ridge_pairing P hdim (Set.range facets)
    hnonempty (by
      rintro F ⟨i, rfl⟩ R hR hdR hRF
      obtain ⟨j, hji, hRj⟩ := hpair i R hR hdR hRF
      exact ⟨facets j, ⟨j, rfl⟩, hji, hRj⟩)
  intro F
  have hF : F ∈ Set.range facets := by rw [hfull]; trivial
  exact hF

/-- Version with a local ridge catalogue.  The local completeness premise
is geometric: it must cover every actual ridge contained in a listed
facet, not merely every ridge in an abstract incidence table. -/
theorem facets_surjective_of_ridge_catalogue (P : ConvexPolytope n)
    (hdim : 2 ≤ P.dim) {ι κ : Type*} [Nonempty ι]
    (facets : ι → FacetType P) (ridge : ι → κ → Set (E n))
    (hcomplete : ∀ i, ∀ R : Set (E n), P.IsFace R →
      faceDim R + 2 = P.dim → R ⊆ (facets i).val.val →
      ∃ k, R = ridge i k)
    (hpair : ∀ i k, ∃ j,
      facets j ≠ facets i ∧ ridge i k ⊆ (facets j).val.val) :
    Function.Surjective facets := by
  apply facets_surjective_of_ridge_pairing P hdim facets
  intro i R hR hdR hRF
  obtain ⟨k, rfl⟩ := hcomplete i R hR hdR hRF
  exact hpair i k

end LeanEval.Geometry.PlatonicClassification
