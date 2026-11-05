import cubical.polytope.simplicial_boundary
import cubical.polytope.simplicial_vertex_figure

/-!
# Every relevant link of a simplicial convex boundary is a minimal cycle

The proof iterates actual hyperplane vertex figures. Their dimensions drop
by one, their facet vertices remain affinely independent, and the precise
boundary-link equality transports the verified circuit property.
-/

open Classical

namespace LeanEval.Geometry.PlatonicClassification

open Cubical.Simplicial

variable {n : ℕ}

/-- All links of dimension relevant to rigidity in a genuine simplicial
convex polytope are minimal simplicial `𝔽₂` cycles. -/
theorem IsSimplicial.boundary_hasCircuitLinks (P : ConvexPolytope n)
    (hs : IsSimplicial P) : HasCircuitLinks P.dim (boundaryFacets P) := by
  have aux : ∀ d : ℕ, ∀ Q : ConvexPolytope n, Q.dim = d → IsSimplicial Q →
      HasCircuitLinks Q.dim (boundaryFacets Q) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hQdim hQ
      by_cases hd : 3 ≤ d
      · apply HasCircuitLinks.of_vertex_links
          (simplicial_boundary_circuit Q hQ (by omega))
        intro v _hv
        let D : DatiFetta Q v.val :=
          Classical.choice (esiste_datiFetta Q v.property (by
            change 1 ≤ Q.dim
            omega))
        have hdim := D.politopo_dim_add_one (by omega)
        have hSimp := D.isSimplicial_of_simplicial hQ (by omega)
        have hlinks := ih D.politopo.dim (by omega) D.politopo rfl hSimp
        have hmapped := hlinks.mapFamily D.neighborEmbedding
        rw [D.boundary_mapFamily_eq_link hQ (by omega)] at hmapped
        rw [show D.politopo.dim = Q.dim - 1 by omega] at hmapped
        exact hmapped
      · intro a _ha hcard
        omega
  exact aux P.dim P rfl hs

end LeanEval.Geometry.PlatonicClassification
