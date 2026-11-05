module

public import paper_verification.toric028

@[expose] public section

/-!
# Theorem 1.1 on an abstract lattice

The original lattice may be any abelian group isomorphic to `ℤⁿ`. Its
realification is the actual tensor product `ℝ ⊗[ℤ] M`. The hypotheses below
use the actual convex hull, actual nondegenerate segment faces, and the
primitive edge-basis condition before any coordinates are chosen.

The lattice-content expression in the edge bound is independent of the
chosen isomorphism, by `latticeLength_independent_of_basis`. The proof
transports both hypotheses and both conclusions through the already proved
equivalences; it does not assume an additional real coordinate map.
-/

noncomputable section

namespace ToricQuadratic

open Set
open PaperVerification.ToricGeometry
open PaperVerification.ToricExchange
open PaperVerification.ToricCoordinateTransport

/-- Theorem 1.1 for a finite full-dimensional polytope in any rank-`n`
lattice. IDP retains every positive degree, and the kernel is that of the
actual polynomial map to `k[M][t]` over the original lattice `M`. -/
theorem normal_and_quadratic_in_lattice
    (k : Type*) [Field k]
    {M : Type*} [AddCommGroup M]
    (n : ℕ) (hn : 1 ≤ n) (e : M ≃+ Lattice n)
    (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ
      (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤)
    (hsmooth : SmoothEdgeBasis n realificationEmbedding
      (convexHull ℝ (realificationEmbedding '' (s : Set M))))
    (hbound : ∀ v w : M,
      realificationEmbedding v ≠ realificationEmbedding w →
      IsExtreme ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M)))
        (segment ℝ (realificationEmbedding v) (realificationEmbedding w)) →
      n ≤ latticeContent (e (w - v))) :
    IntegerDecompositionProperty realificationEmbedding
        (convexHull ℝ (realificationEmbedding '' (s : Set M))) ∧
      RingHom.ker (paperToricMap (latticePoints realificationEmbedding
        (convexHull ℝ (realificationEmbedding '' (s : Set M)))) k) =
      polynomialQuadraticIdeal (latticePoints realificationEmbedding
        (convexHull ℝ (realificationEmbedding '' (s : Set M)))) k := by
  have hP : (coordinatePolytope e s hs hfull).Smooth :=
    (coordinatePolytope_smooth_iff e s hs hfull).mpr hsmooth
  have hlength : (coordinatePolytope e s hs hfull).EdgesAtLeast n :=
    (coordinatePolytope_edgesAtLeast_iff e s hs hfull n).mpr hbound
  exact (coordinatePolytope_principal_conclusions_iff e s hs hfull k).mp
    (toric_theorem_1_1 k n hn (coordinatePolytope e s hs hfull) hP hlength)

end ToricQuadratic
