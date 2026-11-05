module

public import paper_verification.toric009

@[expose] public section

/-!
# Literal algebraic endpoint for the long-edge theorem

This file displays the all-degree IDP statement and the actual polynomial-kernel
equality without hiding either conclusion behind a named target proposition.
The algebraic proof is valid over every commutative coefficient ring.
-/

namespace ToricQuadratic

open PaperVerification.ToricGeometry
open PaperVerification.ToricExchange

theorem normal_and_quadratic_over_ring
    (R : Type*) [CommRing R]
    (n : ℕ) (P : LatticePolytope n)
    (hP : P.Smooth) (hbound : P.EdgesAtLeast n) :
    (∀ k : ℕ, 1 ≤ k → ∀ z : Lattice n,
      (∃ x ∈ P.carrier, embed n z = (k : ℝ) • x) →
      ∃ s : Multiset (latticePoints (embed n) P.carrier),
        s.card = k ∧ total (latticePoints (embed n) P.carrier) s = z) ∧
    RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) R) =
      Ideal.span {f | ∃ a b c d : latticePoints (embed n) P.carrier,
        (a : Lattice n) + b = (c : Lattice n) + d ∧
        f = MvPolynomial.X a * MvPolynomial.X b -
          MvPolynomial.X c * MvPolynomial.X d} := by
  have hidp := P.integerDecomposition_of_smooth_long_edges hP hbound
  have hparity := P.faceParity_of_mixed_parity hP hbound toric_theorem_1_2_polytope
  have hadjoint := P.faceAdjoint_of_mixed_adjoint hP hbound toric_theorem_1_3_polytope
  exact ⟨hidp, (P.proposition2_1 R hidp hparity hadjoint).2⟩

end ToricQuadratic

#print axioms ToricQuadratic.normal_and_quadratic_over_ring
