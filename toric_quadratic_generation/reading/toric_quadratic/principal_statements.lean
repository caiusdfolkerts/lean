module

public import PaperVerification

@[expose] public section

/-!
# Quadratic generation for smooth polytopes with long edges

This is the reader's entry point. The declarations below expose the
principal statements without hiding their quantifiers in a named
proposition. The intrinsic divisor statements at the end retain the actual
schemes, invariant curves, line bundles, and multiplication of global sections.

The mathematical proofs are in the imported development. The accompanying
note and source map identify their correspondence with the manuscript.
-/

noncomputable section

namespace ToricQuadratic

open PaperVerification.ToricGeometry
open PaperVerification.ToricExchange
open scoped Pointwise

/-- Theorem 1.1. Every positive dimension, every field, all positive
dilations, and the actual kernel of `X a ↦ χ^a t` are retained. -/
theorem normal_and_quadratic
    (k : Type*) [Field k] (n : ℕ) (hn : 1 ≤ n)
    (P : LatticePolytope n) (hP : P.Smooth) (hbound : P.EdgesAtLeast n) :
    P.HasIDP ∧
      RingHom.ker (paperToricMap (latticePoints (embed n) P.carrier) k) =
        polynomialQuadraticIdeal (latticePoints (embed n) P.carrier) k :=
  toric_theorem_1_1 k n hn P hP hbound

/-- Theorem 1.2 in its equivalent polytope form, with a genuine
quotient class in the character lattice modulo twice that lattice. -/
theorem prescribed_parity
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast n) (hboundQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ P.carrier ∧ embed n b ∈ Q.carrier ∧
      a + b = m ∧ parityClass n a = α :=
  toric_theorem_1_2_quotient_classes n P Q hP hQ hfan
    hboundP hboundQ m hm α

/-- Theorem 1.3 in its equivalent polytope form. This is the equality
of the two actual sets of lattice points, including both inclusions. -/
theorem adjoint_decomposition
    (n : ℕ) (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    {m : Lattice n | embed n m ∈ P.carrier} +
        {m : Lattice n | embed n m ∈ interior Q.carrier} =
      {m : Lattice n | embed n m ∈ interior (P.minkowskiSum Q)} :=
  toric_theorem_1_3_polytope_sets n P Q hP hQ hfan hboundP hboundQ

/-! ## The original divisor formulations

These declarations have precisely the original theorem types: arbitrary
smooth proper split-toric schemes over a field, ample Cartier divisors, and
ordinary integer degrees on all invariant integral curves. The second
theorem includes surjectivity of multiplication of sections with the
canonical factor defined as the top exterior power of Kähler differentials.
-/

section Divisors

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricSchemes
open scoped BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

/-- Theorem 1.2 as stated for divisors on a smooth projective toric variety.
The degree inequalities range over every actual invariant integral curve. -/
theorem toric_paper_theorem_1_2
    (T : SplitToricEmbedding k n X)
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ) ≤ T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ) ≤ T.invariantCurveDegree D hampleD E C)
    (m : Lattice n)
    (hm : embed n m ∈ interior
      (intrinsicSectionPolytope k n X.left T.torus.left D +
        intrinsicSectionPolytope k n X.left T.torus.left E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a ∈ intrinsicSectionPolytope k n X.left T.torus.left D ∧
      embed n b ∈ intrinsicSectionPolytope k n X.left T.torus.left E ∧
      a + b = m ∧ parityClass n a = α :=
  T.toric_paper_theorem_1_2 D E hampleD hampleE hD hE m hm α

/-- Theorem 1.3 as stated for divisors: the literal lattice-point equality
and surjectivity of the actual tensor product map on global sections.
The canonical factor is the top exterior power of Kähler differentials. -/
theorem toric_paper_theorem_1_3
    (T : SplitToricEmbedding k n X)
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      ((n + 1 : ℕ) : ℤ) ≤ T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      ((n + 1 : ℕ) : ℤ) ≤ T.invariantCurveDegree D hampleD E C) :
    ({m : Lattice n | embed n m ∈ intrinsicSectionPolytope k n X.left T.torus.left D} +
      {m : Lattice n | embed n m ∈ interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)} =
      {m : Lattice n | embed n m ∈ interior
        (intrinsicSectionPolytope k n X.left T.torus.left D +
          intrinsicSectionPolytope k n X.left T.torus.left E)}) ∧
      Function.Surjective
        (moduleSectionMultiplicationOver k D.sheaf
          (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) :=
  T.toric_paper_theorem_1_3 D E hampleD hampleE hD hE

end Divisors

end ToricQuadratic
