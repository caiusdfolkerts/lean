module

public import PaperVerification.ToricMainTheorems
public import PaperVerification.ToricIntrinsicAdjointSections
public import PaperVerification.ToricIntrinsicInvariantCurves

@[expose] public section

/-!
# The intrinsic principal statements with ordinary integer curve degrees

Theorem 1.1 is `ToricGeometry.toric_theorem_1_1`. The two mixed
statements below use the actual degree of each actual restricted line
bundle. Existence and uniqueness of every such degree, and independence
of the auxiliary ample presentation used to construct it, were proved
in the preceding module. The intrinsic section polytopes and the genuine
canonical sheaf keep their definitions independent of the reconstructed fan.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Pointwise BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- Theorem 1.2: prescribed parity for actual ample integral divisors,
with ordinary degrees on all actual invariant integral curves. -/
theorem toric_paper_theorem_1_2
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ)≤T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      (n : ℤ)≤T.invariantCurveDegree D hampleD E C)
    (m : Lattice n)
    (hm : embed n m∈interior
      (intrinsicSectionPolytope k n X.left T.torus.left D+
        intrinsicSectionPolytope k n X.left T.torus.left E))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈intrinsicSectionPolytope k n X.left T.torus.left D ∧
      embed n b∈intrinsicSectionPolytope k n X.left T.torus.left E ∧
      a+b=m ∧ parityClass n a=α :=
  T.toric_theorem_1_2 D E hampleD hampleE
    ((T.invariantCurveDegreesAtLeast_iff D hampleD D n).mpr hD)
    ((T.invariantCurveDegreesAtLeast_iff D hampleD E n).mpr hE) m hm α

/-- Theorem 1.3 in both of the manuscript's formulations, with no
additional existence premise for degrees or for a canonical Cartier
presentation. The tensor product of sections is over the original field. -/
theorem toric_paper_theorem_1_3
    (D E : CartierData X.left) (hampleD : D.IsAmple) (hampleE : E.IsAmple)
    (hD : ∀ C : InvariantIntegralCurve k n X,
      ((n+1 : ℕ) : ℤ)≤T.invariantCurveDegree D hampleD D C)
    (hE : ∀ C : InvariantIntegralCurve k n X,
      ((n+1 : ℕ) : ℤ)≤T.invariantCurveDegree D hampleD E C) :
    ({m : Lattice n | embed n m∈intrinsicSectionPolytope k n X.left T.torus.left D}+
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left E)}=
      {m : Lattice n | embed n m∈interior
        (intrinsicSectionPolytope k n X.left T.torus.left D+
          intrinsicSectionPolytope k n X.left T.torus.left E)}) ∧
      Function.Surjective
        (moduleSectionMultiplicationOver k D.sheaf
          (tensorSheaf E.sheaf (topDifferentialSheaf k X.left n))) :=
  T.toric_theorem_1_3 D E hampleD hampleE
    ((T.invariantCurveDegreesAtLeast_iff D hampleD D (n+1)).mpr hD)
    ((T.invariantCurveDegreesAtLeast_iff D hampleD E (n+1)).mpr hE)

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_paper_theorem_1_2
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.toric_paper_theorem_1_3
