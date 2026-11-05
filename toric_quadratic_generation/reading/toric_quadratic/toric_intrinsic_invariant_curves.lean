module

public import PaperVerification.ToricInvariantOrbitClosure
public import PaperVerification.ToricIntrinsicMixedTheorems
public import PaperVerification.ToricRationalCurveDegreeExistence

@[expose] public section

/-!
# Ordinary degrees on all intrinsic invariant curves

Every actual invariant integral curve of a smooth proper split toric
scheme with an ample Cartier divisor is isomorphic over its original
field to P¹.  Consequently every restricted invertible sheaf has its
unique ordinary O(d) degree.  The geometric degree-bound predicate used
in the principal theorems is exactly the inequality for these integers;
it cannot hold merely because some invariant curve has no degree witness.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricGeometry
open scoped Classical

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

include T in
/-- This classifies an arbitrary genuine invariant integral curve, with
no toric presentation or normality premise on the curve itself. -/
theorem invariantCurve_exists_projectiveLineIso
    (A : CartierData X.left) (hA : A.IsAmple)
    (C : InvariantIntegralCurve k n X) :
    ∃ e : C.curve.left ≅ projectiveLineScheme k,
      e.hom.IsOver (Spec (CommRingCat.of k)) := by
  obtain ⟨«Σ», hpure, e, htorus, hequiv⟩ := T.exists_equivariant_completeFan A hA
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.hom := hequiv
  letI : IsModHom (splitTorusOver k (Fin n → ℤ)) e.symm.hom :=
    inferInstanceAs (IsModHom (splitTorusOver k (Fin n → ℤ)) e.inv)
  exact «Σ».invariantIntegralCurve_exists_projectiveLineIso k hpure (C.mapIso e.symm)

include T in
/-- The ordinary degree exists uniquely on every invariant curve for
every actual restricted Cartier line bundle. -/
theorem invariantCurve_restriction_existsUnique_degree
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    ∃! d : ℤ, RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d := by
  obtain ⟨e, he⟩ := T.invariantCurve_exists_projectiveLineIso A hA C
  letI := he
  exact restrictedCartier_existsUnique_degree k D C.inclusion.left e

/-- The ordinary integer degree of the restricted line bundle.  The
ample divisor is used only to prove the classification and existence;
the uniqueness theorem below removes this auxiliary choice. -/
def invariantCurveDegree
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) : ℤ :=
  Classical.choose (T.invariantCurve_restriction_existsUnique_degree A hA D C)

theorem invariantCurveDegree_spec
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    RationalCurveHasDegree k
      ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf)
      (T.invariantCurveDegree A hA D C) :=
  (Classical.choose_spec (T.invariantCurve_restriction_existsUnique_degree A hA D C)).1

theorem invariantCurveDegree_eq_iff
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) (d : ℤ) :
    T.invariantCurveDegree A hA D C = d ↔
      RationalCurveHasDegree k
        ((Scheme.Modules.pullback C.inclusion.left).obj D.sheaf) d := by
  constructor
  · intro h
    rw [← h]
    exact T.invariantCurveDegree_spec A hA D C
  · intro h
    exact rationalCurveHasDegree_unique k (T.invariantCurveDegree_spec A hA D C) h

theorem invariantCurveDegree_independent_ample
    (A B : CartierData X.left) (hA : A.IsAmple) (hB : B.IsAmple)
    (D : CartierData X.left) (C : InvariantIntegralCurve k n X) :
    T.invariantCurveDegree A hA D C = T.invariantCurveDegree B hB D C :=
  rationalCurveHasDegree_unique k (T.invariantCurveDegree_spec A hA D C)
    (T.invariantCurveDegree_spec B hB D C)

/-- The theorem hypothesis is exactly an inequality for the ordinary
degree of every actual invariant curve, with existence already proved. -/
theorem invariantCurveDegreesAtLeast_iff
    (A : CartierData X.left) (hA : A.IsAmple)
    (D : CartierData X.left) (bound : ℕ) :
    InvariantCurveDegreesAtLeast k n X D bound ↔
      ∀ C : InvariantIntegralCurve k n X,
        (bound : ℤ) ≤ T.invariantCurveDegree A hA D C := by
  constructor
  · intro h C
    exact h C _ (T.invariantCurveDegree_spec A hA D C)
  · intro h C d hd
    rw [← (T.invariantCurveDegree_eq_iff A hA D C d).mpr hd]
    exact h C

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurve_exists_projectiveLineIso
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurve_restriction_existsUnique_degree
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.invariantCurveDegreesAtLeast_iff
