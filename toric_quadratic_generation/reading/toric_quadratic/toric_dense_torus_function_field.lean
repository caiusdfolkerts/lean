module

public import PaperVerification.ToricFunctionFieldBridge
public import PaperVerification.ToricTorusAction
public import PaperVerification.ToricLaurentPicard

@[expose] public section

/-!
# The function field of a scheme containing the actual split torus

The coordinate ring is the ordinary group algebra of the integral
character lattice. Its domain property is proved from the iterated
Laurent presentation, so no additional domain hypothesis is attached to
the torus statement.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n → ℤ) ⟶ X) [hj : IsOpenImmersion j]

/-- Restriction along the actual open torus identifies rational
functions with the fraction field of its character algebra. -/
def torusOpenFunctionFieldEquiv :
    X.functionField ≃+* FractionRing (torusCoordinateRing k n) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv
    (CommRingCat.of (torusCoordinateRing k n)) j

/-- On global regular functions this is the literal restriction to the
torus, followed by the canonical fraction-field embedding. -/
@[simp] theorem torusOpenFunctionFieldEquiv_germ_top (a : Γ(X,⊤)) :
    torusOpenFunctionFieldEquiv k n X j (X.germToFunctionField ⊤ a) =
      algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
          (j.appTop a)) := by
  letI := torusCoordinateRing_isDomain k n
  letI : IsOpenImmersion
      (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj
  exact affineOpenFunctionFieldEquiv_germ_top
    (CommRingCat.of (torusCoordinateRing k n)) j a

/-- Equality of rational functions can be checked on the actual open
torus. This is injectivity of a constructed equivalence, not a hypothesis. -/
theorem rationalFunction_eq_iff_on_torus (f g : X.functionField) :
    f=g ↔ torusOpenFunctionFieldEquiv k n X j f =
      torusOpenFunctionFieldEquiv k n X j g :=
  (torusOpenFunctionFieldEquiv k n X j).injective.eq_iff.symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusOpenFunctionFieldEquiv
