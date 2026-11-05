module

public import PaperVerification.RelativeProjectivization
public import PaperVerification.SymmetricProjectiveFrame
public import PaperVerification.SymmetricProjectiveTwisting

/-!
# The cartesian twisting family on a relative projectivization

The local objects are the homogeneous-fraction twisting sheaves on the
actual affine-base projective charts. Restriction is induced by the literal
restriction of module sections. A basis of those sections gives the usual
polynomial projective chart and preserves every integer twist.

This file supplies the local objects and isomorphisms for module-sheaf
descent. Constructing the global twisting line requires the subsequent
descent of this family, including its identity and composition laws.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.RelativeProjectiveTwisting

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles
open ProjectivizationOfModuleSheaf

variable {X : Scheme.{0}} (M : X.Modules) [M.IsQuasicoherent]

/-- The actual integer twist on an affine-base projective chart. -/
def chartTwist (U : X.AffineZariskiSite) (n : ℤ) : (chart M U).Modules :=
  Proj.twistingSheaf
    (Symmetric.Grading.BundleCycles.symmetricGrading Γ(X, U.val) Γ(M, U.val)) n

/-- The restriction morphism is the map of homogeneous fractions induced
by restriction of the original sheaf's sections. -/
def restriction {U V : X.AffineZariskiSite} (i : U ⟶ V) (n : ℤ) :
    chartTwist M V n ⟶
      (Scheme.Modules.pushforward (chartMap M i)).obj (chartTwist M U n) :=
  TwistingSheafMap.pushforwardHom (gradedRestriction M i)
    (gradedRestriction_irrelevant M i) n

/-- Every chart transition pulls back the original integer twist to the
corresponding twist. This is the cartesian property used in descent. -/
def restrictionIso {U V : X.AffineZariskiSite} (i : U ⟶ V) (n : ℤ) :
    (Scheme.Modules.pullback (chartMap M i)).obj (chartTwist M V n) ≅
      chartTwist M U n :=
  SymmetricProjectiveTwisting.generatedMapPullbackIso
    (gradedRestriction M i) (gradedRestriction_irrelevant M i) n

/-- A local frame gives an isomorphism from the actual polynomial projective
space to the relative chart. The frame size is arbitrary. -/
def frameIso (U : X.AffineZariskiSite) {I : Type}
    (b : Basis I Γ(X, U.val) Γ(M, U.val)) :
    Proj (MvPolynomial.homogeneousSubmodule I Γ(X, U.val)) ≅ chart M U :=
  SymmetricProjectiveFrame.projectiveIso b

/-- All integer twists agree under the same local frame isomorphism. -/
def frameTwistingIso (U : X.AffineZariskiSite) {I : Type}
    (b : Basis I Γ(X, U.val) Γ(M, U.val)) (n : ℤ) :
    (Scheme.Modules.pullback (frameIso M U b).hom).obj (chartTwist M U n) ≅
      Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I Γ(X, U.val)) n :=
  SymmetricProjectiveFrame.twistingIso b n

end PaperVerification.RelativeProjectiveTwisting
