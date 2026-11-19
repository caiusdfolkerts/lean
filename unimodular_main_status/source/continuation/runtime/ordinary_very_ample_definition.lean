module

public import Continuation.Runtime.SectionPullbackDegreeOne

/-!
# Actual degree-one embeddings of ordinary ample sheaves

The projectivity hypothesis is expressed by its literal finite closed
embedding over the scalar field. This is the projectivity already assumed in
Corollary 6.11. Ordinary ampleness and the checked degree-one section ring
presentation then give a closed section morphism whose actual pullback of
the independently constructed polynomial O(1) is the original input sheaf.

Projective normality and the quadratic ideal of the same embedding are
assembled in GraphicNormalEmbedding. The higher N_p clause is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace Unimodular.ActualVeryAmple

variable (k : Type) [Field k] (X : Scheme)
  [X.Over (Spec (CommRingCat.of k))]

/-- The explicit ordinary projectivity witness used in the statement. -/
def HasFiniteProjectiveEmbedding : Prop :=
  ∃ (I : Type) (_ : Fintype I)
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule I k)),
    IsClosedImmersion f ∧
      f ≫ Unimodular.Projectivity.polynomialProjectiveToSpec k I =
        (X ↘ Spec (CommRingCat.of k))

/-- Actual finite projective embeddings give ordinary properness. -/
theorem isProper_of_projective (h : HasFiniteProjectiveEmbedding k X) :
    IsProper (X ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨I, hI, f, hf, he⟩ := h
  letI := hI
  letI := hf
  rw [← he]
  infer_instance

/-- Literal very ampleness over a field: an actual closed projective
embedding and an isomorphism of its actual pulled-back O(1) with M. -/
def VeryAmpleOverField (M : X.Modules) : Prop :=
  ∃ (I : Type) (_ : Fintype I)
    (f : X ⟶ BondalThomsen.polynomialDegreeOneProj k I),
    IsClosedImmersion f ∧
      f ≫ PaperVerification.ToricSchemes.polynomialProjectiveToSpec k I =
        (X ↘ Spec (CommRingCat.of k)) ∧
      Nonempty ((Scheme.Modules.pullback f).obj
        (BondalThomsen.polynomialProjDegreeOneSheaf k I) ≅ M)

end Unimodular.ActualVeryAmple


end
