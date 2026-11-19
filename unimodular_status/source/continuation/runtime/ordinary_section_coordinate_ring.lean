module

public import Continuation.Runtime.OrdinaryDegreeOneSections
public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing

/-! # The ordinary section-coordinate map

The complete generic definitions and comparison from SectionCoordinateRing,
with their original statements, separated from its graphic applications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections

namespace Unimodular.GraphicSectionRing.ActualSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))] (C : RationalCartierCocycle X)
  {ι : Type u}

/-- The genuine degree-one homogeneous element of a given global section. -/
def degreeOneSectionElement (s : Γ(C.sheaf, ⊤)) : sectionRing k C :=
  homogeneousSection k C 1 ⟨s.val, by
    intro i x hx
    simpa only [RationalCartierCocycle.pow, pow_one] using s.property i x hx⟩

@[simp] theorem degreeOneSectionElement_val (s : Γ(C.sheaf, ⊤)) :
    (degreeOneSectionElement k C s).val =
      AddMonoidAlgebra.single 1 (C.toCartierData.sectionValue ⊤ s) := rfl

/-- Polynomial coordinates evaluate in the actual section ring by genuine
degree-one sections. This definition is independent of any surjectivity or
normality assertion. -/
def degreeOneSectionMap (s : ι → Γ(C.sheaf, ⊤)) :
    MvPolynomial ι k →ₐ[k] sectionRing k C :=
  MvPolynomial.aeval (degreeOneSectionElement k C ∘ s)

@[simp] theorem degreeOneSectionMap_X (s : ι → Γ(C.sheaf, ⊤)) (i : ι) :
    degreeOneSectionMap k C s (MvPolynomial.X i) = degreeOneSectionElement k C (s i) :=
  MvPolynomial.aeval_X _ _

/-- Recovering the original degree-one sections does not change a
homogeneous polynomial section-ring presentation. -/
theorem degreeOneSectionMap_eq (Φ : MvPolynomial ι k →ₐ[k] sectionRing k C)
    (hX : ∀ (i : ι) (d : ℕ), d ≠ 1 →
      (Φ (MvPolynomial.X i)).val.coeff d = 0) :
    degreeOneSectionMap k C (polynomialDegreeOneSection k C Φ) = Φ := by
  apply MvPolynomial.algHom_ext
  intro i
  apply Subtype.ext
  rw [degreeOneSectionMap_X, degreeOneSectionElement_val,
    polynomialDegreeOneSection_single k C Φ hX i]

/-- The ordinary homogeneous coordinate quotient attached to actual
sections. Its identification with an embedding is a separate theorem. -/
abbrev sectionCoordinateRing (s : ι → Γ(C.sheaf, ⊤)) :=
  MvPolynomial ι k ⧸ RingHom.ker (degreeOneSectionMap k C s).toRingHom

end Unimodular.GraphicSectionRing.ActualSections

end
