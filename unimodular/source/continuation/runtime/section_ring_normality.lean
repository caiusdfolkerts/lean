module

public import Continuation.Runtime.SectionRingNormalityAlgebra
public import Recovery.Unimodular.GraphicSectionRing.ActualSectionRing

/-!
# Normality of the genuine section ring on a normal integral scheme

The section ring is the existing finite graded sum of actual global
sections, embedded in `K(X)[T]` by a rational Cartier presentation. Its
normality follows from the normality of every actual local ring of `X`.
No positivity, generation, or toric presentation is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

namespace Unimodular.GraphicSectionRing.ActualSections

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricSchemes
open scoped BaseSections

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of k))]

/-- Each embedded local ring is integrally closed in the actual function
field, using its independently proved fraction-field identification. -/
theorem regularAtSubring_isIntegrallyClosedIn (x : X)
    (hx : IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosedIn (regularAtSubring X x) X.functionField := by
  letI := hx
  exact SectionRingNormality.range_isIntegrallyClosedIn
    (X.presheaf.stalk x) X.functionField

/-- The ordinary section ring of a Cartier line bundle on a normal integral
scheme is a normal domain. The hypotheses concern only the actual local
rings of the original scheme. -/
theorem sectionRing_isIntegrallyClosed (C : RationalCartierCocycle X)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed (sectionRing k C) := by
  let ι := Σ i : C.index, {x : X // x ∈ C.openSet i}
  let S : ι → Subring X.functionField := fun a => regularAtSubring X a.2.val
  let g : ι → X.functionField := fun a => C.generator a.1
  apply SectionRingNormality.scaledCoefficients_isIntegrallyClosed
    (sectionRing k C).toSubring S g
  · intro a
    exact regularAtSubring_isIntegrallyClosedIn a.2.val (hX a.2.val)
  · intro p
    change (∀ d, p.coeff d ∈ powerValues k C d) ↔
      ∀ (a : ι) d, p.coeff d / (C.generator a.1 : X.functionField) ^ d ∈
        regularAtSubring X a.2.val
    constructor
    · intro hp a d
      exact (mem_powerValues_iff k C d (p.coeff d)).mp (hp d)
        a.1 a.2.val a.2.property
    · intro hp d
      apply (mem_powerValues_iff k C d (p.coeff d)).mpr
      intro i x hx
      exact hp ⟨i, ⟨x, hx⟩⟩ d

end Unimodular.GraphicSectionRing.ActualSections

#print axioms Unimodular.GraphicSectionRing.ActualSections.sectionRing_isIntegrallyClosed

end
