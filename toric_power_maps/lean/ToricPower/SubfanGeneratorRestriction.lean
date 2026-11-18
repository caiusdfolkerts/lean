module

public import ToricPower.SubfanCoherentExtension

/-!
# Classical generators restrict across the actual toric boundary

The essential-surjectivity premise of the general bounded-derived
restriction theorem is discharged by the explicit coherent-image
construction. The result uses the literal categories of coherent
sheaves and their bounded derived categories.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)
  (nonempty : Nonempty fan.cones) (regular : extension.IsRegular)
  (rayFull : IsFullOnRays fan extension)

include nonempty regular rayFull in
/-- The actual coherent restriction functor is essentially surjective. -/
theorem subfan_coherentRestriction_essSurj :
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.restrictFunctor
      (subfanSchemeMap fan extension included)).EssSurj := by
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  constructor
  intro M
  obtain ⟨P,hP,⟨comparison⟩⟩ := subfan_exists_coherent_extension fan extension included
    nonempty regular rayFull M.obj
  refine ⟨⟨P,hP⟩,⟨?_⟩⟩
  exact (SheafOfModules.isFinitePresentation fan.algebraicRealization.ringCatSheaf).isoMk
    comparison

include nonempty regular rayFull in
/-- Any classical generator restricts to a classical generator, with
no assumed extension of complexes or derived equivalence. -/
theorem subfan_coherentDerivedRestriction_generates
    (G : letI := toricScheme_isNoetherian extension
      DbCoh extension.algebraicRealization)
    (generates : letI := toricScheme_isNoetherian extension
      generatesDbCoh G) :
    letI := toricScheme_isNoetherian fan
    letI := toricScheme_isNoetherian extension
    letI := subfanSchemeMap_isOpenImmersion fan extension included
    generatesDbCoh ((coherentDerivedRestriction
      (subfanSchemeMap fan extension included)).obj G) := by
  letI := toricScheme_isNoetherian fan
  letI := toricScheme_isNoetherian extension
  letI := subfanSchemeMap_isOpenImmersion fan extension included
  letI := subfan_coherentRestriction_essSurj fan extension included nonempty regular rayFull
  exact coherentDerivedRestriction_generates_of_essentiallySurjective
    (subfanSchemeMap fan extension included) G generates

end ToricPower

end
