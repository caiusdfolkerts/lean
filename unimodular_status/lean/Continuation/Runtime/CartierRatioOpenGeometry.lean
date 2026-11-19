module

public import Continuation.Runtime.SectionEmbeddingRecovered

/-!
# Regular ratios on Cartier nonvanishing opens

A quotient of two Cartier sections is an ordinary global regular function
where its denominator is nonvanishing. Its principal open is the overlap
of the two section opens. If the numerator's section open is affine, that
overlap is affine without assuming affineness of the denominator's open.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

/-- Passing from sections on an open to global sections of its actual
open subscheme preserves their actual rational value. -/
theorem open_germToFunctionField_topIso_inv {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    U.toScheme.germToFunctionField ⊤ (U.topIso.inv a) =
      dominantFunctionFieldMap U.ι (X.germToFunctionField U a) := by
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  letI : Nonempty (U.ι ⁻¹ᵁ U) := dominant_preimage_nonempty U.ι U
  have hmap : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  rw [← hmap]
  change U.toScheme.germToFunctionField ⊤
      (U.toScheme.presheaf.map (homOfLE U.ι_preimage_self.ge).op (U.ι.app U a)) = _
  rw [germToFunctionField_restrict]
  exact (dominantFunctionFieldMap_germ U.ι U a).symm

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The literal global function on the denominator's open subscheme. -/
def ratioGlobalSection (t s : Γ(C.sheaf, ⊤)) :
    Γ((C.nonvanishingOpen s).toScheme, ⊤) :=
  (C.nonvanishingOpen s).topIso.inv (C.ratioSection t s)

@[simp]
theorem ratioGlobalSection_self (s : Γ(C.sheaf, ⊤)) :
    C.ratioGlobalSection s s = 1 := by
  rw [ratioGlobalSection, C.ratioSection_self]
  exact map_one _

/-- The rational value of the ordinary global ratio is exactly the
quotient of the original section values, transported by the inclusion. -/
theorem ratioGlobalSection_value (t s : Γ(C.sheaf, ⊤))
    [Nonempty (C.nonvanishingOpen s)] :
    letI : IsIntegral (C.nonvanishingOpen s).toScheme :=
      isIntegral_of_isOpenImmersion (C.nonvanishingOpen s).ι
    (C.nonvanishingOpen s).toScheme.germToFunctionField ⊤
        (C.ratioGlobalSection t s) =
      dominantFunctionFieldMap (C.nonvanishingOpen s).ι
        (C.toCartierData.sectionValue ⊤ t / C.toCartierData.sectionValue ⊤ s) := by
  letI : IsIntegral (C.nonvanishingOpen s).toScheme :=
    isIntegral_of_isOpenImmersion (C.nonvanishingOpen s).ι
  rw [ratioGlobalSection, open_germToFunctionField_topIso_inv,
    C.ratioSection_value]

/-- On the actual open subscheme, the ratio's principal open is exactly
the inverse image of the numerator's nonvanishing open. -/
theorem ratioGlobalSection_basicOpen (t s : Γ(C.sheaf, ⊤)) :
    (C.nonvanishingOpen s).toScheme.basicOpen (C.ratioGlobalSection t s) =
      (C.nonvanishingOpen s).ι ⁻¹ᵁ C.nonvanishingOpen t := by
  let V := C.nonvanishingOpen s
  apply V.ι.image_injective
  dsimp only []
  erw [ratioGlobalSection, Scheme.Opens.ι_image_basicOpen_topIso_inv,
    C.ratioSection_basicOpen, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

/-- Affineness of a section open gives affineness of its overlap with
every other section open, using the reciprocal ratio as a principal
function on the affine open. -/
theorem ratioGlobalSection_basicOpen_isAffine (t s : Γ(C.sheaf, ⊤))
    (ht : IsAffineOpen (C.nonvanishingOpen t)) :
    IsAffineOpen ((C.nonvanishingOpen s).toScheme.basicOpen
      (C.ratioGlobalSection t s)) := by
  apply (C.nonvanishingOpen s).ι.isAffineOpen_iff_of_isOpenImmersion.mp
  erw [ratioGlobalSection, Scheme.Opens.ι_image_basicOpen_topIso_inv,
    C.ratioSection_basicOpen, inf_comm, ← C.ratioSection_basicOpen s t]
  exact ht.basicOpen _

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.ratioGlobalSection_basicOpen_isAffine
