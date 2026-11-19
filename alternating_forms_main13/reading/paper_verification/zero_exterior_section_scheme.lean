module

public import PaperVerification.LineExteriorSquareZero
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The zero scheme of sections whose exterior-sheaf domain is zero

The defining ideals are the images of the actual sheaf morphisms on affine
opens.  The proof establishes that every such image is zero, before using
the ideal-sheaf constructor.  In particular no general claim is made that
an arbitrary family of module images satisfies quasi-coherent descent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PaperVerification.ZeroExteriorSectionScheme

universe u v

variable {X : Scheme.{u}} {L : X.Modules} {ι : Type v}
  (φ : ι → (LineExteriorSquareZero.exteriorSquare L ⟶
    SheafOfModules.unit X.ringCatSheaf))

local instance (U : X.Opens) : CommRing (X.ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing Γ(X, U))

local instance (U : X.Opens) :
    CommRing ((SheafOfModules.unit X.ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(X, U))

/-- The affine equations are the full images of the actual sheaf functionals. -/
def affineImageIdeal (U : X.affineOpens) : Ideal Γ(X, U) :=
  ⨆ i, LinearMap.range ((φ i).val.app (op U.1)).hom

/-- The ideal sheaf determined from those affine equations.  Its exact
equality with the affine image ideals is proved below in the zero-domain case. -/
def imageIdeal : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (affineImageIdeal φ)

theorem affineImageIdeal_eq_bot (hL : IsZero (LineExteriorSquareZero.exteriorSquare L))
    (U : X.affineOpens) : affineImageIdeal φ U = ⊥ := by
  have hφ : ∀ i, φ i = 0 := fun i ↦ hL.eq_zero_of_src (φ i)
  unfold affineImageIdeal
  simp only [hφ]
  apply iSup_eq_bot.mpr
  intro i
  exact LinearMap.range_zero

theorem imageIdeal_eq_bot (hL : IsZero (LineExteriorSquareZero.exteriorSquare L)) :
    imageIdeal φ = ⊥ := by
  apply le_antisymm _ bot_le
  intro U
  exact (Scheme.IdealSheafData.ideal_ofIdeals_le (affineImageIdeal φ) U).trans
    (le_of_eq (affineImageIdeal_eq_bot φ hL U))

/-- There is no loss of affine equations in the ideal-sheaf construction. -/
theorem imageIdeal_ideal (hL : IsZero (LineExteriorSquareZero.exteriorSquare L))
    (U : X.affineOpens) : (imageIdeal φ).ideal U = affineImageIdeal φ U := by
  rw [imageIdeal_eq_bot φ hL, affineImageIdeal_eq_bot φ hL]
  rfl

/-- The resulting closed zero subscheme is the whole original scheme. -/
def zeroSchemeIso (hL : IsZero (LineExteriorSquareZero.exteriorSquare L)) :
    (imageIdeal φ).subscheme ≅ X := by
  letI : IsIso (imageIdeal φ).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (imageIdeal_eq_bot φ hL)
  exact asIso (imageIdeal φ).subschemeι

/-- This comparison is the actual closed immersion, so is over the original ambient scheme. -/
theorem zeroSchemeIso_hom (hL : IsZero (LineExteriorSquareZero.exteriorSquare L)) :
    (zeroSchemeIso φ hL).hom = (imageIdeal φ).subschemeι := rfl

end PaperVerification.ZeroExteriorSectionScheme
