module

public import ToricPower.CartierSourceFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Actual internal Hom of Cartier sources is inverse tensoring

The comparison is the canonical uniqueness map between the genuine
Cartier tensor adjunction and the genuine closed-category adjunction.
Naturality in every original source arrow follows from the exact
composition law for mates. It is therefore valid before taking sections
or cohomology, and for arbitrary module-sheaf coefficients.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual internal Hom functor on the original Cartier line sheaves. -/
def cartierSourcesInternalHom : (CartierSources X)ᵒᵖ ⥤ X.Modules ⥤ X.Modules :=
  (cartierSourcesQuasicoherent X ⋙ quasicoherentInclusion X).op ⋙
    MonoidalClosed.internalHom

/-- Inverse tensor and internal Hom agree on every source morphism,
by actual adjunction mates rather than objectwise duality alone. -/
def cartierSourcesInverseInternalHomIso :
    cartierSourcesInverseTensor X ≅ cartierSourcesInternalHom X :=
  NatIso.ofComponents (fun D =>
    conjugateIsoEquiv
      (cartierTensorEquivalence (cartierSourceDivisor X D.unop)).toAdjunction
      (ihom.adjunction (cartierSourceDivisor X D.unop).sheaf) (Iso.refl _)) (by
    intro D E f
    let adjD := (cartierTensorEquivalence (cartierSourceDivisor X D.unop)).toAdjunction
    let adjE := (cartierTensorEquivalence (cartierSourceDivisor X E.unop)).toAdjunction
    let closedD := ihom.adjunction (cartierSourceDivisor X D.unop).sheaf
    let closedE := ihom.adjunction (cartierSourceDivisor X E.unop).sheaf
    let α := (tensoringLeft X.Modules).map f.unop.hom
    change conjugateEquiv adjD adjE α ≫ conjugateEquiv adjE closedE (𝟙 _) =
      conjugateEquiv adjD closedD (𝟙 _) ≫ conjugateEquiv closedD closedE α
    rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.id_comp, Category.comp_id])

end ToricPower

end
