module

public import ToricPower.AffineConeCoresolution
public import Mathlib.Basic.Complex.Basic

/-! # A fixed complex presentation of the genuine affine coresolution

The original finite affine replacement is retained as a whole functor.
Its complex structures are identified while the scheme and cover remain
abstract, before any toric fan or normalized Hom diagram is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

attribute [local instance 2000] Abelian.toPreadditive
attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms

namespace ToricPower

universe u v

variable {X : Scheme.{u}} {I : Type v}
  (opens : I → X.Opens) [∀ i, IsAffineHom (opens i).ι]

/-- The actual affine coresolution, with its complex functor type fixed
before any concrete scheme or cover is substituted. -/
def canonicalAffineCoresolution (l : List I) :
    CochainComplex (QCoh X) ℤ ⥤ CochainComplex (QCoh X) ℤ :=
  affineConeCoresolution opens l

/-- The fixed presentation is the original whole affine replacement. -/
def canonicalAffineCoresolutionIso (l : List I) :
    canonicalAffineCoresolution opens l ≅ affineConeCoresolution opens l :=
  Iso.refl _

end ToricPower

end
