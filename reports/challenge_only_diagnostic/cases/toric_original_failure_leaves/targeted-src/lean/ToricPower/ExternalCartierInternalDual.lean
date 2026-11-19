module

public import ToricPower.SchemeInversePairingPullback
public import ToricPower.TensorProductInversePairing
public import ToricPower.CartierTensorPairing

/-!
# The actual internal dual of an exterior Cartier product

The inverse label is an exterior product of the two inverse Cartier
sheaves. Rational multiplication gives both evaluation isomorphisms;
canonical pullback and middle-factor interchange transport them to the
product. The resulting dual isomorphism is natural for actual maps
compatible with those evaluations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

local instance cartierSheafQuasicoherent {T : Scheme.{u}} [IsIntegral T]
    (D : CartierDivisor T) : D.sheaf.IsQuasicoherent := by
  letI := D.isInvertible_sheaf
  infer_instance

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (p : Z ⟶ X) (q : Z ⟶ Y)

/-- The literal exterior product with the ordinary scheme pullbacks. -/
def externalCartierSheaf (D : CartierDivisor X) (E : CartierDivisor Y) : Z.Modules :=
  (Scheme.Modules.pullback p).obj D.sheaf ⊗
    (Scheme.Modules.pullback q).obj E.sheaf

/-- Evaluation is the tensor of the two pulled-back rational pairings. -/
def externalCartierTensorNegIsoUnit (D : CartierDivisor X) (E : CartierDivisor Y) :
    externalCartierSheaf p q D E ⊗ externalCartierSheaf p q (-D) (-E) ≅
      𝟙_ Z.Modules :=
  tensorProductPairingIso
    (pullbackPairingIso p (cartierTensorNegIsoUnit D))
    (pullbackPairingIso q (cartierTensorNegIsoUnit E))

def externalCartierNegTensorIsoUnit (D : CartierDivisor X) (E : CartierDivisor Y) :
    externalCartierSheaf p q (-D) (-E) ⊗ externalCartierSheaf p q D E ≅
      𝟙_ Z.Modules :=
  tensorProductPairingIso
    (pullbackPairingIso p (cartierNegTensorIsoUnit D))
    (pullbackPairingIso q (cartierNegTensorIsoUnit E))

/-- The actual internal dual is the actual exterior inverse label. -/
def externalCartierInternalDualIso (D : CartierDivisor X) (E : CartierDivisor Y) :
    externalCartierSheaf p q (-D) (-E) ≅
      (internalDual Z.Modules).obj (op (externalCartierSheaf p q D E)) :=
  inverseTensorInternalDualIso _ _
    (externalCartierNegTensorIsoUnit p q D E)
    (externalCartierTensorNegIsoUnit p q D E)

/-- The exterior product of the specified source maps. -/
def externalCartierMap {D D' : CartierDivisor X} {E E' : CartierDivisor Y}
    (a : D.sheaf ⟶ D'.sheaf) (b : E.sheaf ⟶ E'.sheaf) :
    externalCartierSheaf p q D E ⟶ externalCartierSheaf p q D' E' :=
  (Scheme.Modules.pullback p).map a ⊗ₘ (Scheme.Modules.pullback q).map b

/-- The two genuine factor-pairing squares give the exact dual-map
square for the exterior product. -/
theorem externalCartierInternalDualIso_naturality
    {D D' : CartierDivisor X} {E E' : CartierDivisor Y}
    (a : D.sheaf ⟶ D'.sheaf) (b : E.sheaf ⟶ E'.sheaf)
    (a' : (-D').sheaf ⟶ (-D).sheaf) (b' : (-E').sheaf ⟶ (-E).sheaf)
    (pairingD : D.sheaf ◁ a' ≫ (cartierTensorNegIsoUnit D).hom =
      a ▷ (-D').sheaf ≫ (cartierTensorNegIsoUnit D').hom)
    (pairingE : E.sheaf ◁ b' ≫ (cartierTensorNegIsoUnit E).hom =
      b ▷ (-E').sheaf ≫ (cartierTensorNegIsoUnit E').hom) :
    (externalCartierInternalDualIso p q D' E').hom ≫
        (internalDual Z.Modules).map (externalCartierMap p q a b).op =
      externalCartierMap p q a' b' ≫ (externalCartierInternalDualIso p q D E).hom := by
  apply inverseTensorInternalDualIso_naturality
  exact tensorProductPairingIso_naturality _ _ _ _
    ((Scheme.Modules.pullback p).map a) ((Scheme.Modules.pullback q).map b)
    ((Scheme.Modules.pullback p).map a') ((Scheme.Modules.pullback q).map b')
    (pullbackPairingIso_naturality p _ _ a a' pairingD)
    (pullbackPairingIso_naturality q _ _ b b' pairingE)

end ToricPower

end
