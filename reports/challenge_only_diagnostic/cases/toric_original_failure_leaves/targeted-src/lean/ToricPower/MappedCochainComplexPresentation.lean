module

public import ToricPower.SerrePairingCochains

/-! # The literal object presentation of an additive mapped complex

This small generic equation prevents a concrete coefficient functor
from being unfolded while converting the standard mapped-complex API
into the signed-pairing API.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ToricPower.SerrePairing
universe u v
variable {A : Type u} [Category.{v} A] [Preadditive A]
  (T : A ⥤ A) [T.Additive]

theorem mappedCochainComplex_eq (J : CochainComplex A ℤ) :
    (T.mapHomologicalComplex (.up ℤ)).obj J = mappedCochainComplex T J := rfl

end ToricPower.SerrePairing
end
