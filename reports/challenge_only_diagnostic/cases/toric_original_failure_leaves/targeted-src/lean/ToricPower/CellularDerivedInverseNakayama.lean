module

public import ToricPower.CellularEnoughInjectives
public import ToricPower.CellularDerivedHom

/-!
# The actual derived inverse Nakayama functor

The functor is the ordinary right-derived functor of Hom from the
co-representable incidence diagrams. Enough injectives is proved for
the actual diagram category, so the derived functor is unconditional.
This module alone asserts neither Serre duality nor preservation of
bounded finite-dimensional objects; those require the finite-resolution
and pairing comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w
variable (k : Type u) [Field k] (C : Type u) [Category.{u} C]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]

abbrev derivedInverseNakayamaPlus :
    DerivedCategory.Plus (C ⥤ ModuleCat.{u} k) ⥤
      DerivedCategory.Plus (C ⥤ ModuleCat.{u} k) :=
  (inverseNakayama k (C := C)).rightDerivedFunctorPlus


end ToricPower.Cellular

end
