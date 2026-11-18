module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Basic.Complex.Basic

/-! # Native isomorphism components in the reconstruction comparison

Both the isomorphism projection and its complex component are compared
before any actual scalar cellular isomorphism is substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

attribute [local instance 2100] Complex.instRing

namespace ToricPower

/-- The native scalar cochain isomorphism has the same forward component
in the fixed-ring category with the displayed natural-number shape. -/
theorem reconstructionCochainIsoHom_fieldRing_natShape
    {K L : CochainComplex
      (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) ℕ}
    (e : K ≅ L) (q : ℕ) :
    HomologicalComplex.Hom.f (V := ModuleCat.{0} ℂ) (c := ComplexShape.up ℕ)
        (Iso.hom (C := HomologicalComplex (ModuleCat.{0} ℂ) (ComplexShape.up ℕ)) e) q =
      HomologicalComplex.Hom.f
        (V := @ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing)
        (Iso.hom (C := CochainComplex
          (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) ℕ) e) q :=
  rfl

/-- The native inverse component is retained at every complex shape. -/
theorem reconstructionComplexIsoInv_fieldRing
    {ι : Type*} (c : ComplexShape ι)
    {K L : HomologicalComplex
      (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) c}
    (e : K ≅ L) (q : ι) :
    HomologicalComplex.Hom.f (V := ModuleCat.{0} ℂ) (c := c)
        (Iso.inv (C := HomologicalComplex (ModuleCat.{0} ℂ) c) e) q =
      HomologicalComplex.Hom.f
        (V := @ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) (c := c)
        (Iso.inv (C := HomologicalComplex
          (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) c) e) q :=
  rfl

end ToricPower

end
