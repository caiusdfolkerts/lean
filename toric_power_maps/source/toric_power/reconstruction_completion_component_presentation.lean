module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Basic.Complex.Basic

/-! # Component presentations before actual reconstruction is substituted

The scalar field and ring presentations of complex modules have the same
components. These equalities are checked on arbitrary complexes, before
the original cellular diagrams and their affine sections are inserted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2100] Complex.instRing

namespace ToricPower

/-- Component projection is unchanged by the field-derived ring
presentation, at an arbitrary homological-complex shape. -/
theorem reconstructionComplexComponent_fieldRing
    {ι : Type*} (c : ComplexShape ι)
    {K L : HomologicalComplex
      (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) c}
    (f : K ⟶ L) (q : ι) :
    HomologicalComplex.Hom.f (V := ModuleCat.{0} ℂ) (c := c) f q =
      HomologicalComplex.Hom.f
        (V := @ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) (c := c) f q :=
  rfl

/-- This presentation comparison also retains the native natural-number
cochain shape of the scalar complex. -/
theorem reconstructionCochainComponent_fieldRing_natShape
    {K L : CochainComplex
      (@ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) ℕ}
    (f : K ⟶ L) (q : ℕ) :
    HomologicalComplex.Hom.f (V := ModuleCat.{0} ℂ)
        (c := ComplexShape.up ℕ) f q =
      HomologicalComplex.Hom.f
        (V := @ModuleCat.{0} ℂ Complex.instField.toDivisionRing.toRing) f q :=
  rfl

/-- A triple comparison has precisely the composite of its three
component maps, with the complexes still arbitrary. -/
theorem reconstructionTripleIso_component
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι}
    {K L M N : HomologicalComplex C c}
    (e : K ≅ L) (f : L ≅ M) (g : M ≅ N) (q : ι) :
    (e ≪≫ f ≪≫ g).hom.f q = e.hom.f q ≫ f.hom.f q ≫ g.hom.f q := by
  simp only [Iso.trans_hom, HomologicalComplex.comp_f, Category.assoc]

end ToricPower

end
