module

public import ToricPower.CellularHomDiagram
public import Mathlib.Basic.Complex.Basic

/-! # A concrete complex-scalar presentation of the intrinsic Hom diagram

The original Hom diagram is defined for an abstract commutative ring.
This wrapper seals the equal inherited ring structures while the label
functor and coefficient category are still abstract. It changes no
objects, scalar actions, incidence maps or coefficient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe v

variable {C : Type} [Category.{0} C]
  {A : Type v} [Category.{0} A] [Preadditive A] [Linear ℂ A]
  (P : Cᵒᵖ ⥤ A)

/-- The complete intrinsic Hom functor in the concrete `ModuleCat ℂ`
presentation, before substituting any geometric label. -/
def complexHomDiagram : A ⥤ C ⥤ ModuleCat ℂ := homDiagram ℂ P

theorem complexHomDiagram_eq : complexHomDiagram P = homDiagram ℂ P := rfl

def complexHomDiagramIso : complexHomDiagram P ≅ homDiagram ℂ P := Iso.refl _

instance complexHomDiagram_additive : (complexHomDiagram P).Additive :=
  homDiagram_additive ℂ P

instance complexHomDiagram_linear : (complexHomDiagram P).Linear ℂ :=
  homDiagram_linear ℂ P

end ToricPower.Cellular
end
