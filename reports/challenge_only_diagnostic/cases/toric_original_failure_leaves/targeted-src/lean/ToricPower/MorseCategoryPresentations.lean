module

public import ToricPower.QuasicoherentCategory
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Equal canonical category structures at the geometric Morse boundary

These are equalities of the inherited structures, recorded before any
large coefficient functor is substituted. No new category or scalar
action is introduced.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

theorem morseQuasicoherentPreadditivePresentation (X : Scheme) :
    (Abelian.toPreadditive : Preadditive (QCoh X)) =
      (inferInstance : Preadditive (QCoh X)) := rfl

theorem morseDiagramPreadditivePresentation (k : Type) [Field k]
    (C : Type) [Category.{0} C] :
    (Abelian.toPreadditive : Preadditive (C ⥤ ModuleCat k)) =
      (functorCategoryPreadditive (C := C) (D := ModuleCat k)) := rfl

theorem morseComplexRingPresentation :
    Complex.instField.toDivisionRing.toRing = Complex.instRing := rfl

theorem morseIntegerRingPresentation :
    Int.instRing = Int.instCommRing.toRing := rfl

theorem morseIntegerAdditivePresentation :
    Int.instAddCommGroup = Int.instCommRing.toRing.toAddCommGroup := rfl

end ToricPower

end
