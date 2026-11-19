module

public import ToricPower.CellularPointSerre
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The abelian parent presentation of inverse Nakayama

The pointwise additive structure and the parent of the abelian structure
on module-valued diagrams are the same. Recording that equality before
applying a concrete coefficient functor avoids reducing the entire
functor merely to compare two presentations of its additive instance.
No functor or mathematical hypothesis is changed.
-/

@[expose] public noncomputable section

open CategoryTheory
namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

theorem diagramPreadditivePresentation :
    (Abelian.toPreadditive : Preadditive (C ⥤ ModuleCat.{u} k)) =
      (functorCategoryPreadditive (C := C) (D := ModuleCat.{u} k)) := rfl

attribute [local instance 2000] Abelian.toPreadditive

/-- The genuine additive instance, with the literal parent used by the
generic abelian homotopy and localization interfaces. -/
instance (priority := 1100) inverseNakayamaAbelian_additive :
    (inverseNakayama k (C := C)).Additive := by
  rw [diagramPreadditivePresentation k]
  exact inverseNakayama_additive k

end ToricPower.Cellular
end
