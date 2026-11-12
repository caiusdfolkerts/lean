module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-! # The canonical scalar section of the constant face diagram -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace ToricPower.Cellular

universe u
variable (k : Type u) [CommRing k] (C : Type u) [Category.{u} C]

abbrev constantDiagram : C ⥤ ModuleCat.{u} k :=
  (Functor.const C).obj (ModuleCat.of k k)

abbrev constantSections : (C ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k :=
  (linearCoyoneda k (C ⥤ ModuleCat.{u} k)).obj (op (constantDiagram k C))

def constantScalarMap : ModuleCat.of k k ⟶ (constantSections k C).obj (constantDiagram k C) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton k
    (constantDiagram k C ⟶ constantDiagram k C) (𝟙 _))

end ToricPower.Cellular

end
