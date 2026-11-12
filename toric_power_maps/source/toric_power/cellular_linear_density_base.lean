module

public import ToricPower.CellularRealization
public import ToricPower.CellularVectorCover
public import ToricPower.CovariantRepresentableSource
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Actual linear density of cellular representables

The free-module Yoneda equivalence is linear and natural in both
variables. Consequently the original coend of all representables is
canonically the original diagram, with a specified formula on every
vector generator. No finite-dimensional assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

theorem evaluate_representablePrecompose
    (F : C ⥤ ModuleCat.{u} k) {c d : C} (f : c ⟶ d)
    (φ : representable k c ⟶ F) :
    evaluate k F d (representablePrecompose k f ≫ φ) =
      F.map f (evaluate k F c φ) := by
  change φ.app d ((representablePrecompose k f).app d (ModuleCat.freeMk (𝟙 d))) = _
  rw [representablePrecompose_freeMk,Category.comp_id]
  have h := ConcreteCategory.congr_hom (φ.naturality f) (ModuleCat.freeMk (𝟙 c))
  simp only [ModuleCat.comp_apply,representable_map_freeMk,Category.id_comp] at h
  exact h

/-- All original Hom diagrams of free representables recover the
original diagram functor, including all its arrows. -/
def homRepresentablesIso : homDiagram k (representableFunctor k (C := C)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F =>
    NatIso.ofComponents (fun c => (representableHomLinearEquiv k F c).toModuleIso) (by
      intro c d f
      ext φ
      exact evaluate_representablePrecompose k F f φ)) (by
    intro F G f
    ext c φ
    exact evaluate_comp k c φ f)

/-- The actual coend of the full linear representable diagram is the
identity, by the proved ordinary coend--Hom adjunction. -/
def representableDensityIso : realization k (representableFunctor k (C := C)) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq
    ((realizationHomAdjunction k (representableFunctor k)).ofNatIsoRight
      (homRepresentablesIso k)) Adjunction.id

/-- The canonical density map sends the literal cell/vector generator
to its original Yoneda map. This specifies the comparison independently
of the uniqueness-of-adjoint presentation used to construct it. -/
theorem representableDensityIso_generator
    (F : C ⥤ ModuleCat.{u} k) (c : C) (x : F.obj c) :
    realizationInclusion k (representableFunctor k) F c x ≫
        (representableDensityIso k).hom.app F = fromValue k F c x := by
  apply (representableHomEquiv k F c).injective
  change evaluate k F c (realizationInclusion k (representableFunctor k) F c x ≫
      (representableDensityIso k).hom.app F) = evaluate k F c (fromValue k F c x)
  rw [evaluate_fromValue]
  have equality := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((realizationHomAdjunction k (representableFunctor k)).ofNatIsoRight
      (homRepresentablesIso k)) Adjunction.id F
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at equality
  exact ConcreteCategory.congr_hom (congrArg (fun η => η.app c) equality) x

end ToricPower.Cellular

end
