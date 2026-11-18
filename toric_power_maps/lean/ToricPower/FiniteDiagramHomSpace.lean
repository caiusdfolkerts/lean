module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional natural-transformation spaces

Only the object set needs to be finite: the space of natural
transformations injects into the finite product of its component Hom
spaces. There is no restriction on the number of arrows.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C] [Finite C]

theorem finiteDiagramHom_finite_of_finite_objects (F G : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] [∀ c, FiniteDimensional k (G.obj c)] :
    FiniteDimensional k (F ⟶ G) := by
  let components : (F ⟶ G) →ₗ[k] ∀ c, F.obj c →ₗ[k] G.obj c :=
    { toFun := fun f c => (f.app c).hom
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective components
  intro f g h
  apply NatTrans.ext
  funext c
  apply ModuleCat.hom_ext
  exact congrFun h c

end ToricPower.Cellular

end
