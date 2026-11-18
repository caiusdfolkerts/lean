module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Module.LinearMap.Basic

/-! An additive functor carries actual endomorphism-ring actions to actions
on its abelian-group values. This small generic construction keeps the
scheme cohomology action independent of the implementation of `Ext`. -/

@[expose] public section

open CategoryTheory

namespace ToricPower

universe u v w

/-- The endomorphism action carried by an additive abelian-group-valued functor. -/
def additiveFunctorEndAction {C : Type u} [Category.{v} C] [Preadditive C]
    (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (M : C) :
    End M →+* AddMonoid.End (F.obj M) where
  toFun e := (F.map e.asHom).hom
  map_one' := by
    ext x
    exact F.map_id_apply M x
  map_mul' a b := by
    ext x
    exact F.map_comp_apply b.asHom a.asHom x
  map_zero' := by
    ext x
    change F.map (0 : M ⟶ M) x = 0
    rw [F.map_zero]
    rfl
  map_add' a b := by
    ext x
    change F.map (a.asHom + b.asHom) x = F.map a.asHom x + F.map b.asHom x
    rw [F.map_add]
    rfl

/-- A functorial map is linear whenever its two scalar actions are induced
by commuting endomorphisms of the source category. -/
def additiveFunctorMapLinear {C : Type u} [Category.{v} C]
    {R : Type*} [Semiring R] (F : C ⥤ AddCommGrpCat.{w}) {M N : C}
    [Module R (F.obj M)] [Module R (F.obj N)] (f : M ⟶ N)
    (sourceAction : R → (M ⟶ M)) (targetAction : R → (N ⟶ N))
    (sourceScalar : ∀ r x, r • x = F.map (sourceAction r) x)
    (targetScalar : ∀ r x, r • x = F.map (targetAction r) x)
    (naturality : ∀ r, sourceAction r ≫ f = f ≫ targetAction r) :
    F.obj M →ₗ[R] F.obj N where
  toFun := F.map f
  map_add' := map_add _
  map_smul' r x := by
    rw [sourceScalar, targetScalar]
    rw [← F.map_comp_apply, ← F.map_comp_apply, naturality]
    rfl

/-- Functoriality preserves a commuting endomorphism square pointwise. -/
theorem additiveFunctorMap_commutes {C : Type u} [Category.{v} C]
    (F : C ⥤ AddCommGrpCat.{w}) {M N : C} (f : M ⟶ N)
    (a : M ⟶ M) (b : N ⟶ N) (commutes : a ≫ f = f ≫ b) (x : F.obj M) :
    (F.map f).hom ((F.map a).hom x) = (F.map b).hom ((F.map f).hom x) := by
  have equality := congrArg (fun mapping => F.map mapping x) commutes
  simpa only [F.map_comp_apply] using equality

/-- An additive map commuting with specified scalar actions is linear. -/
def linearMapOfAddHomScalar {R A B : Type*} [Semiring R]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    (f : A →+ B) (sourceAction : R → AddMonoid.End A) (targetAction : R → AddMonoid.End B)
    (sourceScalar : ∀ r x, r • x = sourceAction r x)
    (targetScalar : ∀ r x, r • x = targetAction r x)
    (commutes : ∀ r x, f (sourceAction r x) = targetAction r (f x)) : A →ₗ[R] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (r • x) = r • f x
    rw [sourceScalar, targetScalar, commutes]

end ToricPower
