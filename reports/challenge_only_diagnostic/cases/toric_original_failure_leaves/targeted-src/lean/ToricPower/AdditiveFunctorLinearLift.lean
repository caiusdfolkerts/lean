module

public import ToricPower.AdditiveEndAction
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The canonical scalar lift of an additive functor

An additive functor from an `R`-linear category to abelian groups has a
canonical `R`-module action: `r` acts by the image of `r • 𝟙`. Every
natural transformation commutes with this action. The construction below
therefore lifts actual natural isomorphisms to module-valued natural
isomorphisms. A comparison with an existing linear functor proves that
this lift uses its existing scalar structure, not an arbitrary transported
one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ToricPower

universe r u v w
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The action on an additive functor value induced by the actual scalar
endomorphisms in its source category. -/
@[instance_reducible]
def additiveLinearModule (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (X : C) :
    Module R (F.obj X) :=
  Module.compHom (F.obj X)
    ((additiveFunctorEndAction F X).comp (algebraMap R (End X)))

/-- The canonical lifted scalar action has its specified functorial
meaning. -/
theorem additiveLinearModule_smul (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    (X : C) (r : R) (x : F.obj X) :
    letI := additiveLinearModule R F X
    r • x = F.map (r • 𝟙 X) x := by
  change F.map ((algebraMap R (End X) r).asHom) x = _
  rw [Algebra.algebraMap_eq_smul_one, End.smul_asHom]
  rfl

/-- The same abelian group with its canonical source-induced scalars. -/
def additiveLinearLiftObj (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (X : C) :
    ModuleCat.{w} R :=
  letI := additiveLinearModule R F X
  ModuleCat.of R (F.obj X)

/-- Every actual coefficient map commutes with the canonical scalars. -/
def additiveLinearLiftMap (F : C ⥤ AddCommGrpCat.{w}) [F.Additive]
    {X Y : C} (f : X ⟶ Y) :
    additiveLinearLiftObj R F X ⟶ additiveLinearLiftObj R F Y := by
  letI := additiveLinearModule R F X
  letI := additiveLinearModule R F Y
  exact ModuleCat.ofHom
    { toFun := F.map f
      map_add' := map_add _
      map_smul' := by
        intro r x
        change F.map f (_ • x) = _ • F.map f x
        rw [additiveLinearModule_smul, additiveLinearModule_smul,
          ← F.map_comp_apply, ← F.map_comp_apply]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id, RingHom.id_apply] }

/-- The canonical module-valued lift retains all actual maps of the
original additive functor. -/
def additiveLinearLift (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    C ⥤ ModuleCat.{w} R where
  obj := additiveLinearLiftObj R F
  map := additiveLinearLiftMap R F
  map_id X := by
    ext x
    exact F.map_id_apply X x
  map_comp f g := by
    ext x
    exact F.map_comp_apply f g x

instance additiveLinearLift_additive (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (additiveLinearLift R F).Additive where
  map_add {X Y} {f g} := by
    ext x
    exact ConcreteCategory.congr_hom (F.map_add (f := f) (g := g)) x

instance additiveLinearLift_linear (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] :
    (additiveLinearLift R F).Linear R where
  map_smul {X Y} f r := by
    ext x
    letI := additiveLinearModule R F Y
    change F.map (r • f) x = r • F.map f x
    rw [additiveLinearModule_smul]
    exact (congrArg (fun g => F.map g (x : F.obj X))
      (by simp only [Linear.comp_smul, Category.comp_id] : r • f = f ≫ (r • 𝟙 Y))).trans
        (F.map_comp_apply f (r • 𝟙 Y) x)

/-- Naturality at actual scalar endomorphisms proves linearity of every
component, in every degree or diagram position. -/
def additiveLinearLiftNatTrans {F G : C ⥤ AddCommGrpCat.{w}}
    [F.Additive] [G.Additive] (α : F ⟶ G) :
    additiveLinearLift R F ⟶ additiveLinearLift R G where
  app X := by
    letI := additiveLinearModule R F X
    letI := additiveLinearModule R G X
    exact ModuleCat.ofHom
      { toFun := α.app X
        map_add' := map_add _
        map_smul' := by
          intro r x
          change α.app X (r • x) = r • α.app X x
          rw [additiveLinearModule_smul, additiveLinearModule_smul]
          exact ConcreteCategory.congr_hom (α.naturality (r • 𝟙 X)) x }
  naturality {X Y} f := by
    ext x
    exact ConcreteCategory.congr_hom (α.naturality f) x

/-- An actual additive natural isomorphism lifts to the canonical
module structures without additional choices. -/
def additiveLinearLiftNatIso {F G : C ⥤ AddCommGrpCat.{w}}
    [F.Additive] [G.Additive] (e : F ≅ G) :
    additiveLinearLift R F ≅ additiveLinearLift R G where
  hom := additiveLinearLiftNatTrans R e.hom
  inv := additiveLinearLiftNatTrans R e.inv
  hom_inv_id := by
    ext X x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id X) x
  inv_hom_id := by
    ext X x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id X) x

/-- Forgetting a genuinely linear functor and taking the canonical lift
recovers its existing module structures and all its maps. -/
def additiveLinearLiftForgetIso (F : C ⥤ ModuleCat.{w} R) [F.Additive] [F.Linear R] :
    additiveLinearLift R (F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ≅ F :=
  NatIso.ofComponents (fun X => by
    let e : additiveLinearLiftObj R
        (F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) X ≃ₗ[R] F.obj X :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r x
          have h := additiveLinearModule_smul R
            (F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) X r (x : F.obj X)
          have scalarMap : F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
            rw [F.map_smul, F.map_id]
          exact h.trans (ConcreteCategory.congr_hom scalarMap x) }
    exact e.toModuleIso) (by
    intro X Y f
    ext x
    rfl)

end ToricPower
