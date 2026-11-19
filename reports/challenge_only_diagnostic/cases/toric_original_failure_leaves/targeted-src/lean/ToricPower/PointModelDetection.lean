module

public import ToricPower.PointClosedPullback
public import ToricPower.ScalarRetractDetection
public import ToricPower.CellularLocalMorseVanishing

/-!
# The actual local point model transfers a nonzero closed-slice test

The source may have arbitrary unbounded, infinite-dimensional stalks.
Its genuine evaluation unit gives the point model, the specified branch
pulls that model back to the actual closed slice, and a shifted scalar
retract transfers the original nonzero scalar test to this source.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

variable (k : Type) [Field k] {Source Target : Type}
  [Preorder Source] [Preorder Target]
  (support : Source → Prop) (downward : Antitone support)
  (branch : Source ⥤ Target) (point : Target)
  (condition : ∀ d : Source, branch.obj d ≤ point ↔ support d)

local instance pointModelDerivedScalars : HasDerivedCategory.{1} (ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance pointModelDerivedSource : HasDerivedCategory.{1} (Source ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance pointModelDerivedTarget : HasDerivedCategory.{1} (Target ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

variable
  (incoming : ∀ d : Target, d ≠ point → IsEmpty (d ⟶ point))
  (K : CochainComplex (Target ⥤ ModuleCat.{0} k) ℤ)
  (vanishes : ∀ d : Target, d ≠ point →
    ((((evaluation Target (ModuleCat.{0} k)).obj d).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)

/-- The exact pullback of the original unit is the prescribed closed
coefficient functor on the original unbounded stalk complex. -/
def pointPullbackDerivedModelIso :
    (ElementPushdown.baseRestriction branch (D := ModuleCat.{0} k)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ≅
      (closedConstantFunctor k support downward).mapDerivedCategory.obj
        (((evaluation Target (ModuleCat.{0} k)).obj point).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) :=
  (ElementPushdown.baseRestriction branch (D := ModuleCat.{0} k)).mapDerivedCategory.mapIso
      (pointSupportedDerivedIso k point incoming K vanishes) ≪≫
    (Functor.mapDerivedCategoryCompIso (pointCoinducedFunctor k point)
      (ElementPushdown.baseRestriction branch (D := ModuleCat.{0} k))).app
        (((evaluation Target (ModuleCat.{0} k)).obj point).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) ≪≫
    (exactDerivedFunctorIso (pointPullbackClosedIso k support downward branch point condition)).app
      (((evaluation Target (ModuleCat.{0} k)).obj point).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K))

include condition incoming vanishes in
/-- A nonzero scalar test gives a nonzero shifted map from the actual
branch pullback of the whole original source. -/
theorem exists_nonzero_from_point_pullback
    (nonzero : ¬ (K.asFunctor.obj point).Acyclic)
    (T : DerivedCategory (Source ⥤ ModuleCat.{0} k))
    (test : (closedConstantFunctor k support downward).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶ T)
    (testNonzero : test ≠ 0) :
    ∃ q : ℤ, ∃ f :
      (ElementPushdown.baseRestriction branch (D := ModuleCat.{0} k)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) ⟶ T⟦q⟧, f ≠ 0 := by
  let E := ((evaluation Target (ModuleCat.{0} k)).obj point).mapDerivedCategory.obj
    (DerivedCategory.Q.obj K)
  have nonzeroE : ¬ IsZero E := by
    intro zero
    apply nonzero
    apply acyclic_of_derivedComplex_isZero
    exact (((evaluation Target (ModuleCat.{0} k)).obj point).mapDerivedCategoryFactors.app K).isZero_iff.mp zero
  obtain ⟨q,f,hf⟩ := exists_nonzero_from_coefficient k
    (closedConstantFunctor k support downward).mapDerivedCategory T test testNonzero E nonzeroE
  let model := pointPullbackDerivedModelIso k support downward branch point condition
    incoming K vanishes
  refine ⟨q,model.hom ≫ f,?_⟩
  intro zero
  apply hf
  rw [← cancel_epi model.hom,comp_zero]
  exact zero

end ToricPower.Cellular

end
