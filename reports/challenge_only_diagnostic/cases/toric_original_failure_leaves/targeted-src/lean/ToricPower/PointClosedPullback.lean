module

public import ToricPower.CellularPointExact
public import ToricPower.CellularClosedSections
public import ToricPower.ElementPullbackBaseChange

/-!
# Pulling the actual point model back to a closed slice

The incoming-incidence predicate of a point coinduced diagram can be
identified with any specified downward-closed support. The resulting
isomorphism is natural both in the coefficient module and in all face
incidences. It identifies the complete coefficient functors, so arbitrary
complexes may subsequently be substituted.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

variable (R : Type) [Ring R] {Source Target : Type}
  [Preorder Source] [Preorder Target]
  (support : Source → Prop) (downward : Antitone support)

local instance constant_additive :
    (Functor.const {d : Source // support d} (C := ModuleCat.{0} R)).Additive where
  map_add := rfl

/-- The literal constant coefficient on the specified closed subposet,
extended by zero to the whole original source category. -/
def closedConstantFunctor : ModuleCat.{0} R ⥤ Source ⥤ ModuleCat.{0} R :=
  Functor.const {d : Source // support d} ⋙ closedFaceExtensionFunctor R support downward

instance closedConstantFunctor_additive :
    (closedConstantFunctor R support downward).Additive := by
  unfold closedConstantFunctor
  infer_instance

instance closedConstantFunctor_limits :
    PreservesFiniteLimits (closedConstantFunctor R support downward) := by
  unfold closedConstantFunctor
  infer_instance

instance closedConstantFunctor_colimits :
    PreservesFiniteColimits (closedConstantFunctor R support downward) := by
  unfold closedConstantFunctor
  infer_instance

/-- Restriction retains precisely the same closed predicate and the
same literal restriction maps on coefficients. -/
def closedConstantRestrictionIso {Sub : Type} [Preorder Sub] (f : Sub ⥤ Source) :
    closedConstantFunctor R support downward ⋙
        ElementPushdown.baseRestriction f (D := ModuleCat.{0} R) ≅
      closedConstantFunctor R (fun d => support (f.obj d))
        (fun _ _ h => downward (f.map (homOfLE h)).le) :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; rfl)) (by intros; rfl)

variable (branch : Source ⥤ Target) (point : Target)
  (condition : ∀ d : Source, branch.obj d ≤ point ↔ support d)

/-- All incoming incidences are reindexed by the actual closed-support
predicate; no stalk or boundary face is omitted. -/
def pointPullbackClosedIso :
    pointCoinducedFunctor R point ⋙
        ElementPushdown.baseRestriction branch (D := ModuleCat.{0} R) ≅
      closedConstantFunctor R support downward :=
  NatIso.ofComponents (fun M => NatIso.ofComponents (fun d =>
    ({ toFun := fun x h => x (homOfLE ((condition d).mpr h.down))
       invFun := fun x f => x ⟨(condition d).mp f.le⟩
       left_inv := by
         intro x
         funext f
         exact congrArg x (Subsingleton.elim _ _)
       right_inv := by intro x; rfl
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } :
      ((branch.obj d ⟶ point) → M) ≃ₗ[R] (PLift (support d) → M)).toModuleIso)
      (by
        intro d e f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext h
        change x (branch.map f ≫ homOfLE ((condition e).mpr h.down)) =
          x (homOfLE ((condition d).mpr (downward f.le h.down)))
        exact congrArg x (Subsingleton.elim _ _))) (by
          intro M N f
          apply NatTrans.ext
          funext d
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          funext h
          rfl)

end ToricPower.Cellular

end
