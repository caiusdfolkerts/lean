module

public import ToricPower.CellularPointAdjunction
public import ToricPower.ExactDerivedAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Exact point coinduction on the full face category

At each face the original incoming-incidence module is either the
coefficient module or zero. This proves exactness of the actual
coinduction functor and gives its action on the entire unbounded derived
category. The local point model is identified by its original unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u w w'
variable (R : Type u) [Ring R] {B : Type u} [Preorder B] (c : B)

def pointCoinducedEvaluationIso (d : B) (f : d ⟶ c) :
    pointCoinducedFunctor R c ⋙ (evaluation B (ModuleCat.{u} R)).obj d ≅
      𝟭 (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun M =>
    { hom := ModuleCat.ofHom
        { toFun := fun x => x f
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      inv := ModuleCat.ofHom
        { toFun := fun x _ => x
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext g
        exact congrArg x (Subsingleton.elim f g)
      inv_hom_id := rfl }) (by intros; rfl)

instance pointCoinducedFunctor_limits :
    PreservesFiniteLimits (pointCoinducedFunctor R c) := by
  letI := (pointCoinducedAdjunction R c).isRightAdjoint
  infer_instance

instance pointCoinducedFunctor_colimits :
    PreservesFiniteColimits (pointCoinducedFunctor R c) := by
  classical
  apply preservesFiniteColimits_of_evaluation
  intro d
  by_cases h : Nonempty (d ⟶ c)
  · exact preservesFiniteColimits_of_natIso
      (pointCoinducedEvaluationIso R c d h.some).symm
  · letI : IsEmpty (d ⟶ c) := ⟨fun f => h ⟨f⟩⟩
    let F := pointCoinducedFunctor R c ⋙ (evaluation B (ModuleCat.{u} R)).obj d
    have zeroF : IsZero F := F.isZero (fun M => pointCoinduced_isZero R c d M)
    letI := F.preservesColimitsOfSize_of_isZero.{0,0} zeroF
    infer_instance

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} (B ⥤ ModuleCat.{u} R)]

def pointCoinducedDerivedAdjunction :
    ((evaluation B (ModuleCat.{u} R)).obj c).mapDerivedCategory ⊣
      (pointCoinducedFunctor R c).mapDerivedCategory :=
  exactDerivedAdjunction (pointCoinducedAdjunction R c)

/-- The actual local unit supplies the unbounded point model. -/
def pointSupportedDerivedIso
    (incoming : ∀ d : B, d ≠ c → IsEmpty (d ⟶ c))
    (K : CochainComplex (B ⥤ ModuleCat.{u} R) ℤ)
    (vanishes : ∀ d : B, d ≠ c →
      ((((evaluation B (ModuleCat.{u} R)).obj d).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    DerivedCategory.Q.obj K ≅
      (pointCoinducedFunctor R c).mapDerivedCategory.obj
        (((evaluation B (ModuleCat.{u} R)).obj c).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) := by
  letI := pointComplexUnit_quasiIso R (.up ℤ) c incoming K vanishes
  exact asIso (DerivedCategory.Q.map (pointComplexUnit R (.up ℤ) c K)) ≪≫
    ((((evaluation B (ModuleCat.{u} R)).obj c ⋙ pointCoinducedFunctor R c).mapDerivedCategoryFactors).app K).symm ≪≫
    ((Functor.mapDerivedCategoryCompIso ((evaluation B (ModuleCat.{u} R)).obj c)
      (pointCoinducedFunctor R c)).app (DerivedCategory.Q.obj K)).symm

end ToricPower.Cellular

end
