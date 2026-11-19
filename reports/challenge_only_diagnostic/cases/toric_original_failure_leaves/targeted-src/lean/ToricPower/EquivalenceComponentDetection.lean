module

public import ToricPower.ProductComponentDetection
public import ToricPower.ElementPullbackBaseChange

/-!
# Component detection through the actual covering equivalence

The source category may be presented by a category of elements rather
than a literal product. An explicit equivalence to all discrete
components, together with the specified projection comparison, transports
the whole-component detection theorem without deleting other sheets.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ComponentEquivalence

variable {I C X : Type} [SmallCategory C] [SmallCategory X]
  (k : Type) [Field k] (e : X ≌ Discrete I × C) (P : X ⥤ C)

set_option quotPrecheck false in
local notation "Modk" => ModuleCat.{0} k
set_option quotPrecheck false in
local notation "F" => (e.congrLeft (E := Modk)).functor
local notation "pull" => ElementPushdown.baseRestriction P (D := Modk)

local instance congrLeft_additive : (F).Additive := by
  change ((whiskeringLeft (Discrete I × C) X Modk).obj e.inverse).Additive
  infer_instance

def component (i : I) : C ⥤ X := ProductComponent.embedding i ⋙ e.inverse

def restriction (i : I) : (X ⥤ Modk) ⥤ (C ⥤ Modk) :=
  ElementPushdown.baseRestriction (component e i)

instance restriction_additive (i : I) : (restriction k e i).Additive := by
  unfold restriction
  infer_instance

instance restriction_limits (i : I) : PreservesFiniteLimits (restriction k e i) := by
  unfold restriction
  infer_instance

instance restriction_colimits (i : I) : PreservesFiniteColimits (restriction k e i) := by
  unfold restriction
  infer_instance

def restrictionIso (i : I) :
    F ⋙ ProductComponent.restriction k i ≅ restriction k e i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl)

def repetitionIso
    (projection : e.inverse ⋙ P ≅ CategoryTheory.Prod.snd (Discrete I) C) :
    pull ⋙ F ≅ ProductComponent.repetition k :=
  NatIso.ofComponents (fun K => Functor.isoWhiskerRight projection K) (by
    intro K M f
    apply NatTrans.ext
    funext c
    exact (f.naturality (projection.hom.app c)).symm)

local instance : HasDerivedCategory.{1} (X ⥤ Modk) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (C ⥤ Modk) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Discrete I × C ⥤ Modk) := HasDerivedCategory.standard _

def derivedRestrictionIso (i : I) :
    (F).mapDerivedCategory ⋙ (ProductComponent.restriction k i).mapDerivedCategory ≅
      (restriction k e i).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ exactDerivedFunctorIso (restrictionIso k e i)

def derivedRepetitionIso
    (projection : e.inverse ⋙ P ≅ CategoryTheory.Prod.snd (Discrete I) C) :
    (pull).mapDerivedCategory ⋙ (F).mapDerivedCategory ≅
      (ProductComponent.repetition k).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    exactDerivedFunctorIso (repetitionIso k e P projection)

/-- A map from one entire actual covering component survives in the
full target pulled back along the specified projection. -/
theorem exists_nonzero_into_pullback
    (projection : e.inverse ⋙ P ≅ CategoryTheory.Prod.snd (Discrete I) C)
    (i : I) (E : DerivedCategory (X ⥤ Modk)) (K : DerivedCategory (C ⥤ Modk))
    (f : (restriction k e i).mapDerivedCategory.obj E ⟶ K) (nonzero : f ≠ 0) :
    ∃ g : E ⟶ (pull).mapDerivedCategory.obj K, g ≠ 0 := by
  let equivalence := (e.congrLeft (E := Modk)).mapDerivedCategory
  let r : (ProductComponent.restriction k i).mapDerivedCategory.obj
      (equivalence.functor.obj E) ≅ (restriction k e i).mapDerivedCategory.obj E :=
    (derivedRestrictionIso k e i).app E
  have nonzeroComponent : r.hom ≫ f ≠ 0 := by
    intro zero
    apply nonzero
    rw [← cancel_epi r.hom,comp_zero]
    exact zero
  obtain ⟨a,ha⟩ := ProductComponent.exists_nonzero_into_repetition k i
    (equivalence.functor.obj E) K (r.hom ≫ f) nonzeroComponent
  let q := (derivedRepetitionIso k e P projection).app K
  let g := equivalence.fullyFaithfulFunctor.preimage (a ≫ q.inv)
  refine ⟨g,?_⟩
  intro zero
  have mapped := congrArg equivalence.functor.map zero
  rw [equivalence.fullyFaithfulFunctor.map_preimage,Functor.map_zero] at mapped
  apply ha
  rw [← cancel_mono q.inv,zero_comp]
  exact mapped

end ToricPower.ComponentEquivalence

end
