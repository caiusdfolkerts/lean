module

public import ToricPower.DiscreteComponentDetection
public import ToricPower.ExactDerivedFunctorIso
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Detecting a map on one whole component of a product category

Currying identifies a diagram on `Discrete I × C` with a discrete
family of full `C`-diagrams. The comparison below keeps the actual
restriction functors and lifts a nonzero map in any one component to
the complete repeated target diagram, also after derived localization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace ToricPower.ProductComponent

variable {I C : Type} [SmallCategory C] (k : Type) [Field k]

def embedding (i : I) : C ⥤ Discrete I × C where
  obj c := (Discrete.mk i,c)
  map f := (𝟙 _,f)

def restriction (i : I) : (Discrete I × C ⥤ ModuleCat.{0} k) ⥤ (C ⥤ ModuleCat.{0} k) :=
  (whiskeringLeft C (Discrete I × C) (ModuleCat.{0} k)).obj (embedding i)

def repetition : (C ⥤ ModuleCat.{0} k) ⥤ (Discrete I × C ⥤ ModuleCat.{0} k) :=
  (whiskeringLeft (Discrete I × C) C (ModuleCat.{0} k)).obj (CategoryTheory.Prod.snd (Discrete I) C)

local notation "Diag" => C ⥤ ModuleCat k

local instance curry_equivalence :
    (curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).IsEquivalence :=
  (currying (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).isEquivalence_inverse

local instance curry_additive :
    (curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).Additive where
  map_add := rfl

local instance uncurry_additive :
    (uncurry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).Additive where
  map_add := rfl

local instance currying_symm_additive :
    (currying (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).symm.functor.Additive := by
  change (curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).Additive
  infer_instance

local instance currying_additive :
    (currying (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).functor.Additive := by
  change (uncurry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).Additive
  infer_instance

local instance constant_additive : (Functor.const (Discrete I) (C := Diag)).Additive where
  map_add := rfl

instance restriction_additive (i : I) : (restriction (C := C) k i).Additive := by
  unfold restriction
  infer_instance

instance restriction_limits (i : I) : PreservesFiniteLimits (restriction (C := C) k i) := by
  unfold restriction
  infer_instance

instance restriction_colimits (i : I) : PreservesFiniteColimits (restriction (C := C) k i) := by
  unfold restriction
  infer_instance

instance repetition_additive : (repetition (I := I) (C := C) k).Additive := by
  unfold repetition
  infer_instance

instance repetition_limits : PreservesFiniteLimits (repetition (I := I) (C := C) k) := by
  unfold repetition
  infer_instance

instance repetition_colimits : PreservesFiniteColimits (repetition (I := I) (C := C) k) := by
  unfold repetition
  infer_instance

/-- Evaluation after currying is literal restriction to a whole component. -/
def curryEvaluationIso (i : I) :
    curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k) ⋙
        (evaluation (Discrete I) Diag).obj (Discrete.mk i) ≅ restriction k i :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl)

/-- Repeating a diagram retains it identically in every discrete component. -/
def curryRepetitionIso :
    repetition (I := I) (C := C) k ⋙ curry ≅ Functor.const (Discrete I) :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun _ => Iso.refl F) (by
    intros
    apply NatTrans.ext
    funext c
    change F.map (𝟙 c) ≫ 𝟙 (F.obj c) = 𝟙 (F.obj c)
    simp)) (by
      intro F G f
      apply NatTrans.ext
      funext i
      apply NatTrans.ext
      funext c
      change f.app c ≫ 𝟙 _ = 𝟙 _ ≫ f.app c
      simp)

local instance : HasDerivedCategory.{1} Diag := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Discrete I ⥤ Diag) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (Discrete I × C ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

def derivedCurryEvaluationIso (i : I) :
    (curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).mapDerivedCategory ⋙
        ((evaluation (Discrete I) Diag).obj (Discrete.mk i)).mapDerivedCategory ≅
      (restriction k i).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ exactDerivedFunctorIso (curryEvaluationIso k i)

def derivedCurryRepetitionIso :
    (repetition (I := I) (C := C) k).mapDerivedCategory ⋙
        (curry (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).mapDerivedCategory ≅
      (Functor.const (Discrete I) (C := Diag)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫ exactDerivedFunctorIso (curryRepetitionIso k)

/-- A nonzero map on one full component induces a nonzero map into
the actual repeated target, with every other component still present. -/
theorem exists_nonzero_into_repetition (i : I)
    (E : DerivedCategory (Discrete I × C ⥤ ModuleCat.{0} k)) (K : DerivedCategory Diag)
    (f : (restriction k i).mapDerivedCategory.obj E ⟶ K) (nonzero : f ≠ 0) :
    ∃ g : E ⟶ (repetition (I := I) k).mapDerivedCategory.obj K, g ≠ 0 := by
  let equivalence := (currying (C := Discrete I) (D := C) (E := ModuleCat.{0} k)).symm.mapDerivedCategory
  let e : ((evaluation (Discrete I) Diag).obj (Discrete.mk i)).mapDerivedCategory.obj
      (equivalence.functor.obj E) ≅ (restriction k i).mapDerivedCategory.obj E :=
    (derivedCurryEvaluationIso k i).app E
  have fNonzero : e.hom ≫ f ≠ 0 := by
    intro h
    apply nonzero
    rw [← cancel_epi e.hom,comp_zero]
    exact h
  obtain ⟨g,hg⟩ := DiscreteComponent.exists_nonzero_into_constant i
    (equivalence.functor.obj E) K (e.hom ≫ f) fNonzero
  let q := (derivedCurryRepetitionIso (I := I) k).app K
  let a := equivalence.fullyFaithfulFunctor.preimage (g ≫ q.inv)
  refine ⟨a,?_⟩
  intro zero
  have mapped := congrArg equivalence.functor.map zero
  rw [equivalence.fullyFaithfulFunctor.map_preimage,Functor.map_zero] at mapped
  apply hg
  rw [← cancel_mono q.inv,zero_comp]
  exact mapped

end ToricPower.ProductComponent

end
