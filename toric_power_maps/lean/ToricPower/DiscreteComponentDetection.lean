module

public import ToricPower.ExactDerivedAdjunction
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Detecting a map in one component of a discrete family

The right adjoint to evaluation at one component is a direct summand of
the constant family. Its inclusion is the projection at that component
and zero elsewhere. The explicit retraction persists in the unbounded
derived category, so a nonzero map in one component supplies a nonzero
map into the complete constant family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.DiscreteComponent

universe u v
variable {I : Type} {D : Type u} [Category.{v} D] [HasProducts.{0} D]
  [Abelian D] (i : I)

local notation "j₀" => Discrete.mk i

/-- The whole product at the selected component is canonically the original object. -/
def evaluationIso :
    evaluationRightAdjoint D j₀ ⋙ (evaluation (Discrete I) D).obj j₀ ≅ 𝟭 D :=
  NatIso.ofComponents (fun X =>
    { hom := Pi.π (fun _ : j₀ ⟶ j₀ => X) (𝟙 j₀)
      inv := Pi.lift (fun _ : j₀ ⟶ j₀ => 𝟙 X)
      hom_inv_id := by
        apply Pi.hom_ext
        intro f
        have hf : f = 𝟙 j₀ := Subsingleton.elim _ _
        subst f
        simp only [Category.assoc,Pi.lift_comp_π,Category.comp_id,Category.id_comp]
        exact Category.comp_id _
      inv_hom_id := Pi.lift_comp_π _ _ }) (by
    intro X Y f
    exact Pi.lift_comp_π _ _)

theorem evaluationAway_isZero (j : Discrete I) (different : j.as ≠ i) (X : D) :
    IsZero (((evaluationRightAdjoint D j₀).obj X).obj j) := by
  rw [IsZero.iff_id_eq_zero]
  apply Pi.hom_ext
  intro f
  exact (different (Discrete.eq_of_hom f)).elim

/-- The specified component is included by its actual projection; all
other components receive the actual zero map. -/
def inclusion : evaluationRightAdjoint D j₀ ⟶ Functor.const (Discrete I) where
  app X := Discrete.natTrans (fun j => by
    classical
    exact if h : j.as = i then Pi.π (fun _ : j ⟶ j₀ => X) (Discrete.eqToHom h) else 0)
  naturality {X Y} f := by
    classical
    apply NatTrans.ext
    funext j
    by_cases h : j.as = i
    · change (Pi.lift (fun g : j ⟶ j₀ => Pi.π (fun _ => X) g ≫ f)) ≫
          (if h : j.as = i then Pi.π (fun _ : j ⟶ j₀ => Y) (Discrete.eqToHom h) else 0) =
        (if h : j.as = i then Pi.π (fun _ : j ⟶ j₀ => X) (Discrete.eqToHom h) else 0) ≫ f
      simp only [dite_eq_left h,Pi.lift_comp_π]
    · change _ ≫ (if h : j.as = i then _ else 0) =
        (if h : j.as = i then _ else 0) ≫ f
      simp only [dite_eq_right h,comp_zero,zero_comp]

def projection : Functor.const (Discrete I) ⟶ evaluationRightAdjoint D j₀ where
  app X := Discrete.natTrans (fun j => Pi.lift (fun _ : j ⟶ j₀ => 𝟙 X))
  naturality {X Y} f := by
    apply NatTrans.ext
    funext j
    apply Pi.hom_ext
    intro g
    change (f ≫ Pi.lift (fun _ : j ⟶ j₀ => 𝟙 Y)) ≫ Pi.π (fun _ => Y) g =
      (Pi.lift (fun _ : j ⟶ j₀ => 𝟙 X) ≫
        Pi.lift (fun h : j ⟶ j₀ => Pi.π (fun _ => X) h ≫ f)) ≫ Pi.π (fun _ => Y) g
    simp only [Category.assoc,Pi.lift_comp_π,Pi.lift_comp_π_assoc,
      Category.id_comp,Category.comp_id]

/-- This is the literal splitting, before any localization. -/
theorem inclusion_projection : inclusion (D := D) i ≫ projection i = 𝟙 _ := by
  classical
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext j
  apply Pi.hom_ext
  intro f
  have h : j.as = i := Discrete.eq_of_hom f
  change ((if h : j.as = i then Pi.π (fun _ : j ⟶ j₀ => X)
      (Discrete.eqToHom h) else 0) ≫ Pi.lift (fun _ : j ⟶ j₀ => 𝟙 X)) ≫
        Pi.π (fun _ => X) f = 𝟙 _ ≫ Pi.π (fun _ => X) f
  simp only [dite_eq_left h,Category.assoc,Pi.lift_comp_π,Category.comp_id,Category.id_comp]
  congr 1
  exact Subsingleton.elim _ _


instance rightAdjoint_limits : PreservesFiniteLimits (evaluationRightAdjoint D j₀) := by
  letI := (evaluationAdjunctionLeft D j₀).isRightAdjoint
  infer_instance

instance rightAdjoint_colimits : PreservesFiniteColimits (evaluationRightAdjoint D j₀) := by
  classical
  apply preservesFiniteColimits_of_evaluation
  intro j
  by_cases h : j.as = i
  · have hj : j = j₀ := Discrete.ext h
    subst j
    exact preservesFiniteColimits_of_natIso (evaluationIso (D := D) i).symm
  · let F := evaluationRightAdjoint D j₀ ⋙ (evaluation (Discrete I) D).obj j
    have zeroF : IsZero F := F.isZero (fun X => evaluationAway_isZero i j h X)
    letI := F.preservesColimitsOfSize_of_isZero.{0,0} zeroF
    infer_instance

instance rightAdjoint_additive : (evaluationRightAdjoint D j₀).Additive :=
  (evaluationRightAdjoint D j₀).additive_of_preserves_binary_products

local instance constant_additive : (Functor.const (Discrete I) (C := D)).Additive where
  map_add := rfl

variable [HasDerivedCategory D] [HasDerivedCategory (Discrete I ⥤ D)]

/-- Evaluation and extension on the entire unbounded derived categories. -/
def derivedAdjunction :
    ((evaluation (Discrete I) D).obj j₀).mapDerivedCategory ⊣
      (evaluationRightAdjoint D j₀).mapDerivedCategory :=
  exactDerivedAdjunction (evaluationAdjunctionLeft D j₀)

theorem derived_inclusion_projection :
    (inclusion (D := D) i).mapDerivedCategory ≫ (projection i).mapDerivedCategory = 𝟙 _ := by
  rw [← NatTrans.mapDerivedCategory_comp,inclusion_projection,NatTrans.mapDerivedCategory_id]

/-- A nonzero component map remains nonzero in the complete family. -/
theorem exists_nonzero_into_constant
    (E : DerivedCategory (Discrete I ⥤ D)) (K : DerivedCategory D)
    (f : ((evaluation (Discrete I) D).obj j₀).mapDerivedCategory.obj E ⟶ K)
    (nonzero : f ≠ 0) :
    ∃ g : E ⟶ (Functor.const (Discrete I) (C := D)).mapDerivedCategory.obj K, g ≠ 0 := by
  let a := (derivedAdjunction (D := D) i).homEquiv E K f
  refine ⟨a ≫ (inclusion i).mapDerivedCategory.app K,?_⟩
  intro zero
  have ha : a = 0 := by
    have h := congrArg (fun g => g ≫ (projection i).mapDerivedCategory.app K) zero
    rw [Category.assoc,← NatTrans.comp_app,derived_inclusion_projection,
      NatTrans.id_app,Category.comp_id,zero_comp] at h
    exact h
  apply nonzero
  apply ((derivedAdjunction (D := D) i).homEquiv E K).injective
  exact ha.trans ((derivedAdjunction (D := D) i).homAddEquiv_zero E K).symm

end ToricPower.DiscreteComponent

end
