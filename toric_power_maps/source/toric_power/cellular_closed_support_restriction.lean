module

public import ToricPower.CellularClosedSections
public import ToricPower.ExactDerivedAdjunction

/-!
# Restricting a target to its genuine closed cohomological support

For a downward-closed face subposet, restriction and literal extension
by zero are exact adjoints. The original unit is a quasi-isomorphism
whenever the coefficient complex is acyclic away from that subposet.
This permits local Hom computations without replacing cohomological
support by the generally larger support of the individual cochains.

No boundedness or finiteness assumption is imposed on the complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

universe u

variable (R : Type u) [Ring R] {B : Type u} [Preorder B]
  (P : B → Prop) (downward : Antitone P)

theorem closedFaceUnit_app_isIso (F : B ⥤ ModuleCat.{u} R)
    (b : B) (hb : P b) :
    IsIso (((closedFaceUnit R P downward).app F).app b) := by
  let inverse :
      (closedFaceExtension R P downward ((closedFaceRestriction R P).obj F)).obj b ⟶
        F.obj b :=
    ModuleCat.ofHom
      { toFun := fun x => x ⟨hb⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · rfl
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext h
    rfl

instance closedFaceCounit_isIso : IsIso (closedFaceCounit R P downward) := by
  haveI (F : {b : B // P b} ⥤ ModuleCat.{u} R) :
      IsIso ((closedFaceCounit R P downward).app F) := by
    haveI (b : {b : B // P b}) :
        IsIso (((closedFaceCounit R P downward).app F).app b) := by
      change IsIso (closedFaceEvaluationEquiv R P downward F b.val b.property).toModuleIso.hom
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The comparison is the actual restriction/extension unit in each degree. -/
def closedFaceComplexUnit {ι : Type*} (shape : ComplexShape ι)
    (K : HomologicalComplex (B ⥤ ModuleCat.{u} R) shape) :
    K ⟶ (((closedFaceRestriction R P) ⋙
      closedFaceExtensionFunctor R P downward).mapHomologicalComplex shape).obj K :=
  (NatTrans.mapHomologicalComplex (closedFaceUnit R P downward) shape).app K

/-- Cohomological support suffices: individual terms may be nonzero
outside the closed set, and the coefficient complex may be unbounded. -/
theorem closedFaceComplexUnit_quasiIso {ι : Type*} (shape : ComplexShape ι)
    (K : HomologicalComplex (B ⥤ ModuleCat.{u} R) shape)
    (vanishes : ∀ b : B, ¬ P b →
      ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex shape).obj K).Acyclic) :
    QuasiIso (closedFaceComplexUnit R P downward shape K) := by
  classical
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro b
  by_cases hb : P b
  · haveI (q : ι) : IsIso
        (((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex shape).map
          (closedFaceComplexUnit R P downward shape K)).f q) :=
      closedFaceUnit_app_isIso R P downward (K.X q) b hb
    letI : IsIso ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex shape).map
        (closedFaceComplexUnit R P downward shape K)) :=
      HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  · rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_exactAt _ q (vanishes b hb q)).mpr
    exact HomologicalComplex.ExactAt.of_isZero
      (closedFaceExtension_isZero R P downward ((closedFaceRestriction R P).obj (K.X q)) b hb)

variable [HasDerivedCategory (B ⥤ ModuleCat.{u} R)]
  [HasDerivedCategory ({b : B // P b} ⥤ ModuleCat.{u} R)]

/-- Exact restriction and exact extension give an adjunction on the
entire unbounded derived categories. -/
def closedFaceDerivedAdjunction :
    (closedFaceRestriction R P).mapDerivedCategory ⊣
      (closedFaceExtensionFunctor R P downward).mapDerivedCategory :=
  exactDerivedAdjunction (closedFaceAdjunction R P downward)

/-- A complex with the stated support is represented by the literal
extension of its restriction, through the genuine unit. -/
def closedFaceSupportedDerivedIso
    (K : CochainComplex (B ⥤ ModuleCat.{u} R) ℤ)
    (vanishes : ∀ b : B, ¬ P b →
      ((((evaluation B (ModuleCat.{u} R)).obj b).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    DerivedCategory.Q.obj K ≅
      DerivedCategory.Q.obj ((((closedFaceRestriction R P) ⋙
        closedFaceExtensionFunctor R P downward).mapHomologicalComplex (.up ℤ)).obj K) := by
  letI := closedFaceComplexUnit_quasiIso R P downward (.up ℤ) K vanishes
  exact asIso (DerivedCategory.Q.map (closedFaceComplexUnit R P downward (.up ℤ) K))

end ToricPower.Cellular

end
