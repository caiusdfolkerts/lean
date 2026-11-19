module

public import ToricPower.ClosedScalarTestRestriction
public import ToricPower.ClosedSupportShiftedDetection

/-! # A scalar test in any degree restricts to the actual closed carrier -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

variable (k : Type) [Field k] {B : Type} [Preorder B]
  (P Q : B → Prop) (downP : Antitone P) (downQ : Antitone Q)

local instance scalarShiftRestrictionDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance scalarShiftRestrictionDerivedFull :
    HasDerivedCategory.{1} (B ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _
local instance scalarShiftRestrictionDerivedClosed :
    HasDerivedCategory.{1} ({b : B // P b} ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

include downP in
/-- The degree is unchanged, and every map is the original closed-support
adjunction map composed with the literal coefficient frame. -/
theorem restrict_shifted_nonzero_closed_scalar_test
    (K : CochainComplex (B ⥤ ModuleCat.{0} k) ℤ)
    (vanishes : ∀ b : B, ¬ P b →
      ((((evaluation B (ModuleCat.{0} k)).obj b).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (q : ℤ)
    (f : (closedConstantFunctor k Q downQ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶
        (DerivedCategory.Q.obj K)⟦q⟧) (nonzero : f ≠ 0) :
    ∃ g : (closedConstantFunctor k (fun d : {b : B // P b} => Q d.val)
      (fun _ _ h => downQ h)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶
      ((closedFaceRestriction k P).mapDerivedCategory.obj (DerivedCategory.Q.obj K))⟦q⟧,
      g ≠ 0 := by
  let source := (closedConstantFunctor k Q downQ).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k))
  let target := ((closedFaceRestriction k P).mapDerivedCategory.obj
    (DerivedCategory.Q.obj K))⟦q⟧
  let model := shiftedClosedSupportModelIso k P downP K vanishes q
  let adj := closedFaceDerivedAdjunction k P downP
  let a := (adj.homEquiv source target).symm (f ≫ model.hom)
  have nonzeroA : a ≠ 0 := by
    intro zero
    have mapped := congrArg (adj.homEquiv source target) zero
    rw [Equiv.apply_symm_apply,adj.homAddEquiv_zero] at mapped
    apply nonzero
    rw [← cancel_mono model.hom,zero_comp]
    exact mapped
  let frame := closedScalarRestrictionIso k P Q downQ
    ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k))
  refine ⟨frame.inv ≫ a,?_⟩
  intro zero
  apply nonzeroA
  rw [← cancel_epi frame.inv,comp_zero]
  exact zero

end ToricPower.Cellular

end
