module

public import ToricPower.ClosedSupportDetection
public import ToricPower.PointClosedPullback

/-! # Restricting the original closed scalar test to the target carrier -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.Cellular

variable (k : Type) [Field k] {B : Type} [Preorder B]
  (P Q : B → Prop) (downP : Antitone P) (downQ : Antitone Q)

local instance scalarRestrictionDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance scalarRestrictionDerivedFull : HasDerivedCategory.{1} (B ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance scalarRestrictionDerivedClosed :
    HasDerivedCategory.{1} ({b : B // P b} ⥤ ModuleCat.{0} k) := HasDerivedCategory.standard _

/-- The restricted whole scalar-coefficient functor is exactly the
closed coefficient on the intersection of the two original supports. -/
def closedScalarRestrictionIso (V : DerivedCategory (ModuleCat.{0} k)) :
    (closedFaceRestriction k P).mapDerivedCategory.obj
      ((closedConstantFunctor k Q downQ).mapDerivedCategory.obj V) ≅
    (closedConstantFunctor k (fun d : {b : B // P b} => Q d.val)
      (fun _ _ h => downQ h)).mapDerivedCategory.obj V :=
  (Functor.mapDerivedCategoryCompIso (closedConstantFunctor k Q downQ)
    (closedFaceRestriction k P)).app V ≪≫
    (exactDerivedFunctorIso
      (closedConstantRestrictionIso k Q downQ (closedFaceInclusion P))).app V

include downP in
/-- Nonvanishing is retained through the actual restriction/extension
adjunction and the literal scalar coefficient frame. -/
theorem restrict_nonzero_closed_scalar_test
    (K : CochainComplex (B ⥤ ModuleCat.{0} k) ℤ)
    (vanishes : ∀ b : B, ¬ P b →
      ((((evaluation B (ModuleCat.{0} k)).obj b).mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (f : (closedConstantFunctor k Q downQ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶
        DerivedCategory.Q.obj K) (nonzero : f ≠ 0) :
    ∃ g : (closedConstantFunctor k (fun d : {b : B // P b} => Q d.val)
      (fun _ _ h => downQ h)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶
      (closedFaceRestriction k P).mapDerivedCategory.obj (DerivedCategory.Q.obj K), g ≠ 0 := by
  obtain ⟨g,hg⟩ := restrict_nonzero_into_closed_support k P downP K vanishes _ f nonzero
  let e := closedScalarRestrictionIso k P Q downQ
    ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k))
  refine ⟨e.inv ≫ g,?_⟩
  intro zero
  apply hg
  rw [← cancel_epi e.inv,comp_zero]
  exact zero

end ToricPower.Cellular

end
