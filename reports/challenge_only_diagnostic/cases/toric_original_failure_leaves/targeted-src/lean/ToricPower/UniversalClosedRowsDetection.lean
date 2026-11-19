module

public import ToricPower.UniversalClosedRowsPartition
public import ToricPower.UniversalArrangementDerivedCoproducts
public import ToricPower.CoproductHomDetection

/-!
# An actual affine-plane component detects a nonzero closed-subtorus test

The full derived coproduct property is used here. It applies to arbitrary
unbounded targets and retains the complete integral component family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))
  (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
    ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c - latticeLift a ∈
      arrangementZeroSlice (augmentedForms A) selected)
  (k : Type) [Field k]

local instance rowsDetectionDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} k) :=
  HasDerivedCategory.standard _
local instance rowsDetectionDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) :=
  HasDerivedCategory.standard _

include covered in
/-- One genuine lattice translate detects the original nonzero map.
There is no degree bound or finiteness premise on the target. -/
theorem exists_nonzero_affine_plane_of_closed_rows
    (T : DerivedCategory (UniversalIncidenceObject A ⥤ ModuleCat.{0} k))
    (f : (DerivedCategory.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) 0).obj
      (universalCoverProjection A ⋙ closedIntegralRowsDiagram A selected k) ⟶ T)
    (nonzero : f ≠ 0) :
    ∃ m : Fin n → ℤ, ∃ g :
      (Cellular.closedConstantFunctor k (universalAffineSliceSupport A selected m)
        (universalAffineSliceSupport_downward A selected m)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)) ⟶ T,
      g ≠ 0 := by
  let family := Cellular.closedComponentDiagram k
    (universalClosedRowsSupport A selected) (universalClosedRowsSupport_downward A selected)
    (universalClosedRowsLabel A selected covered)
    (universalClosedRowsLabel_compatible A selected covered)
  let single := DerivedCategory.singleFunctor (UniversalIncidenceObject A ⥤ ModuleCat.{0} k) 0
  letI := universalArrangementSingle_preservesCoproducts A k (IntegralSliceValue A selected) 0
  obtain ⟨value,detected⟩ := exists_nonzero_coproduct_component family single
    (universalClosedRowsCoproductIso A selected covered k) f nonzero
  let a := single.map (colimit.ι (Discrete.functor family) ⟨value⟩ ≫
    (universalClosedRowsCoproductIso A selected covered k).hom) ≫ f
  let m := sliceValueRepresentative A selected value
  let frame := ((Cellular.closedConstantFunctor k (universalAffineSliceSupport A selected m)
    (universalAffineSliceSupport_downward A selected m)).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of k k) ≪≫
    single.mapIso (universalClosedRowsComponentIso A selected covered k value).symm
  refine ⟨m,frame.hom ≫ a,?_⟩
  intro zero
  apply detected
  rw [← cancel_epi frame.hom,comp_zero]
  exact zero

end ToricPower.IntegralArrangement

end
