module

public import ToricPower.ClosedPartitionDiagrams
public import ToricPower.ClosedConstantCongruence
public import ToricPower.ClosedSliceComponentIndex
public import ToricPower.ArrangementClosedSubtorus
public import ToricPower.ArrangementUniversalCover
public import ToricPower.ArrangementAffineSlice

/-!
# The whole lifted closed subtorus is the coproduct of its affine planes

Components are indexed by the image of the actual integral row map.
The coverage hypothesis says precisely that the selected integral
levels have integral representatives; regular fan cones supply it.
No finite character set is substituted for this unrestricted family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))

@[simp]
theorem universalCoverProjection_active (c : UniversalIncidenceObject A) :
    ((universalCoverProjection A).obj c).2.val.val.2 = c.2.val.2 := rfl

def universalClosedRowsSupport (c : UniversalIncidenceObject A) : Prop :=
  selected ⊆ c.2.val.2

theorem universalClosedRowsSupport_downward :
    Antitone (universalClosedRowsSupport A selected) := by
  intro c d h
  exact closedIntegralRowsSupport_incidence A selected
    ((universalCoverProjection A).map (homOfLE h))

variable (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
  ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c - latticeLift a ∈
    arrangementZeroSlice (augmentedForms A) selected)

/-- The actual selected ceiling levels, with their integral preimage. -/
def universalClosedRowsLabel (c : UniversalIncidenceObject A)
    (h : universalClosedRowsSupport A selected c) : IntegralSliceValue A selected :=
  ⟨fun j => c.2.val.1 j.val,
    cellLevel_mem_integralSliceValues A selected c.2 h (covered c.2 h)⟩

theorem universalClosedRowsLabel_compatible {c d : UniversalIncidenceObject A}
    (h : c ≤ d) (hd : universalClosedRowsSupport A selected d) :
    universalClosedRowsLabel A selected covered c
        (universalClosedRowsSupport_downward A selected h hd) =
      universalClosedRowsLabel A selected covered d hd := by
  apply Subtype.ext
  funext j
  exact closedRows_incidence_levels A selected c.2 d.2
    (universalClosedRowsSupport_downward A selected h hd) hd h j

/-- The component label identifies the literal affine plane, including
all of its lower dimensional boundary cells. -/
theorem universalClosedRowsComponent_iff_affine
    (value : IntegralSliceValue A selected) (c : UniversalIncidenceObject A) :
    Cellular.closedComponentSupport (universalClosedRowsSupport A selected)
        (universalClosedRowsLabel A selected covered) value c ↔
      universalAffineSliceSupport A selected (sliceValueRepresentative A selected value) c := by
  rw [universalAffineSliceSupport_iff_center,mem_arrangementAffineSlice]
  constructor
  · rintro ⟨active,equal⟩ j hj
    have level := cellCenter_mem (augmentedForms A) c.2 j
    rw [if_pos (active hj)] at level
    have label := congrArg (fun v : IntegralSliceValue A selected => v.val ⟨j,hj⟩) equal
    change c.2.val.1 j = value.val ⟨j,hj⟩ at label
    rw [level,augmentedForms_latticeLift,
      sliceValueRepresentative_values A selected value ⟨j,hj⟩,label]
  · intro inPlane
    have height : ∀ j : selected,
        augmentedForms A j.val (cellCenter (augmentedForms A) c.2) = (value.val j : ℝ) := by
      intro j
      rw [inPlane j.val j.property,augmentedForms_latticeLift,
        sliceValueRepresentative_values]
    have active : universalClosedRowsSupport A selected c := by
      intro j hj
      rw [← cellCenter_integralIndices A c.2]
      change augmentedForms A j (cellCenter (augmentedForms A) c.2) =
        (⌈augmentedForms A j (cellCenter (augmentedForms A) c.2)⌉ : ℝ)
      rw [height ⟨j,hj⟩,Int.ceil_intCast]
    refine ⟨active,?_⟩
    apply Subtype.ext
    funext j
    change c.2.val.1 j.val = value.val j
    rw [← ceil_eq_of_mem_cell (augmentedForms A) _ _ (cellCenter_mem _ c.2) j.val,
      height j,Int.ceil_intCast]

variable (k : Type) [Field k]

/-- This is the original base diagram pulled back by the genuine cover. -/
def closedIntegralRowsUniversalPullbackIso :
    universalCoverProjection A ⋙ closedIntegralRowsDiagram A selected k ≅
      (Cellular.closedConstantFunctor k (universalClosedRowsSupport A selected)
        (universalClosedRowsSupport_downward A selected)).obj (ModuleCat.of k k) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Each component is the actual closed scalar affine-plane diagram. -/
def universalClosedRowsComponentIso (value : IntegralSliceValue A selected) :
    Cellular.closedComponentDiagram k (universalClosedRowsSupport A selected)
        (universalClosedRowsSupport_downward A selected)
        (universalClosedRowsLabel A selected covered)
        (universalClosedRowsLabel_compatible A selected covered) value ≅
      (Cellular.closedConstantFunctor k
        (universalAffineSliceSupport A selected (sliceValueRepresentative A selected value))
        (universalAffineSliceSupport_downward A selected (sliceValueRepresentative A selected value))).obj
          (ModuleCat.of k k) :=
  (Cellular.closedConstantCongrIso k _ _ _ _
    (universalClosedRowsComponent_iff_affine A selected covered value)).app (ModuleCat.of k k)

/-- The complete categorical coproduct recovers the actual pulled-back
closed subtorus, with all incidence maps, not just its stalks. -/
def universalClosedRowsCoproductIso :
    colimit (Discrete.functor (Cellular.closedComponentDiagram k
      (universalClosedRowsSupport A selected) (universalClosedRowsSupport_downward A selected)
      (universalClosedRowsLabel A selected covered)
      (universalClosedRowsLabel_compatible A selected covered))) ≅
        universalCoverProjection A ⋙ closedIntegralRowsDiagram A selected k :=
  Cellular.closedPartitionCoproductIso k _ _ _ _ ≪≫
    (closedIntegralRowsUniversalPullbackIso A selected k).symm

end ToricPower.IntegralArrangement

end
