module

public import ToricPower.ArrangementClosedSubtorus
public import ToricPower.ArrangementLaurentLabels

/-! # Every closed-slice Laurent coefficient is a genuine lifted cell

The complete monomial family is reindexed by original universal cells
on the periodic closed slice, inside the literal open chart region.
The signed translation is the same one used by the actual incidence
maps. No lattice weight or connected component is discarded.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s))

theorem translatedCell_openWeight_zero_iff {q : ℕ}
    (c : NormalizedCell A q) (m : Fin n → ℤ) :
    cellCenter (augmentedForms A) (translateCell A (-m) c.val) ∈
        openWeightRegion (augmentedForms A) (Sum.inl '' S)
          (augmentedLatticePairing A 0) ↔
      ∀ j ∈ S, 0 ≤ rayPairing A m j + reflectedCeiling A c.val j := by
  rw [cellCenter_openWeight_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  have zero : rayPairing A (0 : Fin n → ℤ) j = 0 := by simp [rayPairing]
  have negative : rayPairing A (-m) j = -rayPairing A m j := by
    simp [rayPairing,mul_neg,Finset.sum_neg_distrib]
  rw [reflectedCeiling_translate,negative,zero]
  omega

/-- Literal monomial coordinates of the closed constant coefficient
at every original normalized cell. -/
def ClosedSliceLaurentIndex (q : ℕ) :=
  Σ c : {c : NormalizedCell A q // closedIntegralRowsSupport A selected ⟨q,c⟩},
    ReflectedLaurentWeight A S ⟨q,c.val⟩

def ClosedSliceOpenCell (q : ℕ) :=
  {d : Cell (augmentedForms A) q // selected ⊆ d.val.2 ∧
    cellCenter (augmentedForms A) d ∈
      openWeightRegion (augmentedForms A) (Sum.inl '' S) (augmentedLatticePairing A 0)}

/-- The full index equivalence uses each lattice translate exactly once. -/
def closedSliceLaurentCellEquiv (q : ℕ) :
    ClosedSliceLaurentIndex A selected S q ≃ ClosedSliceOpenCell A selected S q := by
  let first : ClosedSliceLaurentIndex A selected S q ≃
      {p : NormalizedCell A q × (Fin n → ℤ) //
        closedIntegralRowsSupport A selected ⟨q,p.1⟩ ∧
          ∀ j ∈ S, 0 ≤ rayPairing A p.2 j + reflectedCeiling A p.1.val j} :=
    { toFun := fun p => ⟨⟨p.1.val,p.2.val⟩,p.1.property,p.2.property⟩
      invFun := fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
      left_inv := fun p => by rcases p with ⟨⟨c,hc⟩,⟨m,hm⟩⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨c,m⟩,hc,hm⟩; rfl }
  refine first.trans ((signedCellOrbitEquiv A q).symm.subtypeEquiv ?_)
  intro p
  change (closedIntegralRowsSupport A selected ⟨q,p.1⟩ ∧ _) ↔
    (selected ⊆ (translateCell A (-p.2) p.1.val).val.2 ∧ _)
  exact and_congr Iff.rfl (translatedCell_openWeight_zero_iff A S p.1 p.2).symm

@[simp]
theorem closedSliceLaurentCellEquiv_val (q : ℕ) (p : ClosedSliceLaurentIndex A selected S q) :
    (closedSliceLaurentCellEquiv A selected S q p).val =
      translateCell A (-p.2.val) p.1.val.val := rfl

/-- The actual positive monomial incidence is exactly the original
closed-cell inclusion after the signed Laurent reindexing. -/
theorem reflectedLaurent_lifted_incidence {c d : IncidenceObject A}
    (f : c ⟶ d) (m : ReflectedLaurentWeight A S c) :
    closedCell (augmentedForms A) (translateCell A (-m.val) c.2.val).val.1
        (translateCell A (-m.val) c.2.val).val.2 ⊆
      closedCell (augmentedForms A)
        (translateCell A (-(reflectedLaurentWeightMap A S f m).val) d.2.val).val.1
        (translateCell A (-(reflectedLaurentWeightMap A S f m).val) d.2.val).val.2 := by
  intro x hx
  have original := (mem_translatedClosedCell_iff A c.2.val (-m.val) x).mp hx
  have target := f.property _ original
  apply (mem_translatedClosedCell_iff A d.2.val
    (-(reflectedLaurentWeightMap A S f m).val) x).mpr
  have points : x - latticeLift (-(reflectedLaurentWeightMap A S f m).val) =
      x - latticeLift (-m.val) + latticeLift f.val := by
    change x-latticeLift (-(m.val+f.val)) = _
    rw [latticeLift_neg,latticeLift_neg,latticeLift_add]
    abel
  rw [points]
  exact target

end ToricPower.IntegralArrangement

end
