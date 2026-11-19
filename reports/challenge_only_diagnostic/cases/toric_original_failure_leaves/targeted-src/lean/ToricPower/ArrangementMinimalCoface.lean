module

public import ToricPower.ArrangementTopCofaceSupport
public import ToricPower.ArrangementRepresentableHomology

/-!
# A genuine top coface at the least allowed integral character

The nonzero ambient top class forces an actual top cellular coordinate.
The same coordinate remains allowed at every larger permitted character.
Its full Laurent basis is exactly the family of those characters.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A)
  (strictDirection : ∃ v : Fin n → ℝ, ∀ i ∈ Sum.inl '' S,
    0 < augmentedForms A i v)

include strictDirection in
theorem representedSupportedWeight_iff (m : Fin n → ℤ) :
    RepresentableSupportedWeight A S c m ↔
      ∀ j ∈ S, c.2.val.val.1 (.inl j) - 1 ≤ rayPairing A m j := by
  unfold RepresentableSupportedWeight
  rw [costalkRegion_nonempty_iff_integer _ _ _ _ strictDirection]
  constructor
  · intro h j hj
    have value := h (.inl j) ⟨j, hj, rfl⟩
    change ⌈augmentedForms A (.inl j) (cellCenter (augmentedForms A) c.2.val)⌉ - 1 ≤
      rayPairing A m j at value
    rw [ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.2.val) (.inl j)] at value
    exact value
  · intro h j hj
    obtain ⟨j, hj, rfl⟩ := hj
    change ⌈augmentedForms A (.inl j) (cellCenter (augmentedForms A) c.2.val)⌉ - 1 ≤
      rayPairing A m j
    rw [ceil_eq_of_mem_cell (augmentedForms A) _ _
      (cellCenter_mem (augmentedForms A) c.2.val) (.inl j)]
    exact h j hj

variable (minimal : Fin n → ℤ)
  (minimal_eq : ∀ j ∈ S, rayPairing A minimal j = c.2.val.val.1 (.inl j) - 1)

include strictDirection minimal_eq in
theorem representedMinimalTopCoface_nonempty :
    Nonempty (RepresentableCostalkIndex A c S minimal n) := by
  have supported : RepresentableSupportedWeight A S c minimal :=
    (representedSupportedWeight_iff A S c strictDirection minimal).mpr
      (fun j hj => (minimal_eq j hj).ge)
  by_contra empty
  letI : IsEmpty (RepresentableCostalkIndex A c S minimal n) :=
    not_nonempty_iff.mp empty
  let K := representedWeightCellularComplex A S c minimal ℚ
  have zeroTerm : IsZero (K.X n) :=
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of ℚ (RepresentableCostalkIndex A c S minimal n →₀ ℚ))).of_iso
        (representedWeightCellularCoordinates A S c minimal ℚ n).toModuleIso
  have zeroHomology : IsZero (K.homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) zeroTerm
  have zeroField : IsZero (ModuleCat.of ℚ ℚ) := zeroHomology.of_iso
    (representedWeightCellularHomologyIso A S c minimal ℚ supported).symm
  letI : Subsingleton ℚ := ModuleCat.subsingleton_of_isZero zeroField
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

def representedMinimalTopCoface : RepresentableCostalkIndex A c S minimal n :=
  Classical.choice (representedMinimalTopCoface_nonempty A S c strictDirection minimal minimal_eq)

variable (p : RepresentableCostalkIndex A c S minimal n)

include strictDirection minimal_eq in
theorem representedMinimalTopCoface_allowed (m : Fin n → ℤ)
    (supported : RepresentableSupportedWeight A S c m) :
    ∀ j ∈ S, 0 ≤ rayPairing A (m + p.val.2.val) j + reflectedCeiling A p.val.1.val j := by
  intro j hj
  have hm := (representedSupportedWeight_iff A S c strictDirection m).mp supported j hj
  have hp := p.property j hj
  rw [rayPairing_add, minimal_eq j hj] at hp
  rw [rayPairing_add]
  omega

/-- The chosen cell and incidence, in each permitted character. -/
def representedMinimalTopCofaceAt (m : Fin n → ℤ)
    (supported : RepresentableSupportedWeight A S c m) :
    RepresentableCostalkIndex A c S m n :=
  ⟨p.val, representedMinimalTopCoface_allowed A S c strictDirection minimal minimal_eq p m supported⟩

/-- The complete Laurent coefficient set is the complete permitted
character family; the proof fiber is lifted to a genuine small type. -/
def representedMinimalCofaceProofEquiv :
    ReflectedLaurentWeight A S ⟨n,p.val.1⟩ ≃
      Σ m : Fin n → ℤ, PLift (RepresentableSupportedWeight A S c m) where
  toFun r := ⟨r.val - p.val.2.val, ⟨by
    let q : RepresentableCostalkIndex A c S (r.val - p.val.2.val) n :=
      ⟨p.val, by simpa only [sub_add_cancel] using r.property⟩
    let d := (representedCostalkSupportIndexEquiv A S c (r.val - p.val.2.val) n).symm q
    exact ⟨cellCenter (augmentedForms A) d.val, d.property⟩⟩⟩
  invFun r := ⟨r.1 + p.val.2.val,
    representedMinimalTopCoface_allowed A S c strictDirection minimal minimal_eq p r.1 r.2.down⟩
  left_inv r := by
    apply Subtype.ext
    exact sub_add_cancel r.val p.val.2.val
  right_inv r := by
    rcases r with ⟨m, h⟩
    apply Sigma.ext (add_sub_cancel_right m p.val.2.val)
    exact Subsingleton.helim
      (congrArg (fun t => PLift (RepresentableSupportedWeight A S c t))
        (add_sub_cancel_right m p.val.2.val)) _ _

end ToricPower.IntegralArrangement

end
