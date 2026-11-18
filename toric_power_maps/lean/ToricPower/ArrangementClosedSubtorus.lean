module

public import ToricPower.ArrangementIncidenceCategory
public import ToricPower.ArrangementUniversalCells
public import ToricPower.OpenClosedScalar
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Literal closed constant coefficients on integral row levels

Every individual translated face arrow is retained. The support consists
of exactly those cells on which the selected integral forms have integer
values. The coefficient is the ordinary constant scalar module on this
closed support and zero off it. In the toric specialization a separate
integral-basis argument identifies this set with a connected subtorus.
-/

@[expose] public noncomputable section

open CategoryTheory Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (selected : Set (Fin s ⊕ Fin n))

/-- The original normalized cell lies on all the selected integer
hyperplanes. This includes every boundary cell of the closed support. -/
def closedIntegralRowsSupport (c : IncidenceObject A) : Prop :=
  selected ⊆ c.2.val.val.2

theorem closedIntegralRowsSupport_iff_integer (c : IncidenceObject A) :
    closedIntegralRowsSupport A selected c ↔
      ∀ j ∈ selected, ∃ z : ℤ,
        augmentedForms A j (cellCenter (augmentedForms A) c.2.val) = (z : ℝ) := by
  constructor
  · intro supported j hj
    refine ⟨c.2.val.val.1 j,?_⟩
    have point := cellCenter_mem (augmentedForms A) c.2.val j
    rwa [if_pos (supported hj)] at point
  · intro integer j hj
    rw [← cellCenter_integralIndices A c.2.val]
    change augmentedForms A j (cellCenter (augmentedForms A) c.2.val) =
      (⌈augmentedForms A j (cellCenter (augmentedForms A) c.2.val)⌉ : ℝ)
    obtain ⟨z,hz⟩ := integer j hj
    rw [hz,Int.ceil_intCast]

/-- Downward closedness is checked on every actual incidence,
including its lattice translation. -/
theorem closedIntegralRowsSupport_incidence {c d : IncidenceObject A} (f : c ⟶ d) :
    closedIntegralRowsSupport A selected d → closedIntegralRowsSupport A selected c := by
  intro supported
  apply (closedIntegralRowsSupport_iff_integer A selected c).mpr
  intro j hj
  have point := f.property (cellCenter (augmentedForms A) c.2.val)
    (cell_subset_closedCell _ _ _ (cellCenter_mem _ c.2.val)) j
  rw [if_pos (supported hj),map_add,augmentedForms_latticeLift] at point
  refine ⟨d.2.val.val.1 j - augmentedLatticePairing A f.val j,?_⟩
  rw [Int.cast_sub]
  linarith

variable (k : Type) [CommRing k]

/-- Actual closed constant coefficients, with all face maps given by
their literal restrictions. -/
def closedIntegralRowsDiagram : IncidenceObject A ⥤ ModuleCat k where
  obj c := ModuleCat.of k (PLift (closedIntegralRowsSupport A selected c) → k)
  map f := ModuleCat.ofHom (MorseCoefficients.closedScalarMap k
    (closedIntegralRowsSupport_incidence A selected f))
  map_id c := rfl
  map_comp f g := rfl

end ToricPower.IntegralArrangement

end
