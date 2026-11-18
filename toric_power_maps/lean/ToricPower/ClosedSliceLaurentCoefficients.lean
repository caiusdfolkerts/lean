module

public import ToricPower.ClosedCoefficientCopower
public import ToricPower.ClosedSliceLaurentCells
public import ToricPower.ArrangementRepresentableTerms

/-! # Literal closed-slice coefficients in every Laurent character

The scalar coefficient is the ordinary closed constant diagram. These
coordinates are derived from its actual copower universal property.
Every permitted character is retained, and the generator formula fixes
the coefficient normalization before comparing cellular differentials.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (selected : Set (Fin s ⊕ Fin n)) (S : Set (Fin s))
  (k : Type) [Field k]

local notation "Q" => reflectedLaurentDiagram A S k
local notation "F" => closedIntegralRowsDiagram A selected k
local notation "D" => Cellular.covariantCopowerDiagram k Q F

def ClosedSliceCellLaurentIndex (c : IncidenceObject A) :=
  Σ _h : PLift (closedIntegralRowsSupport A selected c), ReflectedLaurentWeight A S c

def closedSliceLaurentCoefficientIso :
    Cellular.covariantCopowerDiagram k Q F ≅
      Cellular.closedLabelFunctor k Q (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected) :=
  Cellular.closedCoefficientCopowerIso k Q (closedIntegralRowsSupport A selected)
    (closedIntegralRowsSupport_incidence A selected)

def closedSliceLaurentCellCoordinates (c : IncidenceObject A) :
    (D).obj c ≃ₗ[k] (ClosedSliceCellLaurentIndex A selected S c →₀ k) :=
  ((closedSliceLaurentCoefficientIso A selected S k).app c).toLinearEquiv.trans
    (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm

theorem closedSliceLaurentCellCoordinates_inclusion (c : IncidenceObject A)
    (x : PLift (closedIntegralRowsSupport A selected c) → k)
    (v : ReflectedLaurentWeight A S c →₀ k)
    (h : PLift (closedIntegralRowsSupport A selected c))
    (m : ReflectedLaurentWeight A S c) :
    closedSliceLaurentCellCoordinates A selected S k c
        (Cellular.vectorCopowerInclusion k ((Q).obj c) ((F).obj c) x v) ⟨h,m⟩ =
      x h • v m := by
  exact congrArg (fun z : ReflectedLaurentWeight A S c →₀ k => z m)
    (Cellular.vectorCopowerFiniteFunctionsIso_inclusion k ((Q).obj c)
      (PLift (closedIntegralRowsSupport A selected c)) x v h)

/-- A supported scalar generator and an actual Laurent monomial give
the corresponding literal free coefficient, with coefficient one. -/
theorem closedSliceLaurentCellCoordinates_generator (c : IncidenceObject A)
    (h : closedIntegralRowsSupport A selected c)
    (m : ReflectedLaurentWeight A S c) (a : k) :
    closedSliceLaurentCellCoordinates A selected S k c
        (Cellular.vectorCopowerInclusion k ((Q).obj c) ((F).obj c)
          (fun _ => 1) (Finsupp.single m a)) =
      Finsupp.single ⟨⟨h⟩,m⟩ a := by
  ext p
  rcases p with ⟨hp,l⟩
  rw [closedSliceLaurentCellCoordinates_inclusion]
  rw [one_smul]
  have same : (⟨⟨h⟩,m⟩ : ClosedSliceCellLaurentIndex A selected S c) = ⟨hp,l⟩ ↔ m = l := by
    constructor
    · intro equal
      exact congrArg (fun p : ClosedSliceCellLaurentIndex A selected S c => p.2) equal
    · intro equal
      subst l
      rfl
  simp only [Finsupp.single_apply,same]

theorem closedSliceLaurentCellCoordinates_symm_single (c : IncidenceObject A)
    (h : closedIntegralRowsSupport A selected c)
    (m : ReflectedLaurentWeight A S c) (a : k) :
    (closedSliceLaurentCellCoordinates A selected S k c).symm
        (Finsupp.single ⟨⟨h⟩,m⟩ a) =
      Cellular.vectorCopowerInclusion k ((Q).obj c) ((F).obj c)
        (fun _ => 1) (Finsupp.single m a) := by
  apply (closedSliceLaurentCellCoordinates A selected S k c).injective
  rw [LinearEquiv.apply_symm_apply,closedSliceLaurentCellCoordinates_generator]

/-- The actual positive-character map acts on every scalar generator,
including all supported target cells and every genuine incidence. -/
theorem closedSliceLaurentCellMap_generator {c d : IncidenceObject A}
    (f : c ⟶ d) (hc : closedIntegralRowsSupport A selected c)
    (hd : closedIntegralRowsSupport A selected d)
    (m : ReflectedLaurentWeight A S c) (a : k) :
    closedSliceLaurentCellCoordinates A selected S k d
        ((D).map f
          ((closedSliceLaurentCellCoordinates A selected S k c).symm
            (Finsupp.single ⟨⟨hc⟩,m⟩ a))) =
      Finsupp.single ⟨⟨hd⟩,reflectedLaurentWeightMap A S f m⟩ a := by
  rw [closedSliceLaurentCellCoordinates_symm_single]
  have action := ConcreteCategory.congr_hom
    (Cellular.covariantCopowerDiagram_map_inclusion k Q F f (fun _ => 1))
    (Finsupp.single m a)
  simp only [ModuleCat.comp_apply,reflectedLaurentDiagram_map_single] at action
  exact (congrArg (closedSliceLaurentCellCoordinates A selected S k d) action).trans
    (closedSliceLaurentCellCoordinates_generator A selected S k d hd
      (reflectedLaurentWeightMap A S f m) a)

end ToricPower.IntegralArrangement

end
