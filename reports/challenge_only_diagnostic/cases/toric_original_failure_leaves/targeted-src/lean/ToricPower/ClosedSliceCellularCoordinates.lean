module

public import ToricPower.ClosedSliceLaurentCoefficients
public import ToricPower.ArrangementCochainFreeCoordinates

/-! # Actual closed-slice cellular terms, with every Laurent coefficient

The original cellular functor is evaluated on the ordinary closed
constant diagram. Canonical copower and finite cellwise biproduct
coordinates identify its terms with all supported pairs of a normalized
cell and an integral Laurent monomial. The signed orbit equivalence
then identifies those pairs with every actual universal-cover cell.
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

/-- The original scalar Laurent realization of the closed constant diagram. -/
def closedSliceCellularComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  (arrangementCellularRealization A k Q).obj F

/-- Regroup only the proof of closed support; every monomial remains. -/
def closedSliceCellIndexEquiv (q : ℕ) :
    (Σ c : NormalizedCell A q, ClosedSliceCellLaurentIndex A selected S ⟨q,c⟩) ≃
      ClosedSliceLaurentIndex A selected S q where
  toFun p := ⟨⟨p.1,p.2.1.down⟩,p.2.2⟩
  invFun p := ⟨p.1.val,⟨⟨p.1.property⟩,p.2⟩⟩
  left_inv p := by rcases p with ⟨c,⟨h⟩,m⟩; rfl
  right_inv p := by rcases p with ⟨⟨c,h⟩,m⟩; rfl

/-- Coordinates of the actual cellular term through its canonical
coefficient bases and finite cellwise biproduct. -/
def closedSliceCellularCoordinates (q : ℕ) :
    (closedSliceCellularComplex A selected S k).X q ≃ₗ[k]
      (ClosedSliceLaurentIndex A selected S q →₀ k) :=
  (cellularCochainFreeCoordinates A k D
    (ClosedSliceCellLaurentIndex A selected S)
    (closedSliceLaurentCellCoordinates A selected S k) q).trans
      (Finsupp.mapDomain.linearEquiv k k (closedSliceCellIndexEquiv A selected S q))

theorem closedSliceCellularCoordinates_apply (q : ℕ)
    (x : (closedSliceCellularComplex A selected S k).X q)
    (p : ClosedSliceLaurentIndex A selected S q) :
    closedSliceCellularCoordinates A selected S k q x p =
      closedSliceLaurentCellCoordinates A selected S k ⟨q,p.1.val⟩
        (arrangementCellularCochainProjection A k D q p.1.val x)
        ⟨⟨p.1.property⟩,p.2⟩ := by
  change Finsupp.mapDomain (closedSliceCellIndexEquiv A selected S q)
    (cellularCochainFreeCoordinates A k D
      (ClosedSliceCellLaurentIndex A selected S)
      (closedSliceLaurentCellCoordinates A selected S k) q x) p = _
  have value := Finsupp.mapDomain_apply_of_injective
    (closedSliceCellIndexEquiv A selected S q).injective
    (cellularCochainFreeCoordinates A k D
      (ClosedSliceCellLaurentIndex A selected S)
      (closedSliceLaurentCellCoordinates A selected S k) q x)
    ((closedSliceCellIndexEquiv A selected S q).symm p)
  rw [Equiv.apply_symm_apply] at value
  exact value.trans (cellularCochainFreeCoordinates_apply A k D
    (ClosedSliceCellLaurentIndex A selected S)
    (closedSliceLaurentCellCoordinates A selected S k) q x p.1.val
      ⟨⟨p.1.property⟩,p.2⟩)

/-- Each displayed free coefficient is the original cochain inclusion. -/
theorem closedSliceCellularCoordinates_generator (q : ℕ)
    (p : ClosedSliceLaurentIndex A selected S q) (r : k) :
    closedSliceCellularCoordinates A selected S k q
      (arrangementCellularCochainInclusion A k D q p.1.val
        ((closedSliceLaurentCellCoordinates A selected S k ⟨q,p.1.val⟩).symm
          (Finsupp.single ⟨⟨p.1.property⟩,p.2⟩ r))) = Finsupp.single p r := by
  change Finsupp.mapDomain (closedSliceCellIndexEquiv A selected S q)
    (cellularCochainFreeCoordinates A k D
      (ClosedSliceCellLaurentIndex A selected S)
      (closedSliceLaurentCellCoordinates A selected S k) q
      (arrangementCellularCochainInclusion A k D q p.1.val
        ((closedSliceLaurentCellCoordinates A selected S k ⟨q,p.1.val⟩).symm
          (Finsupp.single ⟨⟨p.1.property⟩,p.2⟩ r)))) = _
  rw [cellularCochainFreeCoordinates_generator,Finsupp.mapDomain_single]
  rfl

theorem closedSliceCellularCoordinates_symm_single (q : ℕ)
    (p : ClosedSliceLaurentIndex A selected S q) (r : k) :
    (closedSliceCellularCoordinates A selected S k q).symm (Finsupp.single p r) =
      arrangementCellularCochainInclusion A k D q p.1.val
        ((closedSliceLaurentCellCoordinates A selected S k ⟨q,p.1.val⟩).symm
          (Finsupp.single ⟨⟨p.1.property⟩,p.2⟩ r)) := by
  apply (closedSliceCellularCoordinates A selected S k q).injective
  rw [LinearEquiv.apply_symm_apply,closedSliceCellularCoordinates_generator]

/-- No parallel component is removed by the genuine universal-cell coordinates. -/
def closedSliceUniversalCellularCoordinates (q : ℕ) :
    (closedSliceCellularComplex A selected S k).X q ≃ₗ[k]
      (ClosedSliceOpenCell A selected S q →₀ k) :=
  (closedSliceCellularCoordinates A selected S k q).trans
    (Finsupp.mapDomain.linearEquiv k k (closedSliceLaurentCellEquiv A selected S q))

end ToricPower.IntegralArrangement

end
