module

public import PaperVerification.ToricCartierOrders

@[expose] public section

/-!
# The local equations compute actual Cartier orders

The fractional sheaf reconstructed from a rational Cartier cocycle has
the specified local rational generators. This connects its intrinsic
Weil coefficients to the input equations through the actual sheaf frames.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

theorem localFrame_frameLinearEquiv (i : C.index) (V : X.Opens)
    (hV : V≤C.openSet i) :
    C.toCartierData.frameLinearEquiv (C.localFrame i) V hV =
      C.localCoordinates i V hV := rfl

/-- The sheaf construction recovers the literal rational generator,
including its multiplicative scalar. -/
theorem localFrame_rationalGenerator (i : C.index) [Nonempty (C.openSet i)] :
    C.toCartierData.frameRationalGenerator (C.localFrame i) =
      (C.generator i : X.functionField) := by
  let U := C.openSet i
  let s := C.toCartierData.frameGenerator (C.localFrame i) U le_rfl
  have hs : C.localCoordinates i U le_rfl s = 1 := by
    rw [← C.localFrame_frameLinearEquiv]
    exact LinearEquiv.apply_symm_apply _ _
  have h := C.localCoordinates_value i U le_rfl s
  rw [hs,map_one] at h
  change rationalValue X U s.val = (C.generator i : X.functionField)
  exact (div_eq_one_iff_eq (Units.ne_zero _)).mp h.symm

variable [IsLocallyNoetherian X]

/-- The sign is fixed by taking local generators of `O(D)`, rather than
local equations of `D`. -/
theorem weilCoefficient_eq (i : C.index) {x : X} (hx : x∈C.openSet i) :
    C.toCartierData.weilCoefficient x = -X.ord (C.generator i : X.functionField) x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hx⟩⟩
  rw [C.toCartierData.weilCoefficient_eq_neg_frameOrder (C.localFrame i) hx,
    C.localFrame_rationalGenerator]

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.weilCoefficient_eq
