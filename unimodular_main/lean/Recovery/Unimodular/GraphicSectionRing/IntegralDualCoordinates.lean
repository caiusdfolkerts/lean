module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Recovery.Unimodular.GraphicSectionRing.Height

/-! The actual contragredient integral change of coordinates on characters. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.GraphicSectionRing
attribute [local instance] Classical.decEq
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The inverse transpose, defined using the actual integral dual modules. -/
def dualCoordinates (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) :
    (I → ℤ) ≃ₗ[ℤ] (J → ℤ) :=
  (dotProductEquiv ℤ I).trans (e.symm.dualMap.trans (dotProductEquiv ℤ J).symm)

/-- The original lattice pairing is preserved exactly. -/
theorem dualCoordinates_pairing (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) (x m : I → ℤ) :
    dotProduct x m = dotProduct (e x) (dualCoordinates e m) := by
  have h := congrArg (fun f : Module.Dual ℤ (J → ℤ) => f (e x))
    ((dotProductEquiv ℤ J).apply_symm_apply (e.symm.dualMap ((dotProductEquiv ℤ I) m)))
  change dotProduct (dualCoordinates e m) (e x) = dotProduct m (e.symm (e x)) at h
  rw [LinearEquiv.symm_apply_apply] at h
  simpa only [dotProduct_comm] using h.symm

 theorem integral_coordinate_card (e : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)) :
    Fintype.card I = Fintype.card J := by
  calc
    Fintype.card I = Module.finrank ℤ (I → ℤ) :=
      (Module.finrank_eq_card_basis (Pi.basisFun ℤ I)).symm
    _ = Module.finrank ℤ (J → ℤ) := e.finrank_eq
    _ = Fintype.card J := Module.finrank_eq_card_basis (Pi.basisFun ℤ J)

/-- The zero anchor, used uniformly for single-coordinate normals. -/
def coordinateNormal {n : ℕ} : Coordinate n → Lattice n
  | none => 0
  | some i => Pi.single i 1

 theorem coordinateNormal_pairing {n : ℕ} (i : Coordinate n) (m : Lattice n) :
    dotProduct (coordinateNormal i) m = anchored m i := by
  cases i <;> simp [coordinateNormal, anchored, dotProduct, Pi.single_apply]

 theorem differenceNormal_pairing {n : ℕ} (i j : Coordinate n) (m : Lattice n) :
    dotProduct (coordinateNormal i - coordinateNormal j) m = difference m i j := by
  rw [sub_dotProduct, coordinateNormal_pairing, coordinateNormal_pairing]
  rfl

#print axioms dualCoordinates_pairing
#print axioms integral_coordinate_card
#print axioms differenceNormal_pairing

end Unimodular.GraphicSectionRing

#check Unimodular.GraphicSectionRing.dualCoordinates_pairing
