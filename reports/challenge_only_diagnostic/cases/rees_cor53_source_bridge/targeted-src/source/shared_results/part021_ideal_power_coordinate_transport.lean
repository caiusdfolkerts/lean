module
public import graph_foundation.part014
public import shared_results.part021_groebner_rees_order_coordinate_lifting

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealPowerCoordinateTransport -/
section

/-!
# Native ideal coordinates and scalar-restricted Rees coefficients

The two presentations have identical underlying polynomials.  Their scalar
module dictionaries need not be definitionally equal.  The explicit
identity maps below retain the coordinates, differential, and basis, and
therefore retain the complete original-order cycle-lifting statement.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul MvPolynomial

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J^s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

def nativePowerCoefficientBasis (s p : ℕ) :
    Module.Basis (PowerIdealIndex m J s p) K (Set.powersetCard V p →₀ ↥(J^s)) :=
  Finsupp.basis (fun _ => groebnerIdealBasis m (J^s) (G s) (hG s) (hu s))

def powerIdealCoordinateEquiv (s p : ℕ) :
    (Set.powersetCard V p →₀ ↥(J^s)) ≃ₗ[K] PowerIdealCoordinates J s p :=
  Finsupp.mapRange.linearEquiv (idealScalarRestrictionEquiv (J^s))

@[simp] theorem powerIdealCoordinateEquiv_apply (s p : ℕ)
    (x : Set.powersetCard V p →₀ ↥(J^s)) (F : Set.powersetCard V p) :
    (powerIdealCoordinateEquiv J s p x F).val = (x F).val := rfl

/-- The same coefficient identity as a map over the polynomial ring. -/
def idealPowerRestrictionLinear (s : ℕ) : ↥(J^s) →ₗ[MvPolynomial V K] idealPowerPiece J s where
  toFun x := ⟨x.val, x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem powerIdealCoordinateEquiv_basis (s p : ℕ) (a : PowerIdealIndex m J s p) :
    powerIdealCoordinateEquiv J s p (nativePowerCoefficientBasis m J G hG hu s p a) =
      powerIdealCoefficientBasis m J G hG hu s p a := by
  rw [nativePowerCoefficientBasis, powerIdealCoefficientBasis, Finsupp.coe_basis,
    Finsupp.coe_basis]
  change Finsupp.mapRange (idealScalarRestrictionEquiv (J^s))
      (idealScalarRestrictionEquiv (J^s)).map_zero
      (Finsupp.single a.1 (groebnerIdealBasis m (J^s) (G s) (hG s) (hu s) a.2)) = _
  rw [Finsupp.mapRange_single]
  rfl

theorem powerIdealCoordinateEquiv_differential (s p : ℕ)
    (x : Set.powersetCard V p →₀ ↥(J^s)) :
    powerPreviousDifferential J s p (powerIdealCoordinateEquiv J s p x) =
      powerIdealCoordinateEquiv J s p.pred (actualIdealPreviousDifferential (J^s) p x) := by
  cases p with
  | zero => exact (powerIdealCoordinateEquiv J s 0).map_zero.symm
  | succ p =>
    exact coordinateDifferential_mapRange (X : V → MvPolynomial V K)
      (ModuleCat.of (MvPolynomial V K) ↥(J^s))
      (ModuleCat.of (MvPolynomial V K) (idealPowerPiece J s))
      (idealPowerRestrictionLinear J s) p x

def NativePowerOrderedLifts (s p : ℕ) : Prop :=
  BasisCycleLifting.LinearLifts (K := K)
    (X := Set.powersetCard V p →₀ ↥(J^s))
    (Y := Set.powersetCard V p.pred →₀ ↥(J^s))
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred) (Γ := m.syn)
    (nativePowerCoefficientBasis m J G hG hu s p)
    (nativePowerCoefficientBasis m J G hG hu s p.pred)
    (fun a : PowerIdealIndex m J s p => m.toSyn (a.2.val + faceExponent a.1.val))
    (fun a : PowerIdealIndex m J s p.pred => m.toSyn (a.2.val + faceExponent a.1.val))
    (actualIdealPreviousDifferential (J^s) p)

section
attribute [local irreducible] nativePowerCoefficientBasis powerIdealCoefficientBasis
  powerIdealCoordinateEquiv actualIdealPreviousDifferential powerPreviousDifferential

set_option diagnostics true in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- Exact equivalence, including every filtration index and every cycle. -/
theorem nativePowerOrderedLifts_iff (s p : ℕ) :
    NativePowerOrderedLifts m J G hG hu s p ↔ PowerOrderedCoordinateLifts m J G hG hu s p := by
  unfold NativePowerOrderedLifts PowerOrderedCoordinateLifts
  apply BasisCycleLifting.linearLifts_iff_of_equiv
    (e := powerIdealCoordinateEquiv J s p)
    (f := powerIdealCoordinateEquiv J s p.pred)
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p.pred
  · exact powerIdealCoordinateEquiv_differential J s p

end

end FourPapers.Sublattice

end
end
end


end
