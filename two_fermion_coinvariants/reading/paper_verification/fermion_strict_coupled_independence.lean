module

public import PaperVerification.FermionStrictPolynomialBoxes
public import PaperVerification.FermionPairedCoupledIndependence

/-!
# Independence of every coupled strict monomial

The ordinary regular sequence is the constant-one paired extension.  The
creator highest-form calculation uses both parameter prefactors.  These
are distinct roles: no nonexistent zeroth ordinary moment is introduced.
The proved filtered syzygy reduction lifts the exact strict Newton diagonal,
and the actual strict harmonic tests separate all proposed classes.

-/

@[expose] public section
set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton Filtered
open scoped BigOperators TensorProduct

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictCoupledIndependence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- Data used only for the creator highest-form calculation: both creator
prefactors are phi. The ordinary strict ideal remains the s=1 extension. -/
def StrictData.creatorData (d : StrictData (K := R) (n := n)) :
    PairedData (K := R) (n := n) where
  positive_n := d.positive_n
  s := 2
  positive_s := by decide
  r := d.r
  u := d.r
  v := d.r
  positive_r := d.positive_r
  degree_split := fun _ ↦ by omega
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := d.phi
  a := d.phi
  b := d.phi
  highest_phi := d.highest_phi
  highest_a := d.highest_phi
  highest_b := d.highest_phi

def strictCoupledClasses (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) :
    StrictQuotient d.beta d.phi :=
  (strictIdeal d.beta d.phi).ringCon.mkₐ R
    (monomial z.2.val.val 1 ⊗ₜ[R] (Pi.basisFun R (OddIndex n)).ExteriorAlgebra z.1)

end PaperVerification.Fermion

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton Filtered
open scoped BigOperators TensorProduct

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionStrictCoupledIndependence_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem strictOrdinary_quotient_all_moments (d : StrictData (K := F) (n := n)) :
    ∀ k,moment (fun i ↦ Ideal.Quotient.mk (coupledOrdinaryIdeal d.pairedExtension) (d.phi i))
      (fun i ↦ algebraMap F (PolynomialRing F n ⧸ coupledOrdinaryIdeal d.pairedExtension)
        (d.beta i)*Ideal.Quotient.mk (coupledOrdinaryIdeal d.pairedExtension) (d.phi i)) k=0 := by
  intro k
  let q := Ideal.Quotient.mk (coupledOrdinaryIdeal d.pairedExtension)
  have h := coupledOrdinary_quotient_all_moments d.pairedExtension k
  change moment (fun i ↦ q (d.phi i))
    (fun i ↦ algebraMap F (PolynomialRing F n ⧸ coupledOrdinaryIdeal d.pairedExtension)
      (d.beta i) * q (d.phi i) * q (1 : PolynomialRing F n)) k = 0 at h
  simpa only [map_one, mul_one] using h

set_option maxHeartbeats 4000000 in
theorem strict_coupled_creator_diagonal_independent
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) (hT : ValidWord T) :
    LinearIndependent F (fun a : RectangleIndex (strictWordBoxBounds d.r T) ↦
      Ideal.Quotient.mk (coupledOrdinaryIdeal d.pairedExtension)
        (monomial a.val 1*creatorWordPolynomial d.creatorData T)) := by
  classical
  let f (i : Fin n) := coupledOrdinaryMoment d.pairedExtension i
  let g (i : Fin n) := powerMoment d.r d.beta 1 i
  let degree (i : Fin n) := (∏ j,d.r j)*(1+i.val)
  have htop (i : Fin n) : HasTop (coveringWeight d.r) (degree i) (f i) (g i) :=
    coupledOrdinaryMoment_hasTop d.pairedExtension i
  have h₀ : LinearIndependent F
      (fun a : RectangleIndex (strictWordBoxBounds d.r T) ↦
        Ideal.Quotient.mk (powerMomentIdeal d.r d.beta 1)
          (monomial a.val 1*powerCreatorWordPolynomial d.creatorData T)) := by
    have h := strict_creator_diagonal_independent d.r d.beta d.positive_r d.allowed_weights.2 T hT
    convert h using 1
    funext a
    change (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta 1))
      (monomial a.val 1 * powerCreatorWordPolynomial d.creatorData T) =
        (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta 1)) (monomial a.val 1) * _
    rw [map_mul, powerCreatorWordPolynomial, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact creatorDiagonal_map (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta 1))
      (fun i ↦ X i ^ d.r i) (fun i ↦ X i ^ d.r i) (fun i ↦ X i ^ d.r i) d.beta j
  exact polynomial_multiplier_independent_lifts
    (R := F) (ι := Fin n) (m := n)
    (E := RectangleIndex (strictWordBoxBounds d.r T))
    (coveringWeight d.r) f g degree
    (fun i ↦ (htop i).1) (fun i ↦ (htop i).2)
    (powerMoments_isWeaklyRegular d.r d.beta 1 d.positive_r Nat.zero_lt_one d.allowed_weights.2)
    (fun a ↦ monomial a.val 1) (fun a ↦ Finsupp.weight (coveringWeight d.r) a.val)
    (fun a ↦ isWeightedHomogeneous_monomial _ _ _ rfl)
    (creatorWordPolynomial d.creatorData T) (powerCreatorWordPolynomial d.creatorData T)
    (∑ j ∈ T,creatorDiagonalDegree d.creatorData j)
    (creatorWordPolynomial_hasTop d.creatorData T).1
    (creatorWordPolynomial_hasTop d.creatorData T).2 h₀

/-- Every literal strict class is independent for unrestricted coupled
lower terms. The field upper bound is proved separately by the actual split. -/
theorem strictCoupledClasses_linearIndependent (d : StrictData (K := F) (n := n)) :
    LinearIndependent F (strictCoupledClasses d) := by
  classical
  let q := Ideal.Quotient.mkₐ F (coupledOrdinaryIdeal d.pairedExtension)
  apply strict_independent_of_ordinary_diagonal q d.beta d.phi
    (strictOrdinary_quotient_all_moments d)
    (StrictWordPolynomialIndex d.r) (fun T a ↦ monomial a.val.val 1)
  intro T
  by_cases hT : ValidWord T
  · have h := (strict_coupled_creator_diagonal_independent d T hT).comp
      (fun a : StrictWordPolynomialIndex d.r T ↦ a.val) Subtype.val_injective
    convert h using 1
    funext a
    change q (monomial a.val.val 1) * _ =
      q (monomial a.val.val 1 * creatorWordPolynomial d.creatorData T)
    rw [map_mul, creatorWordPolynomial, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact (creatorDiagonal_map q d.phi d.phi d.phi d.beta j).symm
  · haveI : IsEmpty (StrictWordPolynomialIndex d.r T) := ⟨fun a ↦ hT a.property⟩
    exact linearIndependent_empty_type

end PaperVerification.Fermion
