module

public import PaperVerification.FermionHighestForms
public import PaperVerification.FermionPairedPowerBasis

/-!
# Creator independence for every coupled lower-weight perturbation

The ordinary moment ideal is the literal ideal of the coupled data. Its
highest forms are the regular power moments. The proved syzygy reduction
therefore transports every Newton diagonal block to this ordinary quotient.
The actual creator test maps then separate every proposed super-monomial.
-/

@[expose] public section

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior Endpoint Newton Filtered
open scoped BigOperators TensorProduct

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionPairedCoupledIndependence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem coupledOrdinary_quotient_all_moments (d : PairedData (K := F) (n := n)) :
    ∀ j, moment
      (fun i ↦ Ideal.Quotient.mk (coupledOrdinaryIdeal d) (d.phi i))
      (fun i ↦ algebraMap F (PolynomialRing F n ⧸ coupledOrdinaryIdeal d) (d.beta i) *
        Ideal.Quotient.mk (coupledOrdinaryIdeal d) (d.a i) *
        Ideal.Quotient.mk (coupledOrdinaryIdeal d) (d.b i)) j = 0 := by
  intro j
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (coupledOrdinaryMoment_mem d j)
  rw [coupledOrdinaryMoment,scalar_moment_map] at hz
  simpa only [map_mul,← MvPolynomial.algebraMap_eq,Ideal.Quotient.mk_algebraMap] using hz

set_option maxHeartbeats 4000000 in
/-- The polynomial part of each coupled creator diagonal is independent in
the actual coupled ordinary quotient. -/
theorem coupled_creator_diagonal_independent
    (d : PairedData (K := F) (n := n)) (T : Finset (OddIndex n)) (hT : ValidWord T) :
    LinearIndependent F
      (fun a : RectangleIndex (wordBoxBounds d.r d.u d.v d.s T) ↦
        Ideal.Quotient.mk (coupledOrdinaryIdeal d)
          (monomial a.val 1 * creatorWordPolynomial d T)) := by
  classical
  let f (i : Fin n) := coupledOrdinaryMoment d i
  let g (i : Fin n) := powerMoment d.r d.beta d.s i
  let degree (i : Fin n) := (∏ j, d.r j) * (d.s + i.val)
  have htop (i : Fin n) : HasTop (coveringWeight d.r) (degree i) (f i) (g i) :=
    coupledOrdinaryMoment_hasTop d i
  have h₀ : LinearIndependent F
      (fun a : RectangleIndex (wordBoxBounds d.r d.u d.v d.s T) ↦
        Ideal.Quotient.mk (powerMomentIdeal d.r d.beta d.s)
          (monomial a.val 1 * powerCreatorWordPolynomial d T)) := by
    have h := paired_creator_diagonal_independent d.r d.u d.v d.beta d.s
      d.positive_s d.positive_r d.degree_split d.allowed_weights.2 T hT
    convert h using 1
    funext a
    change (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta d.s))
      (monomial a.val 1 * powerCreatorWordPolynomial d T) =
        (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta d.s)) (monomial a.val 1) * _
    rw [map_mul, powerCreatorWordPolynomial, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact creatorDiagonal_map (Ideal.Quotient.mkₐ F (powerMomentIdeal d.r d.beta d.s))
      (fun i ↦ X i ^ d.r i) (fun i ↦ X i ^ d.u i) (fun i ↦ X i ^ d.v i) d.beta j
  exact polynomial_multiplier_independent_lifts
    (R := F) (ι := Fin n) (m := n)
    (E := RectangleIndex (wordBoxBounds d.r d.u d.v d.s T))
    (coveringWeight d.r) f g degree
    (fun i ↦ (htop i).1) (fun i ↦ (htop i).2)
    (powerMoments_isWeaklyRegular d.r d.beta d.s d.positive_r d.positive_s d.allowed_weights.2)
    (fun a ↦ monomial a.val 1) (fun a ↦ Finsupp.weight (coveringWeight d.r) a.val)
    (fun a ↦ isWeightedHomogeneous_monomial _ _ _ rfl)
    (creatorWordPolynomial d T) (powerCreatorWordPolynomial d T)
    (∑ j ∈ T, creatorDiagonalDegree d j)
    (creatorWordPolynomial_hasTop d T).1 (creatorWordPolynomial_hasTop d T).2 h₀

/-- The proposed coupled monomial classes in theta-then-xi exterior order. -/
def pairedCoupledClasses {R : Type*} [CommRing R] (d : PairedData (K := R) (n := n))
    (z : PairedPowerIndex d.r d.u d.v d.s) :
    PairedQuotient d.beta d.phi d.a d.b :=
  (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R
    (monomial z.2.val.val 1 ⊗ₜ[R] (Pi.basisFun R (OddIndex n)).ExteriorAlgebra z.1)

/-- All claimed classes are independent for the full coupled field data.
This theorem proves the lower bound without assuming a deformed colength,
flatness, or an unproved comparison of initial ideals. -/
theorem pairedCoupledClasses_linearIndependent
    (d : PairedData (K := F) (n := n)) :
    LinearIndependent F (pairedCoupledClasses d) := by
  classical
  let q := Ideal.Quotient.mkₐ F (coupledOrdinaryIdeal d)
  apply paired_independent_of_ordinary_diagonal q d.beta d.phi d.a d.b
    (coupledOrdinary_quotient_all_moments d)
    (PairedWordPolynomialIndex d.r d.u d.v d.s) (fun T a ↦ monomial a.val.val 1)
  intro T
  by_cases hT : ValidWord T
  · have h := (coupled_creator_diagonal_independent d T hT).comp
      (fun a : PairedWordPolynomialIndex d.r d.u d.v d.s T ↦ a.val)
      Subtype.val_injective
    convert h using 1
    funext a
    change q (monomial a.val.val 1) * _ =
      q (monomial a.val.val 1 * creatorWordPolynomial d T)
    rw [map_mul, creatorWordPolynomial, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact (creatorDiagonal_map q d.phi d.a d.b d.beta j).symm
  · haveI : IsEmpty (PairedWordPolynomialIndex d.r d.u d.v d.s T) :=
      ⟨fun a ↦ hT a.property⟩
    exact linearIndependent_empty_type

end PaperVerification.Fermion
