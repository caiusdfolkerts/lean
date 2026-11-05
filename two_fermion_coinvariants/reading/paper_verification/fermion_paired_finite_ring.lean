module

public import PaperVerification.FermionFilteredFinite
public import PaperVerification.FermionPairedQuotientBaseChange
public import PaperVerification.FermionSeparatedFinite

/-!
# Finiteness of every coupled paired quotient over its original base ring

The homogeneous quotient is finite by the proved separated-cover criterion.
The actual highest forms of every two-sided relation then lift a finite
homogeneous spanning family.  This supplies the module finiteness needed by
closed-point descent; it is not assumed from fiber dimensions.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedFiniteRing_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem pairedPowerData_quotient_finite (d : PairedData (K := R) (n := n)) :
    Module.Finite R (PairedQuotient d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) := by
  have hm (e : ℕ) : MonicAtDegree (Polynomial.X^e : Polynomial R) e :=
    ⟨Polynomial.natDegree_X_pow_le e,Polynomial.coeff_X_pow_self e⟩
  have hab (i : Fin n) :
      (X i^d.u i : PolynomialRing R n) * X i^d.v i =
        Polynomial.aeval (Polynomial.aeval (X i : PolynomialRing R n) (Polynomial.X^d.r i : Polynomial R))
          (Polynomial.X^d.s : Polynomial R) := by
    simpa only [map_pow,Polynomial.aeval_X,pow_mul,← pow_add] using
      congrArg (fun e ↦ (X i : PolynomialRing R n)^e) (d.degree_split i)
  have h := (paired_separated_finite_iff_over_any_ring d.beta
    (Polynomial.X^d.s) (fun i ↦ Polynomial.X^d.r i)
    (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i) d.s d.r
    d.positive_s d.positive_r (hm d.s) (fun i ↦ hm (d.r i)) hab).mpr
      d.allowed_weights.2
  have hφ : (fun i : Fin n => Polynomial.aeval (X i : PolynomialRing R n)
      (Polynomial.X ^ d.r i : Polynomial R)) = (fun i => (X i : PolynomialRing R n) ^ d.r i) := by
    funext i
    exact Polynomial.aeval_X_pow (x := (X i : PolynomialRing R n))
  exact Eq.mp (congrArg (fun φ : Fin n → PolynomialRing R n =>
    Module.Finite R (PairedQuotient d.beta φ (fun i => X i ^ d.u i) (fun i => X i ^ d.v i))) hφ) h

/-- Finiteness of the literal coupled quotient over every commutative ring,
including rings with nilpotents and the zero ring. -/
theorem pairedCoupled_quotient_finite (d : PairedData (K := R) (n := n)) :
    Module.Finite R (PairedQuotient d.beta d.phi d.a d.b) := by
  letI := pairedPowerData_quotient_finite d
  let b := superMonomialBasis (K := R) (n := n)
  let q := ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
  let q₀ := ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
    (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap
  have hker₀ : q₀.ker = Submodule.span R (Set.range
      (basisRelationMultiple b (pairedPowerFiniteRelation d))) := by
    rw [show q₀.ker = twoSidedIdealSubmodule (pairedIdeal d.beta
        (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) from
      quotient_kernel_eq_twoSidedIdealSubmodule _]
    rw [← pairedPowerFiniteRelation_ideal d,twoSidedIdealSubmodule_span b]
  exact finite_of_filtered_relation_spans b
    (superMonomialWeight (coveringWeight d.r) (pairedOddWeight d))
    (basisRelationMultiple b (pairedFiniteRelation d))
    (basisRelationMultiple b (pairedPowerFiniteRelation d))
    (pairedRelationMultipleDegree d) (pairedRelationMultiple_hasTop d)
    q q₀ ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := R))
    ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ_surjective (α := R))
    (paired_quotient_kernel_eq_relationSpan R d) hker₀

end PaperVerification.Fermion
