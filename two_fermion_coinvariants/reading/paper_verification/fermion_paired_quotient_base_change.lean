module

public import PaperVerification.FermionCoefficientChange
public import PaperVerification.FermionPresentationBaseChange
public import PaperVerification.FermionPairedCoupledBasis

/-!
# Scalar extension of the literal paired two-sided quotient

All four families, their finite recurrence presentation, and every left/right
ambient basis multiple are transported explicitly.  Their actual kernel spans
therefore supply the generic quotient comparison with no assumed fiber
identification.  The prescribed monomial classes are transported exactly.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

local instance FermionPairedQuotientBaseChange_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem superCoefficientMap_pairedFiniteRelation (d : PairedData (K := R) (n := n))
    (j : MomentKind × Fin n) :
    superCoefficientMap R S (pairedFiniteRelation d j) =
      pairedFiniteRelation (d.map (algebraMap R S)) j := by
  rw [pairedFiniteRelation,superCoefficientMap_moment]
  simp only [superCoefficientMap_pairedCoefficients]
  rfl

theorem superBaseChangeEquiv_pairedRelationMultiple (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    superBaseChangeEquiv R S
      ((1 : S) ⊗ₜ[R] basisRelationMultiple (superMonomialBasis (K := R))
        (pairedFiniteRelation d) z) =
      basisRelationMultiple (superMonomialBasis (K := S))
        (pairedFiniteRelation (d.map (algebraMap R S))) z := by
  rw [superBaseChangeEquiv_tmul,one_smul]
  simp only [basisRelationMultiple,map_mul,superCoefficientMap_basis,
    superCoefficientMap_pairedFiniteRelation]

theorem paired_quotient_kernel_eq_relationSpan (d : PairedData (K := R) (n := n)) :
    (((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap).ker =
      Submodule.span R (Set.range
        (basisRelationMultiple (superMonomialBasis (K := R)) (pairedFiniteRelation d))) := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule,← pairedFiniteRelation_ideal d,
    twoSidedIdealSubmodule_span]

/-- The exact scalar-extension isomorphism for the original super quotient.
Its construction uses the actual finite moment ideal on both sides. -/
def pairedQuotientBaseChangeEquiv (d : PairedData (K := R) (n := n)) :
    S ⊗[R] PairedQuotient d.beta d.phi d.a d.b ≃ₗ[S]
      PairedQuotient (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
        (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b :=
  quotientBaseChangeEquivOfSpans (superBaseChangeEquiv R S)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
    ((pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
      (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ S).toLinearMap
    (by
      intro y
      obtain ⟨x,hx⟩ := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := R) y
      exact ⟨x,hx⟩)
    (by
      intro y
      obtain ⟨x,hx⟩ := (pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
        (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ_surjective (α := S) y
      exact ⟨x,hx⟩)
    (basisRelationMultiple (superMonomialBasis (K := R)) (pairedFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := S))
      (pairedFiniteRelation (d.map (algebraMap R S))))
    (paired_quotient_kernel_eq_relationSpan R d)
    (paired_quotient_kernel_eq_relationSpan S (d.map (algebraMap R S)))
    (superBaseChangeEquiv_pairedRelationMultiple R S d)

@[simp] theorem pairedQuotientBaseChangeEquiv_tmul_class
    (d : PairedData (K := R) (n := n)) (s : S) (x : SuperRing R n) :
    pairedQuotientBaseChangeEquiv R S d
      (s ⊗ₜ[R] (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R x) =
      s • (pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
        (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ S
          (superCoefficientMap R S x) := by
  have h := quotientBaseChangeEquivOfSpans_tmul (superBaseChangeEquiv R S)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
    ((pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
      (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ S).toLinearMap
    (by
      intro y
      obtain ⟨x,hx⟩ := (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ_surjective (α := R) y
      exact ⟨x,hx⟩)
    (by
      intro y
      obtain ⟨x,hx⟩ := (pairedIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi
        (d.map (algebraMap R S)).a (d.map (algebraMap R S)).b).ringCon.mkₐ_surjective (α := S) y
      exact ⟨x,hx⟩)
    (basisRelationMultiple (superMonomialBasis (K := R)) (pairedFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := S))
      (pairedFiniteRelation (d.map (algebraMap R S))))
    (paired_quotient_kernel_eq_relationSpan R d)
    (paired_quotient_kernel_eq_relationSpan S (d.map (algebraMap R S)))
    (superBaseChangeEquiv_pairedRelationMultiple R S d) s x
  rw [superBaseChangeEquiv_tmul,map_smul] at h
  exact h

@[simp] theorem pairedQuotientBaseChangeEquiv_class
    (d : PairedData (K := R) (n := n)) (z : PairedPowerIndex d.r d.u d.v d.s) :
    pairedQuotientBaseChangeEquiv R S d ((1 : S) ⊗ₜ[R] pairedCoupledClasses d z) =
      pairedCoupledClasses (d.map (algebraMap R S)) z := by
  rw [pairedCoupledClasses,pairedQuotientBaseChangeEquiv_tmul_class,one_smul]
  rw [superCoefficientMap_tmul,MvPolynomial.map_monomial,map_one,
    exteriorCoefficientMap_basis]
  rfl

end PaperVerification.Fermion
