module

public import PaperVerification.FermionStrictCoupledIndependence
public import PaperVerification.FermionPairedQuotientBaseChange

/-!
# Scalar extension of the literal strict two-sided quotient

Every original strict generator and every left/right basis multiple is
transported through the actual polynomial/exterior coefficient map. The
resulting relation-span equality constructs the quotient comparison by
right exactness, without a flatness hypothesis on the coefficient map.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped TensorProduct

section Data

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

def StrictData.map (d : StrictData (K := R) (n := n)) (f : R →+* S) :
    StrictData (K := S) (n := n) where
  positive_n := d.positive_n
  r := d.r
  positive_r := d.positive_r
  beta := f ∘ d.beta
  allowed_weights := by
    constructor
    · simpa only [map_natCast] using d.allowed_weights.1.map f
    · intro U hU
      simpa only [Function.comp_def,map_sum] using (d.allowed_weights.2 U hU).map f
  phi := fun i ↦ MvPolynomial.map f (d.phi i)
  highest_phi := fun i ↦ HasHighestPower.map f d.r (d.phi i) i (d.r i) (d.highest_phi i)

def strictFiniteRelation (d : StrictData (K := R) (n := n)) (j : MomentKind × Fin n) :
    SuperRing R n := moment d.phi (strictCoefficients d.beta d.phi j.1) j.2

theorem strictFiniteRelation_ideal (d : StrictData (K := R) (n := n)) :
    TwoSidedIdeal.span (Set.range (strictFiniteRelation d))=strictIdeal d.beta d.phi :=
  (strictIdeal_finite d.beta d.phi).symm

end Data

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

local instance FermionStrictBaseChange_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem superCoefficientMap_strictCoefficients (β : Fin n → R)
    (φ : Fin n → PolynomialRing R n) (kind : MomentKind) (i : Fin n) :
    superCoefficientMap R S (strictCoefficients β φ kind i)=
      strictCoefficients (algebraMap R S ∘ β)
        (fun j ↦ MvPolynomial.map (algebraMap R S) (φ j)) kind i := by
  cases kind <;>
    simp only [strictCoefficients,superCoefficientMap_polynomial_smul,
      superCoefficientMap_theta,superCoefficientMap_xi,map_mul,map_one,
      MvPolynomial.map_C,Function.comp_def]

theorem superCoefficientMap_strictFiniteRelation (d : StrictData (K := R) (n := n))
    (j : MomentKind × Fin n) :
    superCoefficientMap R S (strictFiniteRelation d j)=
      strictFiniteRelation (d.map (algebraMap R S)) j := by
  rw [strictFiniteRelation,superCoefficientMap_moment]
  simp only [superCoefficientMap_strictCoefficients]
  rfl

theorem superBaseChangeEquiv_strictRelationMultiple (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    superBaseChangeEquiv R S
      ((1 : S) ⊗ₜ[R] basisRelationMultiple (superMonomialBasis (K := R))
        (strictFiniteRelation d) z)=
      basisRelationMultiple (superMonomialBasis (K := S))
        (strictFiniteRelation (d.map (algebraMap R S))) z := by
  rw [superBaseChangeEquiv_tmul,one_smul]
  simp only [basisRelationMultiple,map_mul,superCoefficientMap_basis,
    superCoefficientMap_strictFiniteRelation]

theorem strict_quotient_kernel_eq_relationSpan (d : StrictData (K := R) (n := n)) :
    (((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap).ker=
      Submodule.span R (Set.range
        (basisRelationMultiple (superMonomialBasis (K := R)) (strictFiniteRelation d))) := by
  rw [quotient_kernel_eq_twoSidedIdealSubmodule,←strictFiniteRelation_ideal d,
    twoSidedIdealSubmodule_span]

def strictQuotientBaseChangeEquiv (d : StrictData (K := R) (n := n)) :
    S ⊗[R] StrictQuotient d.beta d.phi ≃ₗ[S]
      StrictQuotient (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi :=
  quotientBaseChangeEquivOfSpans (superBaseChangeEquiv R S)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
    ((strictIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi).ringCon.mkₐ S).toLinearMap
    (by
      intro y
      obtain ⟨x,hx⟩ := (strictIdeal d.beta d.phi).ringCon.mkₐ_surjective (α := R) y
      exact ⟨x,hx⟩)
    (by
      intro y
      obtain ⟨x,hx⟩ := (strictIdeal (d.map (algebraMap R S)).beta
        (d.map (algebraMap R S)).phi).ringCon.mkₐ_surjective (α := S) y
      exact ⟨x,hx⟩)
    (basisRelationMultiple (superMonomialBasis (K := R)) (strictFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := S)) (strictFiniteRelation (d.map (algebraMap R S))))
    (strict_quotient_kernel_eq_relationSpan R d)
    (strict_quotient_kernel_eq_relationSpan S (d.map (algebraMap R S)))
    (superBaseChangeEquiv_strictRelationMultiple R S d)

@[simp] theorem strictQuotientBaseChangeEquiv_tmul_class
    (d : StrictData (K := R) (n := n)) (s : S) (x : SuperRing R n) :
    strictQuotientBaseChangeEquiv R S d
      (s ⊗ₜ[R] (strictIdeal d.beta d.phi).ringCon.mkₐ R x)=
        s • (strictIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi).ringCon.mkₐ S
          (superCoefficientMap R S x) := by
  have h := quotientBaseChangeEquivOfSpans_tmul (superBaseChangeEquiv R S)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
    ((strictIdeal (d.map (algebraMap R S)).beta (d.map (algebraMap R S)).phi).ringCon.mkₐ S).toLinearMap
    (by
      intro y
      obtain ⟨x,hx⟩ := (strictIdeal d.beta d.phi).ringCon.mkₐ_surjective (α := R) y
      exact ⟨x,hx⟩)
    (by
      intro y
      obtain ⟨x,hx⟩ := (strictIdeal (d.map (algebraMap R S)).beta
        (d.map (algebraMap R S)).phi).ringCon.mkₐ_surjective (α := S) y
      exact ⟨x,hx⟩)
    (basisRelationMultiple (superMonomialBasis (K := R)) (strictFiniteRelation d))
    (basisRelationMultiple (superMonomialBasis (K := S)) (strictFiniteRelation (d.map (algebraMap R S))))
    (strict_quotient_kernel_eq_relationSpan R d)
    (strict_quotient_kernel_eq_relationSpan S (d.map (algebraMap R S)))
    (superBaseChangeEquiv_strictRelationMultiple R S d) s x
  rw [superBaseChangeEquiv_tmul,map_smul] at h
  exact h

@[simp] theorem strictQuotientBaseChangeEquiv_class
    (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) :
    strictQuotientBaseChangeEquiv R S d ((1 : S) ⊗ₜ[R] strictCoupledClasses d z)=
      strictCoupledClasses (d.map (algebraMap R S)) z := by
  rw [strictCoupledClasses,strictQuotientBaseChangeEquiv_tmul_class,one_smul]
  rw [superCoefficientMap_tmul,MvPolynomial.map_monomial,map_one,exteriorCoefficientMap_basis]
  rfl

end PaperVerification.Fermion
