module

public import PaperVerification.FermionStrictRank
public import PaperVerification.FermionStrictHighestForms

/-!
# Actual exterior-degree spaces of the strict quotient

The degree spaces are images of the original homogeneous exterior spaces.
Their finite free bases are the corresponding literal strict monomials;
the complete strict index enumeration determines every Hilbert coefficient.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionStrictExteriorPieces_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

theorem strictRelationMultiple_exterior_homogeneous (d : StrictData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
      (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z) := by
  have ht : BasisFiltered.HasTop (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
      (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z)
      (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z) := by
    unfold basisRelationMultiple strictFiniteRelation
    rw [strictMoment_eq_tensor_sum]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply BasisFiltered.HasTop.sum _ _ Finset.univ _ _ _
    intro i hi
    have h := hasTop_basis_multiples (fun _ : Fin n ↦ 0) (fun _ : OddIndex n ↦ 1)
      (d.phi i^z.2.1.2.val*strictPolynomialCoefficient d.beta d.phi z.2.1.1 i)
      _ 0 (polynomial_hasTop_zero_weight _) (pairedMomentWord z.2.1.1 i) z.1 z.2.2
    have hw : superMonomialWeight (fun _ : Fin n ↦ 0) (fun _ : OddIndex n ↦ 1)=
        fun q : SuperMonomialIndex n ↦ q.2.card := funext superMonomialWeight_zero_one
    rw [hw] at h
    simpa only [superMonomialWeight_zero_one,wordPolynomialWeight,Finset.sum_const,
      nsmul_eq_mul,Nat.cast_id,mul_one,pairedMomentWord_card,zero_add,pairedRelationMultipleExteriorDegree] using h
  have hh := BasisFiltered.homogeneous_component (superMonomialBasis (K := R))
    (fun i ↦ i.2.card) (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (strictFiniteRelation d) z)
  rwa [ht.2] at hh

theorem strict_kernel_exterior_component (d : StrictData (K := R) (n := n))
    (j : ℕ) (x : SuperRing R n)
    (hx : x ∈ (((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap).ker) :
    BasisFiltered.component (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j x ∈
      (((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap).ker := by
  rw [strict_quotient_kernel_eq_relationSpan] at hx ⊢
  exact BasisFiltered.component_mem_span (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    (basisRelationMultiple superMonomialBasis (strictFiniteRelation d))
    pairedRelationMultipleExteriorDegree (strictRelationMultiple_exterior_homogeneous d) x hx j

def strictExteriorPiece (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Submodule R (StrictQuotient d.beta d.phi) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j).map
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap

abbrev StrictExteriorIndex (d : StrictData (K := R) (n := n)) (j : ℕ) :=
  {z : StrictPowerIndex d.r // z.1.card=j}

def strictExteriorPieceBasis (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Module.Basis (StrictExteriorIndex d j) R (strictExteriorPiece d j) :=
  BasisFiltered.quotientPieceBasis (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
    (strictArbitraryRingBasis d)
    (fun z : StrictPowerIndex d.r ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ z.1.card)
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    (fun z ↦ by rw [strictArbitraryRingBasis_apply,superMonomialBasis_apply]; rfl)
    (strict_kernel_exterior_component d) j

@[simp] theorem strictExteriorPieceBasis_coe (d : StrictData (K := R) (n := n))
    (j : ℕ) (z : StrictExteriorIndex d j) :
    (strictExteriorPieceBasis d j z : StrictQuotient d.beta d.phi)=strictCoupledClasses d z.val := by
  have h : (strictExteriorPieceBasis d j z : StrictQuotient d.beta d.phi) =
      strictArbitraryRingBasis d z.val := BasisFiltered.quotientPieceBasis_coe
    (R := R) (Q := StrictQuotient d.beta d.phi)
    (E := StrictPowerIndex d.r)
    (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
    (strictArbitraryRingBasis d)
    (fun z : StrictPowerIndex d.r ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ z.1.card)
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    (fun z ↦ by rw [strictArbitraryRingBasis_apply,superMonomialBasis_apply]; rfl)
    (strict_kernel_exterior_component d) j z
  exact h.trans (strictArbitraryRingBasis_apply d z.val)

theorem card_strictExteriorIndex_eq_coefficient (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Fintype.card (StrictExteriorIndex d j)=(strictBasisExteriorPolynomial d.r).coeff j := by
  classical
  simp only [StrictExteriorIndex,Fintype.card_subtype,strictBasisExteriorPolynomial,
    Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,Finset.card_eq_sum_ones,
    Finset.sum_filter,eq_comm]

theorem strict_exterior_basis_card (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Fintype.card (StrictExteriorIndex d j)=
      (Polynomial.C ((∏ i,d.r i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  rw [card_strictExteriorIndex_eq_coefficient,strictBasisExteriorPolynomial_closed d.r d.positive_n]

theorem strictExteriorPiece_finite_free (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Module.Finite R (strictExteriorPiece d j) ∧ Module.Free R (strictExteriorPiece d j) :=
  ⟨Module.Finite.of_basis (strictExteriorPieceBasis d j),Module.Free.of_basis (strictExteriorPieceBasis d j)⟩

theorem strict_exterior_hilbert_coefficient [Nontrivial R]
    (d : StrictData (K := R) (n := n)) (j : ℕ) :
    Module.finrank R (strictExteriorPiece d j)=
      (Polynomial.C ((∏ i,d.r i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by
  rw [Module.finrank_eq_card_basis (strictExteriorPieceBasis d j),strict_exterior_basis_card]

end PaperVerification.Fermion
