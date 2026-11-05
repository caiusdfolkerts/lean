module

public import PaperVerification.FermionQuotientDegreeBasis
public import PaperVerification.FermionPairedRank

/-!
# The actual exterior-degree spaces and their prescribed bases

Degree is the number of odd generators in the actual ambient exterior basis.
Every two-sided multiple of each moment is homogeneous for this degree, so
the actual quotient inherits its degree spaces.  These are proved equal to
the spans of exactly the corresponding paper basis vectors.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionPairedExteriorPieces_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective

def momentExteriorDegree : MomentKind → ℕ
  | .polynomial => 0
  | .theta => 1
  | .xi => 1
  | .mixed => 2

@[simp] theorem pairedMomentWord_card (kind : MomentKind) (i : Fin n) :
    (pairedMomentWord kind i).card=momentExteriorDegree kind := by
  cases kind <;> simp [pairedMomentWord,momentExteriorDegree]

@[simp] theorem superMonomialWeight_zero_one (z : SuperMonomialIndex n) :
    superMonomialWeight (fun _ ↦ 0) (fun _ ↦ 1) z=z.2.card := by
  simp [superMonomialWeight,wordPolynomialWeight,Finsupp.weight_eq_sum]

theorem polynomial_hasTop_zero_weight (p : PolynomialRing R n) :
    Filtered.HasTop (fun _ ↦ 0) 0 p p := by
  apply Filtered.HasTop.of_homogeneous
  intro a ha
  simp [Finsupp.weight_eq_sum]

def pairedRelationMultipleExteriorDegree
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) : ℕ :=
  z.1.2.card+momentExteriorDegree z.2.1.1+z.2.2.2.card

theorem pairedRelationMultiple_exterior_homogeneous
    (d : PairedData (K := R) (n := n))
    (z : SuperMonomialIndex n × (MomentKind × Fin n) × SuperMonomialIndex n) :
    BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
      (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z) := by
  have ht : BasisFiltered.HasTop (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
      (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z)
      (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z) := by
    unfold basisRelationMultiple pairedFiniteRelation
    rw [pairedMoment_eq_tensor_sum]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply BasisFiltered.HasTop.sum _ _ Finset.univ _ _ _
    intro i hi
    have h := hasTop_basis_multiples (fun _ : Fin n ↦ 0) (fun _ : OddIndex n ↦ 1)
      (d.phi i^z.2.1.2.val*pairedPolynomialCoefficient d.beta d.a d.b z.2.1.1 i)
      _ 0 (polynomial_hasTop_zero_weight _) (pairedMomentWord z.2.1.1 i) z.1 z.2.2
    have hw : superMonomialWeight (fun _ : Fin n ↦ 0) (fun _ : OddIndex n ↦ 1) =
        fun q : SuperMonomialIndex n ↦ q.2.card := funext superMonomialWeight_zero_one
    rw [hw] at h
    simpa only [superMonomialWeight_zero_one,wordPolynomialWeight,Finset.sum_const,
      nsmul_eq_mul,Nat.cast_id,mul_one,pairedMomentWord_card,zero_add,
      pairedRelationMultipleExteriorDegree] using h
  have hh := BasisFiltered.homogeneous_component (superMonomialBasis (K := R))
    (fun i ↦ i.2.card) (pairedRelationMultipleExteriorDegree z)
      (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d) z)
  rwa [ht.2] at hh

theorem paired_kernel_exterior_component (d : PairedData (K := R) (n := n))
    (j : ℕ) (x : SuperRing R n)
    (hx : x ∈ (((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap).ker) :
    BasisFiltered.component (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j x ∈
      (((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap).ker := by
  rw [paired_quotient_kernel_eq_relationSpan] at hx ⊢
  exact BasisFiltered.component_mem_span (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    (basisRelationMultiple superMonomialBasis (pairedFiniteRelation d))
    pairedRelationMultipleExteriorDegree (pairedRelationMultiple_exterior_homogeneous d) x hx j

/-- The degree space is the image of the original homogeneous ambient
space, independently of the proposed basis. -/
def pairedExteriorPiece (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Submodule R (PairedQuotient d.beta d.phi d.a d.b) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j).map
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap

abbrev PairedExteriorIndex (d : PairedData (K := R) (n := n)) (j : ℕ) :=
  {z : PairedPowerIndex d.r d.u d.v d.s // z.1.card=j}

def pairedExteriorPieceBasis (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Module.Basis (PairedExteriorIndex d j) R (pairedExteriorPiece d j) :=
  BasisFiltered.quotientPieceBasis (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
    (pairedArbitraryRingBasis d)
    (fun z : PairedPowerIndex d.r d.u d.v d.s ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ z.1.card)
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    (fun z ↦ by rw [pairedArbitraryRingBasis_apply,superMonomialBasis_apply]; rfl)
    (paired_kernel_exterior_component d) j

@[simp] theorem pairedExteriorPieceBasis_coe (d : PairedData (K := R) (n := n))
    (j : ℕ) (z : PairedExteriorIndex d j) :
    (pairedExteriorPieceBasis d j z : PairedQuotient d.beta d.phi d.a d.b)=
      pairedCoupledClasses d z.val := by
  have h : (pairedExteriorPieceBasis d j z : PairedQuotient d.beta d.phi d.a d.b) =
      pairedArbitraryRingBasis d z.val := BasisFiltered.quotientPieceBasis_coe
    (R := R) (Q := PairedQuotient d.beta d.phi d.a d.b)
    (E := PairedPowerIndex d.r d.u d.v d.s)
    (superMonomialBasis (K := R)) (fun i ↦ i.2.card)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
    (pairedArbitraryRingBasis d)
    (fun z : PairedPowerIndex d.r d.u d.v d.s ↦ superMonomialBasis (z.2.val.val,z.1))
    (fun z ↦ z.1.card)
    (fun z ↦ BasisFiltered.homogeneous_basis _ _ (z.2.val.val,z.1))
    (fun z ↦ by rw [pairedArbitraryRingBasis_apply,superMonomialBasis_apply]; rfl)
    (paired_kernel_exterior_component d) j z
  exact h.trans (pairedArbitraryRingBasis_apply d z.val)

theorem pairedExteriorPiece_finite_free (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Module.Finite R (pairedExteriorPiece d j) ∧ Module.Free R (pairedExteriorPiece d j) :=
  ⟨Module.Finite.of_basis (pairedExteriorPieceBasis d j),
    Module.Free.of_basis (pairedExteriorPieceBasis d j)⟩

theorem pairedExteriorPiece_finrank [Nontrivial R]
    (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Module.finrank R (pairedExteriorPiece d j)=Fintype.card (PairedExteriorIndex d j) :=
  Module.finrank_eq_card_basis (pairedExteriorPieceBasis d j)

def pairedExteriorIndexEquiv (d : PairedData (K := R) (n := n)) (j : ℕ) :
    PairedExteriorIndex d j ≃
      Σ W : {W : Finset (OddIndex n) // W.card=j},
        PairedWordPolynomialIndex d.r d.u d.v d.s W.val where
  toFun z := ⟨⟨z.val.1,z.property⟩,z.val.2⟩
  invFun z := ⟨⟨z.1.val,z.2⟩,z.1.property⟩
  left_inv z := rfl
  right_inv z := rfl

theorem card_pairedExteriorIndex_eq_coefficient (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Fintype.card (PairedExteriorIndex d j)=(pairedBasisExteriorPolynomial d).coeff j := by
  classical
  rw [Fintype.card_congr (pairedExteriorIndexEquiv d j),Fintype.card_sigma]
  simp only [card_pairedWordPolynomialIndex]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun W : Finset (OddIndex n) ↦ W.card=j))
    (by intro W; simp) (fun W ↦ pairedWordBoxCard d.r d.u d.v d.s W)]
  rw [Finset.sum_filter,pairedBasisExteriorPolynomial,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow,eq_comm]

/-- Every coefficient of the printed total-exterior polynomial is the
actual rank of the corresponding homogeneous quotient space. -/
theorem paired_exterior_hilbert_coefficient [Nontrivial R]
    (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Module.finrank R (pairedExteriorPiece d j) =
      (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j := by
  rw [pairedExteriorPiece_finrank,card_pairedExteriorIndex_eq_coefficient,
    pairedBasisExteriorPolynomial_closed]

/-- The same rank data are represented by explicit finite bases over every
commutative ring, including the zero ring. -/
theorem paired_exterior_basis_card (d : PairedData (K := R) (n := n)) (j : ℕ) :
    Fintype.card (PairedExteriorIndex d j) =
      (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j := by
  rw [card_pairedExteriorIndex_eq_coefficient,pairedBasisExteriorPolynomial_closed]

end PaperVerification.Fermion
