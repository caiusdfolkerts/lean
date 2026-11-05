module

public import PaperVerification.AlternatingFormsOddStandardPieces
public import PaperVerification.AlternatingFormsLinearPresentation
public import PaperVerification.AlternatingFormsOddExteriorCutoff

/-!
# The complete good-monomial exterior basis for the canonical odd pencil

The index inequalities are written without truncated subtraction, so they
retain their meaning in every degree, including degrees above the middle.
Degrees zero and one use the proved absence of quadratic-generated relations;
the middle range uses the actual linear Plücker comparison and lifted standard
basis; all higher degrees use the actual generated-ideal cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

variable {K : Type*} [Field K]

/-- The printed good-index inequalities, in zero-based coordinates and with
the upper inequality moved across the subtraction. -/
def GoodOddIndex (k s : ℕ) :=
  {I : PluckerIndex s (2*k+1) // ∀ i,
    2*i.val≤(I.val i).val ∧ (I.val i).val+2*s≤2*k+2+2*i.val}

instance goodOddIndex_fintype (k s : ℕ) : Fintype (GoodOddIndex k s) := by
  classical
  unfold GoodOddIndex
  infer_instance

abbrev OddExteriorQuotientDegree (k s : ℕ) :=
  ExteriorQuotientDegree
    (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s

def goodOddBandEquiv (k t : ℕ) (hs : t+2≤k+1) :
    GoodOddIndex k (t+2) ≃
      BandChain (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs) 1 where
  toFun I := ⟨fun _ => I.val.val,fun _ => I.val.property,
    (by
      intro j i
      have hi := I.property i
      constructor
      · exact hi.1
      · change (I.val.val i).val≤2*(k+1-(t+2)+i.val)
        omega),monotone_const⟩
  invFun C := ⟨⟨C.val 0,C.property.1 0⟩,by
    intro i
    have hi := C.property.2.1 0 i
    constructor
    · exact hi.1
    · have hi2 := hi.2
      change (C.val 0 i).val≤2*(k+1-(t+2)+i.val) at hi2
      change (C.val 0 i).val+2*(t+2)≤2*k+2+2*i.val
      omega⟩
  left_inv I := rfl
  right_inv C := by
    apply Subtype.ext
    funext j i
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    rw [hj]

private theorem odd_pairCoefficientForms (k : ℕ) :
    pairCoefficientForms (oddPluckerForms (K := K) k 0) (oddPluckerForms k 1)=
      oddPluckerForms k := by
  funext i
  fin_cases i <;> rfl

def oddExteriorLinearClass (k t : ℕ) :
    (⋀[K]^(t+2) (Fin (2*k+1) → K)) →ₗ[K]
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) :=
  (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal (t := t) (oddPluckerForms k))).toLinearMap.comp
    (exteriorPluckerCoordinates (t+2) (2*k+1))

theorem oddExteriorLinearClass_ker (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).ker=exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) (t+2) := by
  apply Submodule.ext
  intro x
  change Ideal.Quotient.mk
    (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))
      (exteriorPluckerCoordinates (K := K) (t+2) (2*k+1) x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,← odd_pairCoefficientForms (K := K) k,
    exteriorCoordinates_mem_pairIdeal_iff,coefficientPairRelations_eq_exterior,
    oddPluckerForms_first,oddPluckerForms_second]

theorem oddExteriorLinearClass_range (k t : ℕ) :
    (oddExteriorLinearClass (K := K) k t).range=oddPluckerDegree k t 1 := by
  rw [oddExteriorLinearClass,LinearMap.range_comp,exteriorPluckerCoordinates_range]
  rfl

def oddExteriorLinearPieceEquiv (k t : ℕ) :
    OddExteriorQuotientDegree (K := K) k (t+2) ≃ₗ[K]
      oddPluckerDegree (K := K) k t 1 :=
  (Submodule.quotEquivOfEq _ _ (oddExteriorLinearClass_ker k t).symm).trans
    ((oddExteriorLinearClass k t).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ (oddExteriorLinearClass_range k t)))

theorem oddExteriorLinearPieceEquiv_mk (k t : ℕ)
    (x : ⋀[K]^(t+2) (Fin (2*k+1) → K)) :
    (oddExteriorLinearPieceEquiv k t (Submodule.Quotient.mk x) :
      MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k))=
      Ideal.Quotient.mk _ (exteriorPluckerCoordinates (t+2) (2*k+1) x) := by
  simp only [oddExteriorLinearPieceEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearEquiv.coe_ofEq_apply,
    LinearMap.quotKerEquivRange_apply_mk]
  rfl

def oddExteriorMiddleBasis [CharZero K] (k t : ℕ) (hs : t+2≤k+1) :
    Module.Basis (GoodOddIndex k (t+2)) K (OddExteriorQuotientDegree (K := K) k (t+2)) :=
  ((oddPluckerDegreeBasis k t hs 1).map (oddExteriorLinearPieceEquiv k t).symm).reindex
    (goodOddBandEquiv k t hs).symm

@[simp] theorem oddExteriorMiddleBasis_apply [CharZero K] (k t : ℕ) (hs : t+2≤k+1)
    (I : GoodOddIndex k (t+2)) :
    oddExteriorMiddleBasis (K := K) k t hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis (t+2) (2*k+1) I.val) := by
  apply (oddExteriorLinearPieceEquiv k t).injective
  apply Subtype.ext
  simp only [oddExteriorMiddleBasis,Module.Basis.reindex_apply,Equiv.symm_symm,
    Module.Basis.map_apply,LinearEquiv.apply_symm_apply,oddPluckerDegreeBasis_apply,
    oddExteriorLinearPieceEquiv_mk,exteriorPluckerCoordinates_basis,
    goodOddBandEquiv,chainPluckerProduct,Fin.prod_univ_one]
  rfl

def goodOddLowEquiv (k s : ℕ) (hs : s<2) : GoodOddIndex k s ≃ PluckerIndex s (2*k+1) where
  toFun I := I.val
  invFun I := ⟨I,by
    intro i
    have hi := i.isLt
    have hI := (I.val i).isLt
    constructor <;> omega⟩
  left_inv I := rfl
  right_inv I := rfl

def oddExteriorLowBasis (k s : ℕ) (hs : s<2) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) :=
  ((exteriorPluckerBasis s (2*k+1)).reindex (goodOddLowEquiv k s hs).symm).map
    ((exteriorDegreeRelations
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) s).quotEquivOfEqBot (exteriorDegreeRelations_eq_bot _ _ hs)).symm

@[simp] theorem oddExteriorLowBasis_apply (k s : ℕ) (hs : s<2) (I : GoodOddIndex k s) :
    oddExteriorLowBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  simp only [oddExteriorLowBasis,Module.Basis.map_apply,Module.Basis.reindex_apply,
    Equiv.symm_symm,goodOddLowEquiv,Submodule.quotEquivOfEqBot_symm_apply]
  rfl

theorem goodOddIndex_isEmpty (k s : ℕ) (hs : k+1<s) : IsEmpty (GoodOddIndex k s) := by
  refine ⟨fun I => ?_⟩
  have hpos : 0<s := by omega
  have h := (I.property (⟨0,hpos⟩ : Fin s)).2
  change (I.val.val ⟨0,hpos⟩).val+2*s≤2*k+2+2*0 at h
  omega

def oddExteriorHighBasis [CharZero K] (k s : ℕ) (hs : k+1<s) :
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s) := by
  letI := goodOddIndex_isEmpty k s hs
  letI := odd_exteriorQuotientDegree_subsingleton
    (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*k+1)))) hs
  exact Module.Basis.empty _

@[simp] theorem oddExteriorHighBasis_apply [CharZero K] (k s : ℕ) (hs : k+1<s) (I : GoodOddIndex k s) :
    oddExteriorHighBasis (K := K) k s hs I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  exact (goodOddIndex_isEmpty k s hs).false I |>.elim

/-- The basis covers every degree and every odd ambient dimension. -/
def oddExteriorBasis [CharZero K] (k : ℕ) : (s : ℕ) →
    Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s)
  | 0 => oddExteriorLowBasis k 0 (by decide)
  | 1 => oddExteriorLowBasis k 1 (by decide)
  | t+2 => if hs : t+2≤k+1 then oddExteriorMiddleBasis k t hs
      else oddExteriorHighBasis k (t+2) (Nat.lt_of_not_ge hs)

@[simp] theorem oddExteriorBasis_apply [CharZero K] (k s : ℕ) (I : GoodOddIndex k s) :
    oddExteriorBasis (K := K) k s I=
      Submodule.Quotient.mk (exteriorPluckerBasis s (2*k+1) I.val) := by
  cases s with
  | zero => exact oddExteriorLowBasis_apply k 0 (by decide) I
  | succ s =>
      cases s with
      | zero => exact oddExteriorLowBasis_apply k 1 (by decide) I
      | succ t =>
          dsimp only [oddExteriorBasis]
          split_ifs with hs
          · exact oddExteriorMiddleBasis_apply k t hs I
          · exact oddExteriorHighBasis_apply k (t+2) (Nat.lt_of_not_ge hs) I

/-- The complete exterior-basis clause of Theorem 1.3, faithfully stated
using the actual generated-ideal quotient and the original exterior words.
The separate degeneration and Koszul clauses are not part of this statement. -/
theorem paper_theorem_1_3_exterior_basis [CharZero K] (k s : ℕ) :
    ∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*k+1)) (I.val.val i))) := by
  refine ⟨oddExteriorBasis k s,?_⟩
  intro I
  rw [oddExteriorBasis_apply,exteriorPluckerBasis_apply]

end PaperVerification.AlternatingForms
