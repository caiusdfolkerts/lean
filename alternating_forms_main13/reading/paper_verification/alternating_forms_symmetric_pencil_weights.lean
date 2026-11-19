module

public import PaperVerification.AlternatingFormsRationalRepresentation
public import PaperVerification.AlternatingFormsTopGoodWords
public import PaperVerification.GradedComponentBasis
public import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Torus characters of the actual quotient pieces

Weights are computed on the original vector representation and then on its
actual exterior quotient.  The good basis is used only to compute the trace
of that already constructed action.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators TensorProduct Classical

namespace PaperVerification.AlternatingForms.SymmetricPencil

open TopInterlacing

variable (K : Type) [Field K]

def aWeight (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin k) : Kˣ :=
  u 0^((i.val : ℤ)+1-k) * u 1^(-(i.val : ℤ))

def bWeight (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin (k+1)) : Kˣ :=
  u 0^((k : ℤ)-i.val) * u 1^(i.val : ℤ)

def indexWeight (k : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*k+1)) : Kˣ :=
  Sum.elim (aWeight K k u) (bWeight K k u) ((abIndex k).symm j)

def wordWeight {k s : ℕ} (u : Fin 2 → Kˣ) (I : Fin s → Fin (2*k+1)) : Kˣ :=
  ∏ i, indexWeight K k u (I i)

@[simp] theorem indexWeight_a (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin k) :
    indexWeight K k u (abIndex k (.inl i))=aWeight K k u i := by
  simp [indexWeight]

@[simp] theorem indexWeight_b (k : ℕ) (u : Fin 2 → Kˣ) (i : Fin (k+1)) :
    indexWeight K k u (abIndex k (.inr i))=bWeight K k u i := by
  simp [indexWeight]

theorem binaryBasis_diagonal (d : ℕ) (u : Fin 2 → Kˣ) (i : Fin (d+1)) :
    TauCeti.symPowerRep K 2 d (TauCeti.diagGL u) (binaryBasis K d i) =
      (bWeight K d u i : K) • binaryBasis K d i := by
  have h := (Pi.basisFun K (Fin 2)).map_symmetricPower_of_apply
    (TauCeti.stdRep K 2 (TauCeti.diagGL u)) (fun j => (u j : K))
    (TauCeti.stdRep_diagGL_apply_basisFun u) ((binaryIndex d).symm i)
  rw [TauCeti.symPowerRep, Representation.symmetricPower_apply]
  simp only [binaryBasis,Module.Basis.reindex_apply]
  change SymmetricPower.map (ι := Fin d) (TauCeti.stdRep K 2 (TauCeti.diagGL u))
      ((Pi.basisFun K (Fin 2)).symmetricPower d ((binaryIndex d).symm i)) = _
  rw [h]
  congr 1
  have hi : i.val≤d := by have := i.isLt; omega
  simp only [binaryIndex, Equiv.symm_trans_apply, Fin.revPerm_symm,
    Fin.revPerm_apply, TauCeti.coe_symFinTwoEquiv_symm_apply,
    Multiset.map_add, Multiset.map_replicate, Multiset.prod_add, Multiset.prod_replicate,
    Fin.val_rev, bWeight, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [show d+1-(i.val+1)=d-i.val by omega,Nat.sub_sub_self hi,
    show (d : ℤ)-(i.val : ℤ)=((d-i.val : ℕ) : ℤ) by omega,
    zpow_natCast, zpow_natCast]

theorem binaryDualBasis_diagonal (d : ℕ) (u : Fin 2 → Kˣ) (i : Fin (d+1)) :
    (TauCeti.symPowerRep K 2 d).dual (TauCeti.diagGL u) ((binaryBasis K d).dualBasis i) =
      (aWeight K (d+1) u i : K) • (binaryBasis K d).dualBasis i := by
  apply (binaryBasis K d).ext
  intro j
  change (binaryBasis K d).dualBasis i
      (TauCeti.symPowerRep K 2 d (TauCeti.diagGL u)⁻¹ (binaryBasis K d j)) = _
  rw [← map_inv TauCeti.diagGL u, binaryBasis_diagonal, map_smul,
    LinearMap.smul_apply, Module.Basis.dualBasis_apply_self]
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl, smul_eq_mul, mul_one]
    congr 1
    simp only [bWeight, aWeight, Pi.inv_apply, inv_zpow, inv_inv, Nat.cast_add, Nat.cast_one]
    rw [show ((i.val : ℤ)+1-(d+1)) = -((d : ℤ)-i.val) by omega,
      zpow_neg, zpow_neg]
  · simp only [hij, Ne.symm hij, if_false, smul_eq_mul, mul_zero]

theorem modelBasis_diagonal (t : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*(t+1)+1)) :
    modelRepresentation K t (TauCeti.diagGL u) (modelBasis K t j) =
      (indexWeight K (t+1) u j : K) • modelBasis K t j := by
  obtain ⟨j,rfl⟩ := (abIndex (t+1)).surjective j
  cases j with
  | inl i =>
      have hi : abIndex (t+1) (.inl i)=oddPathMiddle i := by
        apply Fin.ext
        rfl
      rw [hi, modelBasis_middle]
      change ((TauCeti.symPowerRep K 2 t).dual (TauCeti.diagGL u)
          ((binaryBasis K t).dualBasis i),
        TauCeti.symPowerRep K 2 (t+1) (TauCeti.diagGL u) 0) = _
      rw [← hi, indexWeight_a]
      simp only [map_zero, Prod.smul_mk, smul_zero, binaryDualBasis_diagonal]
  | inr i =>
      have hb : modelBasis K t (abIndex (t+1) (.inr i)) =
          (0, binaryBasis K (t+1) i) := by
        change modelBasis K t ((TopInterlacing.abIndex (t+1)) (.inr i)) = _
        simp [modelBasis, Module.Basis.prod_apply]
      rw [hb, indexWeight_b]
      change ((TauCeti.symPowerRep K 2 t).dual (TauCeti.diagGL u) 0,
        TauCeti.symPowerRep K 2 (t+1) (TauCeti.diagGL u) (binaryBasis K (t+1) i)) = _
      simp only [map_zero, Prod.smul_mk, smul_zero, binaryBasis_diagonal]

theorem coordinateBasis_diagonal (t : ℕ) (u : Fin 2 → Kˣ) (j : Fin (2*(t+1)+1)) :
    coordinateRepresentation K t (TauCeti.diagGL u)
      (Pi.basisFun K (Fin (2*(t+1)+1)) j) =
      (indexWeight K (t+1) u j : K) • Pi.basisFun K (Fin (2*(t+1)+1)) j := by
  apply (coordinateEquiv K t).injective
  rw [coordinateRepresentation_equiv, map_smul]
  simpa only [coordinateEquiv, standardBasisEquiv_basisFun] using modelBasis_diagonal K t u j

variable [CharZero K]

theorem quotient_goodBasis_diagonal (t s : ℕ) (u : Fin 2 → Kˣ)
    (I : GoodOddIndex (t+1) s) :
    quotientRepresentation K t s (TauCeti.diagGL u) (oddExteriorBasis (t+1) s I) =
      (wordWeight K u I.val.val : K) • oddExteriorBasis (t+1) s I := by
  rw [oddExteriorBasis_apply, exteriorPluckerBasis_apply, quotientRepresentation_mk,
    exteriorPower.map_apply_ιMulti]
  have he : coordinateRepresentation K t (TauCeti.diagGL u) ∘
      (fun i => Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i)) =
    fun i => (indexWeight K (t+1) u (I.val.val i) : K) •
      Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i) := by
    funext i
    exact coordinateBasis_diagonal K t u _
  rw [he, AlternatingMap.map_smul_univ]
  have hw : (∏ i, (indexWeight K (t+1) u (I.val.val i) : K)) =
      (wordWeight K u I.val.val : K) := by
    exact (Units.coe_prod (fun i => indexWeight K (t+1) u (I.val.val i)) Finset.univ).symm
  rw [hw]
  exact Submodule.Quotient.mk_smul (R := K) (S := K)
    (p := exteriorDegreeRelations (K := K)
      (oddPathFirstQuadratic (K := K) (Pi.basisFun K (Fin (2*(t+1)+1))))
      (oddPathSecondQuadratic (K := K) (Pi.basisFun K (Fin (2*(t+1)+1)))) s)
    (wordWeight K u I.val.val : K)
    (exteriorPower.ιMulti K s (fun i => Pi.basisFun K (Fin (2*(t+1)+1)) (I.val.val i)))

/-- In the exceptional case `k=0`, the only vector span is `Sym⁰ U`, on
which the induced action is the identity. -/
def naturalQuotientRepresentation : (k s : ℕ) →
    Representation K (GL (Fin 2) K) (OddExteriorQuotientDegree (K := K) k s)
  | 0, s => Representation.trivial K (GL (Fin 2) K) _
  | t+1, s => quotientRepresentation K t s

def naturalBigradedRepresentation : (k p q : ℕ) →
    Representation K (GL (Fin 2) K) (Bidegree.actualBigradedPiece (K := K) k p q)
  | 0, p, q => Representation.trivial K (GL (Fin 2) K) _
  | t+1, p, q => bigradedRepresentation K t p q

theorem indexWeight_zero (u : Fin 2 → Kˣ) (j : Fin 1) : indexWeight K 0 u j=1 := by
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  have hzero : abIndex 0 (.inr (0 : Fin 1)) = (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [← hzero, indexWeight_b]
  simp [bWeight]

theorem natural_goodBasis_diagonal (k s : ℕ) (u : Fin 2 → Kˣ)
    (I : GoodOddIndex k s) :
    naturalQuotientRepresentation K k s (TauCeti.diagGL u) (oddExteriorBasis k s I) =
      (wordWeight K u I.val.val : K) • oddExteriorBasis k s I := by
  cases k with
  | zero => simp [naturalQuotientRepresentation, wordWeight, indexWeight_zero]
  | succ t => exact quotient_goodBasis_diagonal K t s u I

def bigradedBasis (k p q : ℕ) :
    Module.Basis {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p} K
      (Bidegree.actualBigradedPiece (K := K) k p q) :=
  (PaperVerification.GradedComponentBasis.componentBasis
    (Bidegree.quotientAGrading k (p+q)) (oddExteriorBasis k (p+q)) Bidegree.goodADegree
    (BasisDegree.basis_mem_piece (oddExteriorBasis k (p+q)) Bidegree.goodADegree) p).map
      (LinearEquiv.ofEq _ _ (Bidegree.quotientAGrading_piece k (p+q) p))

theorem bigradedBasis_coe (k p q : ℕ)
    (I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p}) :
    (bigradedBasis K k p q I : OddExteriorQuotientDegree (K := K) k (p+q)) =
      oddExteriorBasis k (p+q) I.val := by
  simp only [bigradedBasis, PaperVerification.GradedComponentBasis.componentBasis,
    Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply,
    Function.comp_apply]

theorem bigradedBasis_diagonal (k p q : ℕ) (u : Fin 2 → Kˣ)
    (I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p}) :
    naturalBigradedRepresentation K k p q (TauCeti.diagGL u) (bigradedBasis K k p q I) =
      (wordWeight K u I.val.val.val : K) • bigradedBasis K k p q I := by
  apply Subtype.ext
  have h := natural_goodBasis_diagonal K k (p+q) u I.val
  rw [← bigradedBasis_coe K k p q I] at h
  cases k <;> exact h

/-- The character is the trace of the actual quotient action, evaluated in
the proved original good-monomial basis. -/
theorem bigraded_character (k p q : ℕ) (u : Fin 2 → Kˣ) :
    (naturalBigradedRepresentation K k p q).character (TauCeti.diagGL u) =
      ∑ I : {I : GoodOddIndex k (p+q) // Bidegree.goodADegree I=p},
        (wordWeight K u I.val.val.val : K) := by
  rw [Representation.character, LinearMap.trace_eq_matrix_trace K (bigradedBasis K k p q),
    Matrix.trace]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, bigradedBasis_diagonal,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

end PaperVerification.AlternatingForms.SymmetricPencil
