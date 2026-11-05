module

public import PaperVerification.PowerCoinvariantComparator
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Polynomial.Div
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Point-stabilizer invariants in the ordinary coinvariant quotient

The variables other than the distinguished first variable are symmetric.
The fundamental theorem of symmetric polynomials applies over the coefficient
ring `K[T]`. In the actual coinvariant quotient their elementary symmetric
polynomials become powers of the negative distinguished variable. That variable
has nilpotence exponent equal to the full number of variables.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerCoinvariantStabilizer

open PowerOperators

section Ring

variable {K : Type*} [CommRing K] {n : ℕ}

local notation "P" => MvPolynomial (Fin (n+1)) K
local notation "Q" => P ⧸ ordinaryCoinvariantIdeal K (n+1)

def restElementary (k : ℕ) : P := MvPolynomial.rename Fin.succ (MvPolynomial.esymm (Fin n) K k)

theorem elementary_successor (k : ℕ) :
    MvPolynomial.esymm (Fin (n+1)) K (k+1) =
      restElementary (K := K) (n := n) (k+1) + X 0 * restElementary (K := K) (n := n) k := by
  rw [MvPolynomial.esymm_eq_multiset_esymm,Fin.univ_val_map,List.ofFn_succ]
  change ((X 0 : P) ::ₘ (List.ofFn (fun i : Fin n => (X i.succ : P)) : Multiset P)).esymm (k+1) = _
  rw [Multiset.esymm_cons]
  simp only [restElementary,MvPolynomial.rename_eq_aeval,
    MvPolynomial.aeval_esymm_eq_multiset_esymm,Fin.univ_val_map,Function.comp_def]

def quotientMap : P →ₐ[K] Q := Ideal.Quotient.mkₐ K _

def firstVariable : Q := quotientMap (X 0)

theorem quotient_elementary_eq_zero (k : ℕ) (hk : 0 < k) (hkn : k ≤ n+1) :
    quotientMap (K := K) (n := n) (MvPolynomial.esymm (Fin (n+1)) K k) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨⟨k-1,by omega⟩,?_⟩
  change MvPolynomial.esymm (Fin (n+1)) K (k-1+1) =
    MvPolynomial.esymm (Fin (n+1)) K k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]

theorem quotient_restElementary (k : ℕ) (hk : k ≤ n+1) :
    quotientMap (restElementary (K := K) (n := n) k) = (-firstVariable (K := K) (n := n))^k := by
  induction k with
  | zero => simp only [restElementary,MvPolynomial.esymm_zero,map_one,pow_zero]
  | succ k ih =>
    have hrec := congrArg (quotientMap (K := K) (n := n)) (elementary_successor (K := K) (n := n) k)
    rw [quotient_elementary_eq_zero (k+1) (Nat.succ_pos _) hk,map_add,map_mul] at hrec
    change 0 = quotientMap (restElementary (K := K) (n := n) (k+1)) +
      firstVariable * quotientMap (restElementary (K := K) (n := n) k) at hrec
    rw [ih (by omega)] at hrec
    calc
      _ = -(firstVariable * (-firstVariable (K := K) (n := n))^k) :=
        eq_neg_of_add_eq_zero_left hrec.symm
      _ = _ := by rw [pow_succ]; ring

theorem firstVariable_pow_card_eq_zero : (firstVariable (K := K) (n := n))^(n+1) = 0 := by
  have he : MvPolynomial.esymm (Fin n) K (n+1) = 0 := by
    rw [MvPolynomial.esymm_eq_multiset_esymm,Multiset.esymm_of_card_lt]
    simp
  have h := quotient_restElementary (K := K) (n := n) (n+1) le_rfl
  rw [restElementary,he,map_zero,map_zero] at h
  rw [_root_.neg_pow (firstVariable (K := K) (n := n)) (n+1)] at h
  exact (isUnit_neg_one.pow (n+1)).mul_right_eq_zero.mp h.symm

/-- Extend a permutation of the last `n` variables by fixing the first. -/
def liftPermutation (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by cases i using Fin.cases <;> simp

@[simp] theorem liftPermutation_zero (e : Equiv.Perm (Fin n)) : liftPermutation e 0 = 0 := rfl
@[simp] theorem liftPermutation_succ (e : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPermutation e i.succ = (e i).succ := rfl

@[simp] theorem liftPermutation_one : liftPermutation (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i
  cases i using Fin.cases <;> rfl

@[simp] theorem liftPermutation_mul (e f : Equiv.Perm (Fin n)) :
    liftPermutation (e*f) = liftPermutation e * liftPermutation f := by
  ext i
  cases i using Fin.cases <;> rfl

/-- Regard the first variable as the coefficient indeterminate. -/
def splitPolynomial : P →ₐ[K] MvPolynomial (Fin n) (Polynomial K) :=
  MvPolynomial.aeval (Fin.cases (C Polynomial.X) (fun i => X i))

def joinPolynomial : MvPolynomial (Fin n) (Polynomial K) →ₐ[K] P :=
  MvPolynomial.aevalTower (Polynomial.aeval (X 0)) (fun i => X i.succ)

theorem join_split (p : P) : joinPolynomial (splitPolynomial p) = p := by
  have he : (joinPolynomial (K := K) (n := n)).comp splitPolynomial = AlgHom.id K P := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;>
      simp only [AlgHom.comp_apply,splitPolynomial,joinPolynomial,MvPolynomial.aeval_X,
        Fin.cases_zero,Fin.cases_succ,MvPolynomial.aevalTower_C,MvPolynomial.aevalTower_X,
        Polynomial.aeval_X,AlgHom.id_apply]
  exact AlgHom.congr_fun he p

theorem split_rename (e : Equiv.Perm (Fin n)) (p : P) :
    splitPolynomial (MvPolynomial.rename (liftPermutation e) p) =
      MvPolynomial.rename e (splitPolynomial p) := by
  have he : (splitPolynomial (K := K) (n := n)).comp (MvPolynomial.rename (liftPermutation e)) =
      ((MvPolynomial.rename e).restrictScalars K).comp splitPolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;>
      simp only [AlgHom.comp_apply,MvPolynomial.rename_X,liftPermutation_zero,liftPermutation_succ,
        splitPolynomial,MvPolynomial.aeval_X,Fin.cases_zero,Fin.cases_succ,
        AlgHom.restrictScalars_apply,MvPolynomial.rename_C,MvPolynomial.rename_X]
  exact AlgHom.congr_fun he p

theorem split_isSymmetric (p : P)
    (hp : ∀ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p = p) :
    (splitPolynomial p).IsSymmetric := by
  intro e
  rw [← split_rename,hp]

theorem join_elementary (k : ℕ) :
    joinPolynomial (MvPolynomial.esymm (Fin n) (Polynomial K) k) =
      restElementary (K := K) (n := n) k := by
  simp only [joinPolynomial,restElementary,MvPolynomial.esymm,map_sum,map_prod,
    MvPolynomial.aevalTower_X,MvPolynomial.rename_X]

/-- A point-stabilizer invariant polynomial class lies in the actual
one-variable polynomial subalgebra generated by the distinguished variable. -/
theorem invariant_class_mem_polynomial_range (p : P)
    (hp : ∀ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p = p) :
    quotientMap p ∈ (Polynomial.aeval (R := K) (firstVariable (K := K) (n := n))).range := by
  let S := (Polynomial.aeval (R := K) (firstVariable (K := K) (n := n))).range
  obtain ⟨f,hf⟩ := MvPolynomial.esymmAlgHom_surjective (σ := Fin n) (Polynomial K)
    (n := n) (by simp) ⟨splitPolynomial p,split_isSymmetric p hp⟩
  have he : MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) (Polynomial K) (i.val+1)) f =
      splitPolynomial p := by
    simpa only [MvPolynomial.esymmAlgHom_apply] using congrArg Subtype.val hf
  rw [← join_split p,← he]
  clear hf he
  induction f using MvPolynomial.induction_on with
  | C r =>
    change quotientMap (joinPolynomial (MvPolynomial.aeval _ (C r))) ∈ S
    rw [MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq]
    rw [joinPolynomial,MvPolynomial.aevalTower_C]
    change quotientMap (Polynomial.aeval (X 0) r) ∈ S
    refine ⟨r,?_⟩
    exact Polynomial.aeval_algHom_apply quotientMap (X 0) r
  | add f g hf hg =>
    simpa only [map_add] using S.add_mem hf hg
  | mul_X f i hf =>
    simp only [map_mul,MvPolynomial.aeval_X,join_elementary,
      quotient_restElementary (K := K) (n := n) (i.val+1) (by omega)]
    apply S.mul_mem hf
    apply S.pow_mem
    apply S.neg_mem
    exact ⟨Polynomial.X,Polynomial.aeval_X _⟩

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin (n+1)) K
local notation "Q" => P ⧸ ordinaryCoinvariantIdeal K (n+1)

theorem invariant_class_bounded_polynomial (p : P)
    (hp : ∀ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p = p) :
    ∃ f : Polynomial K, f.natDegree < n+1 ∧
      Polynomial.aeval (firstVariable (K := K) (n := n)) f = quotientMap p := by
  obtain ⟨f,hf⟩ := invariant_class_mem_polynomial_range p hp
  let g := f %ₘ (Polynomial.X^(n+1))
  have hX : (Polynomial.X^(n+1) : Polynomial K) ≠ 1 := by
    intro h
    have h0 := congrArg (fun p : Polynomial K => p.coeff 0) h
    simpa using h0
  refine ⟨g,?_,?_⟩
  · simpa only [Polynomial.natDegree_X_pow] using
      Polynomial.natDegree_modByMonic_lt f (Polynomial.monic_X.pow (n+1)) hX
  · have hroot : Polynomial.eval₂ (algebraMap K Q) firstVariable
        (Polynomial.X^(n+1) : Polynomial K) = 0 := by
      simpa only [Polynomial.eval₂_pow,Polynomial.eval₂_X] using
        firstVariable_pow_card_eq_zero (K := K) (n := n)
    calc
      Polynomial.aeval firstVariable g = Polynomial.aeval firstVariable f :=
        Polynomial.eval₂_modByMonic_eq_self_of_root hroot
      _ = quotientMap p := hf

attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialGrading : TauCeti.InternalGrading K P ℕ :=
  .ofDecomposition (homogeneousSubmodule (Fin (n+1)) K)

theorem ordinaryCoinvariantIdeal_homogeneous :
    DirectSum.SetLike.IsHomogeneous (polynomialGrading (K := K) (n := n)).piece
      ((ordinaryCoinvariantIdeal K (n+1)).restrictScalars K) := by
  rw [polynomialGrading,TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
  change (ordinaryCoinvariantIdeal K (n+1)).IsHomogeneous (homogeneousSubmodule (Fin (n+1)) K)
  apply Ideal.homogeneous_span
  rintro p ⟨i,rfl⟩
  exact ⟨i.val+1,MvPolynomial.isHomogeneous_esymm _⟩

def coinvariantGrading : TauCeti.InternalGrading K Q ℕ :=
  (polynomialGrading (K := K) (n := n)).quotient
    (ordinaryCoinvariantIdeal K (n+1)) ordinaryCoinvariantIdeal_homogeneous

@[simp] theorem coinvariantGrading_piece (d : ℕ) :
    (coinvariantGrading (K := K) (n := n)).piece d =
      (homogeneousSubmodule (Fin (n+1)) K d).map quotientMap.toLinearMap := by
  simp only [coinvariantGrading,TauCeti.InternalGrading.quotient_piece,
    polynomialGrading,TauCeti.InternalGrading.ofDecomposition_piece]
  rfl

def degreeProjection (d : ℕ) : Q →ₗ[K] Q :=
  ((coinvariantGrading (K := K) (n := n)).piece d).subtype.comp
    ((DirectSum.component K ℕ (fun e => (coinvariantGrading (K := K) (n := n)).piece e) d).comp
      (DirectSum.decomposeLinearEquiv (coinvariantGrading (K := K) (n := n)).piece).toLinearMap)

@[simp] theorem degreeProjection_apply (d : ℕ) (z : Q) :
    degreeProjection d z =
      (DirectSum.decompose (coinvariantGrading (K := K) (n := n)).piece z d : Q) := rfl

set_option maxHeartbeats 1000000 in
theorem homogeneous_invariant_class_eq_zero (d : ℕ) (hd : n+1 ≤ d) (p : P)
    (hp : p.IsHomogeneous d)
    (hinv : ∀ e : Equiv.Perm (Fin n), MvPolynomial.rename (liftPermutation e) p = p) :
    quotientMap p = 0 := by
  obtain ⟨f,hdeg,hf⟩ := invariant_class_bounded_polynomial p hinv
  have hself : degreeProjection d (quotientMap p) = quotientMap p := by
    rw [degreeProjection_apply]
    apply DirectSum.decompose_of_mem_same
    rw [coinvariantGrading_piece]
    exact ⟨p,hp,rfl⟩
  have hz : degreeProjection d (quotientMap p) = 0 := by
    rw [← hf,f.as_sum_range_C_mul_X_pow' hdeg,map_sum,map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
    rw [← Algebra.smul_def]
    change degreeProjection d ((f.coeff j) • (quotientMap (X 0))^j) = 0
    rw [← map_pow,map_smul,degreeProjection_apply]
    have hm : quotientMap ((X 0 : P)^j) ∈
        (coinvariantGrading (K := K) (n := n)).piece j := by
      rw [coinvariantGrading_piece]
      exact ⟨(X 0)^j,by simpa using (isHomogeneous_X K (0 : Fin (n+1))).pow j,rfl⟩
    rw [DirectSum.decompose_of_mem_ne _ hm (by have hj' := Finset.mem_range.mp hj; omega),smul_zero]
  exact hself.symm.trans hz

end Field

end PaperVerification.PowerCoinvariantStabilizer
