module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary
public import Mathlib.RingTheory.Ideal.Operations
public import Lean.Elab.Tactic.Omega

/-!
# The literal ordinary coinvariant ideal

The first `n` complete homogeneous symmetric polynomials generate precisely
the ideal of the first `n` elementary symmetric polynomials. The proof is the
integral generating-function convolution, so the identification is valid in
every characteristic and involves no characteristic-zero division.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable (R : Type*) [CommRing R] (n : ℕ)

def ordinaryCoinvariantIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun i : Fin n => esymm (Fin n) R (i.val+1))

def completeCoinvariantIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun i : Fin n => hsymm (Fin n) R (i.val+1))

theorem hsymm_mem_ordinaryCoinvariantIdeal (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    hsymm (Fin n) R k ∈ ordinaryCoinvariantIdeal R n := by
  let I := ordinaryCoinvariantIdeal R n
  have hrec := TauCeti.sum_range_hsymm_mul_neg_one_pow_mul_esymm (σ := Fin n) R k
  rw [if_neg (Nat.ne_of_gt hk), Finset.sum_range_succ] at hrec
  simp only [Nat.sub_self, pow_zero, esymm_zero, one_mul, mul_one] at hrec
  have hsum : (∑ j ∈ Finset.range k, hsymm (Fin n) R j *
      ((-1 : MvPolynomial (Fin n) R)^(k-j) * esymm (Fin n) R (k-j))) ∈ I := by
    apply I.sum_mem
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have he : esymm (Fin n) R (k-j) ∈ I := by
      apply Ideal.subset_span
      refine ⟨⟨k-j-1, by omega⟩, ?_⟩
      change esymm (Fin n) R (k-j-1+1) = esymm (Fin n) R (k-j)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k-j)]
    exact I.mul_mem_left _ (I.mul_mem_left _ he)
  have heq : hsymm (Fin n) R k =
      -(∑ j ∈ Finset.range k, hsymm (Fin n) R j *
        ((-1 : MvPolynomial (Fin n) R)^(k-j) * esymm (Fin n) R (k-j))) := by
    exact eq_neg_of_add_eq_zero_right hrec
  rw [heq]
  exact I.neg_mem hsum

theorem esymm_mem_completeCoinvariantIdeal (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    esymm (Fin n) R k ∈ completeCoinvariantIdeal R n := by
  let I := completeCoinvariantIdeal R n
  have hrec := TauCeti.sum_range_hsymm_mul_neg_one_pow_mul_esymm (σ := Fin n) R k
  rw [if_neg (Nat.ne_of_gt hk), Finset.sum_range_succ'] at hrec
  simp only [Nat.sub_zero, hsymm_zero, one_mul] at hrec
  have hsum : (∑ j ∈ Finset.range k, hsymm (Fin n) R (j+1) *
      ((-1 : MvPolynomial (Fin n) R)^(k-(j+1)) * esymm (Fin n) R (k-(j+1)))) ∈ I := by
    apply I.sum_mem
    intro j hj
    have hjk := Finset.mem_range.mp hj
    have hh : hsymm (Fin n) R (j+1) ∈ I :=
      Ideal.subset_span ⟨⟨j, by omega⟩, rfl⟩
    exact I.mul_mem_right _ hh
  have hhead : (-1 : MvPolynomial (Fin n) R)^k * esymm (Fin n) R k ∈ I := by
    have heq : (-1 : MvPolynomial (Fin n) R)^k * esymm (Fin n) R k =
        -(∑ j ∈ Finset.range k, hsymm (Fin n) R (j+1) *
          ((-1 : MvPolynomial (Fin n) R)^(k-(j+1)) * esymm (Fin n) R (k-(j+1)))) := by
      exact eq_neg_of_add_eq_zero_right hrec
    rw [heq]
    exact I.neg_mem hsum
  exact (I.unit_mul_mem_iff_mem (isUnit_neg_one.pow k)).mp hhead

theorem completeCoinvariantIdeal_eq_ordinaryCoinvariantIdeal :
    completeCoinvariantIdeal R n = ordinaryCoinvariantIdeal R n := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hsymm_mem_ordinaryCoinvariantIdeal R n _ (Nat.succ_pos _) (by omega)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact esymm_mem_completeCoinvariantIdeal R n _ (Nat.succ_pos _) (by omega)

end PaperVerification.PowerOperators
