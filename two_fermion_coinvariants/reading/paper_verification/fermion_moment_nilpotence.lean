module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Nilpotence forced by weighted moment equations

This argument treats arbitrary finite index sets and actual coefficient rings.
A polynomial isolates each fiber of the node function over a fraction field.
Passing through every prime ideal proves nilpotence in the original ring.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open Polynomial
open scoped BigOperators

section Field

variable {F ι : Type*} [Field F] [Fintype ι]

/-- If every nonempty sum of weights is nonzero, vanishing of all weighted
moments forces a function of each node to vanish at every node. No distinctness
hypothesis on the nodes is imposed. -/
theorem weighted_moments_zero_field (beta node : ι → F) (value : F → F)
    (hbeta : ∀ s : Finset ι,s.Nonempty → (∑ i ∈ s,beta i)≠0)
    (hm : ∀ k : ℕ,∑ i,beta i*node i^k*value (node i)=0) :
    ∀ i,value (node i)=0 := by
  classical
  have hp : ∀ p : Polynomial F,∑ i,beta i*p.eval (node i)*value (node i)=0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.eval_add,mul_add,add_mul,Finset.sum_add_distrib,hp,hq,add_zero]
    | monomial k c =>
      simp only [Polynomial.eval_monomial]
      calc
        (∑ i,beta i*(c*node i^k)*value (node i)) =
            c*(∑ i,beta i*node i^k*value (node i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _=0 := by rw [hm,mul_zero]
  intro i
  let bad : Finset ι := Finset.univ.filter (fun j ↦ node j≠node i)
  let same : Finset ι := Finset.univ.filter (fun j ↦ node j=node i)
  let p : Polynomial F := ∏ j ∈ bad,(Polynomial.X-Polynomial.C (node j))
  have hsame : same.Nonempty := ⟨i,by simp [same]⟩
  have hpi : p.eval (node i)≠0 := by
    dsimp only [p]
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : node j≠node i := (Finset.mem_filter.mp hj).2
    simpa only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using
      sub_ne_zero.mpr (Ne.symm hji)
  have hpbad : ∀ j,node j≠node i → p.eval (node j)=0 := by
    intro j hj
    dsimp only [p]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (show j∈bad by simp [bad,hj])
    simp
  have hsum :
      (∑ j,beta j*p.eval (node j)*value (node j)) =
        (∑ j ∈ same,beta j)*(p.eval (node i)*value (node i)) := by
    calc
      (∑ j,beta j*p.eval (node j)*value (node j)) =
          ∑ j,if node j=node i then beta j*(p.eval (node i)*value (node i)) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : node j=node i
        · simp only [hji,if_true,mul_assoc]
        · simp only [hji,if_false,hpbad j hji,mul_zero,zero_mul]
      _=(∑ j ∈ same,beta j)*(p.eval (node i)*value (node i)) := by
        rw [Finset.sum_mul]
        simp only [same,Finset.sum_filter]
  have hz : (∑ j ∈ same,beta j)*(p.eval (node i)*value (node i))=0 := by
    rw [←hsum]
    exact hp p
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hbeta same hsame))).resolve_left hpi

end Field

section Ring

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]

/-- All-ring form of the moment nilpotence argument. The conclusion is
nilpotence in the actual algebra, not merely vanishing at complex points. -/
theorem weighted_polynomial_moments_nilpotent (beta : ι → R)
    (hbeta : ∀ s : Finset ι,s.Nonempty → IsUnit (∑ i ∈ s,beta i))
    (node : ι → A) (p : Polynomial R)
    (hm : ∀ k : ℕ,∑ i,algebraMap R A (beta i)*node i^k*
      Polynomial.aeval (node i) p=0) :
    ∀ i,IsNilpotent (Polynomial.aeval (node i) p) := by
  classical
  intro i
  apply nilpotent_iff_mem_prime.mpr
  intro J hJ
  letI : J.IsPrime := hJ
  let L := FractionRing (A ⧸ J)
  let f : A →ₐ[R] L :=
    (IsScalarTower.toAlgHom R (A ⧸ J) L).comp (Ideal.Quotient.mkₐ R J)
  have hbL : ∀ s : Finset ι,s.Nonempty →
      (∑ j ∈ s,algebraMap R L (beta j))≠0 := by
    intro s hs
    have hu := (hbeta s hs).map (algebraMap R L)
    rw [map_sum] at hu
    exact hu.ne_zero
  have hmL : ∀ k : ℕ,
      ∑ j,algebraMap R L (beta j)*(f (node j))^k*
        Polynomial.aeval (f (node j)) p=0 := by
    intro k
    have he := congrArg f (hm k)
    simpa only [map_sum,map_mul,map_pow,map_zero,f.commutes,
      ←Polynomial.aeval_algHom_apply] using he
  have hz := weighted_moments_zero_field
    (fun j ↦ algebraMap R L (beta j)) (fun j ↦ f (node j))
    (fun x ↦ Polynomial.aeval x p) hbL hmL i
  have hq : Ideal.Quotient.mk J (Polynomial.aeval (node i) p)=0 := by
    apply IsFractionRing.injective (A ⧸ J) L
    rw [map_zero]
    change f (Polynomial.aeval (node i) p)=0
    rwa [←Polynomial.aeval_algHom_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hq

/-- In the homogeneous power case each coordinate is nilpotent. This
does not require positive exponents: a zero exponent forces the relevant
quotient to be the zero ring, and the conclusion remains correct. -/
theorem weighted_power_moments_nilpotent (beta : ι → R)
    (hbeta : ∀ s : Finset ι,s.Nonempty → IsUnit (∑ i ∈ s,beta i))
    (z : ι → A) (r : ι → ℕ) (s : ℕ)
    (hm : ∀ k : ℕ,∑ i,algebraMap R A (beta i)*z i^(r i*(s+k))=0) :
    ∀ i,IsNilpotent (z i) := by
  have he := weighted_polynomial_moments_nilpotent beta hbeta
    (fun i ↦ z i^r i) (Polynomial.X^s) (fun k ↦ by
      simpa only [Polynomial.aeval_X_pow,←pow_add,←pow_mul,
        mul_assoc,←Nat.mul_add,Nat.add_comm k s] using hm k)
  intro i
  obtain ⟨N,hN⟩ := he i
  refine ⟨r i*(s*N),?_⟩
  simpa only [Polynomial.aeval_X_pow,pow_mul] using hN

end Ring

end PaperVerification.Fermion
