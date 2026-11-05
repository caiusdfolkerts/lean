module

public import PaperVerification.FermionStrictIndex
public import PaperVerification.FermionPairedExteriorPieces

/-!
# Strict rank and exact exterior index enumeration

The complete strict-to-paired-tail bijection preserves exterior degree.
Consequently it transfers the already proved paired weighted enumeration
to every strict box, including the n=1 endpoint with empty paired tail.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open Exterior Endpoint
open scoped BigOperators

variable {A R : Type*} [CommSemiring A] [CommRing R] {n : ℕ}

theorem paired_index_exterior_sum (r u v : Fin n → ℕ) (s : ℕ)
    (huv : ∀ i,u i+v i=r i*s) (t : A) :
    (∑ z : PairedPowerIndex r u v s,t^z.1.card)=
      ((∏ i,r i : ℕ) : A)*(s.ascFactorial n : A)*(1+t)^n := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pairedWordPolynomialIndex]
  exact paired_box_sum r u v s huv t

theorem strict_index_exterior_sum (r : Fin n → ℕ) (hn : 0<n) (t : A) :
    (∑ z : StrictPowerIndex r,t^z.1.card)=
      ((∏ i,r i : ℕ) : A)*(n.factorial : A)*(1+t)^(n-1) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
      rw [←Equiv.sum_comp (strictIndexTailEquiv r).symm,Fintype.sum_prod_type]
      have hcard (a : Fin (r 0))
          (z : PairedPowerIndex (fun i ↦ r i.succ) (fun i ↦ r i.succ) (fun i ↦ r i.succ) 2) :
          ((strictIndexTailEquiv r).symm (a,z)).1.card=z.1.card := wordCons_card z.1
      simp only [hcard,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin]
      rw [paired_index_exterior_sum _ _ _ 2 (fun i ↦ by omega),Fin.prod_univ_succ,Nat.cast_mul]
      have hfac : (2 : ℕ).ascFactorial n=(n+1).factorial := by
        simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 n
      rw [hfac,Nat.add_sub_cancel]
      ring

instance strictIndex_fintype (d : StrictData (K := R) (n := n)) : Fintype (StrictIndex d) :=
  Fintype.ofEquiv (StrictPowerIndex d.r) (strictIndexEquiv d).symm

theorem card_strictIndex (d : StrictData (K := R) (n := n)) :
    Fintype.card (StrictIndex d)=2^(n-1)*(∏ i,d.r i)*n.factorial := by
  rw [Fintype.card_congr (strictIndexEquiv d)]
  exact card_strictPowerIndex d.r d.positive_n

theorem strict_finrank [Nontrivial R] (d : StrictData (K := R) (n := n)) :
    Module.finrank R (StrictQuotient d.beta d.phi)=2^(n-1)*(∏ i,d.r i)*n.factorial := by
  rw [Module.finrank_eq_card_basis (strictPaperBasis d),card_strictIndex]

def strictBasisExteriorPolynomial (r : Fin n → ℕ) : Polynomial ℕ :=
  ∑ z : StrictPowerIndex r,Polynomial.X^z.1.card

theorem strictBasisExteriorPolynomial_closed (r : Fin n → ℕ) (hn : 0<n) :
    strictBasisExteriorPolynomial r=
      Polynomial.C ((∏ i,r i)*n.factorial)*(1+Polynomial.X)^(n-1) := by
  have hC (k : ℕ) : Polynomial.C k = (k : Polynomial ℕ) := by
    simpa only [Nat.cast_id] using (Polynomial.C_eq_natCast (R := ℕ) k)
  simpa only [strictBasisExteriorPolynomial,hC,Nat.cast_mul,mul_assoc] using
    strict_index_exterior_sum r hn (Polynomial.X : Polynomial ℕ)

end PaperVerification.Fermion
