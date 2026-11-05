module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The generating series of all positive-weight exponent vectors

The coefficient identity is proved by a literal equivalence between
weighted exponent vectors and divisible exponent vectors in the finite
coefficient convolution.  Thus the product of geometric series counts
all monomials of every weight; no Hilbert-series formula is postulated.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.WeightedMonomialSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (w : ι → ℕ) (hw : ∀ i,w i≠0)

def Exponents (d : ℕ) := {a : ι →₀ ℕ // Finsupp.weight w a=d}

def scale (a : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i*a i)

def unscale (a : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i/w i)

@[simp] theorem scale_apply (a : ι →₀ ℕ) (i : ι) : scale w a i=w i*a i := by
  simp [scale]

@[simp] theorem unscale_apply (a : ι →₀ ℕ) (i : ι) : unscale w a i=a i/w i := by
  simp [unscale]

def divisibleAntidiagonal (d : ℕ) : Finset (ι →₀ ℕ) :=
  (Finset.finsuppAntidiag Finset.univ d).filter (fun a => ∀ i,w i∣a i)

theorem mem_divisibleAntidiagonal (d : ℕ) (a : ι →₀ ℕ) :
    a∈divisibleAntidiagonal w d ↔ (∑ i,a i)=d ∧ ∀ i,w i∣a i := by
  simp only [divisibleAntidiagonal,Finset.mem_filter,Finset.mem_finsuppAntidiag,
    Finset.subset_univ,and_true]

def exponentEquiv (d : ℕ) : Exponents w d ≃ divisibleAntidiagonal w d where
  toFun a := ⟨scale w a.val,by
    rw [mem_divisibleAntidiagonal]
    constructor
    · simpa only [scale_apply,Finsupp.weight_eq_sum,smul_eq_mul,mul_comm] using a.property
    · intro i
      exact ⟨a.val i,rfl⟩⟩
  invFun a := ⟨unscale w a.val,by
    have ha := (mem_divisibleAntidiagonal w d a.val).mp a.property
    rw [Finsupp.weight_eq_sum]
    calc
      (∑ i,unscale w a.val i • w i) = ∑ i,a.val i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.div_mul_cancel (ha.2 i)
      _ = d := ha.1⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    simp only [unscale_apply,scale_apply,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (hw i))]
  right_inv a := by
    apply Subtype.ext
    ext i
    simp only [scale_apply,unscale_apply]
    exact Nat.mul_div_cancel' (((mem_divisibleAntidiagonal w d a.val).mp a.property).2 i)

def geometric (i : ι) : ℤ⟦X⟧ :=
  PowerSeries.expand (w i) (hw i) (PowerSeries.invOneSubPow ℤ 1)

theorem coeff_geometric (i : ι) (d : ℕ) :
    PowerSeries.coeff d (geometric w hw i)=if w i∣d then 1 else 0 := by
  rw [geometric,PowerSeries.coeff_expand]
  simp [PowerSeries.invOneSubPow]

private theorem product_indicators (a : ι →₀ ℕ) :
    (∏ i,if w i∣a i then (1 : ℤ) else 0)=
      if ∀ i,w i∣a i then 1 else 0 := by
  by_cases h : ∀ i,w i∣a i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Exact generating-series coefficients, including degree zero. -/
theorem coeff_product (d : ℕ) :
    PowerSeries.coeff d (∏ i,geometric w hw i)=Nat.card (Exponents w d) := by
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_geometric,product_indicators]
  rw [Finset.sum_boole]
  have hcard : Nat.card (Exponents w d)=(divisibleAntidiagonal w d).card := by
    have h := Nat.card_congr (exponentEquiv w hw d)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using h
  rw [hcard]
  rfl

theorem series_eq_product :
    PowerSeries.mk (fun d => (Nat.card (Exponents w d) : ℤ))=
      ∏ i,geometric w hw i := by
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_mk,coeff_product]

/-- Every factor is the inverse of its actual monomial denominator. -/
theorem geometric_mul_denominator (i : ι) :
    geometric w hw i*(1-PowerSeries.X^(w i))=1 := by
  have h := (PowerSeries.invOneSubPow ℤ 1).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow,pow_one] at h
  have he := congrArg (PowerSeries.expand (w i) (hw i)) h
  simpa only [map_mul,map_sub,map_one,PowerSeries.expand_X,geometric] using he

include hw in
theorem series_mul_denominator_eq_one :
    PowerSeries.mk (fun d => (Nat.card (Exponents w d) : ℤ))*
      (∏ i,(1-PowerSeries.X^(w i)))=1 := by
  rw [series_eq_product w hw,←Finset.prod_mul_distrib]
  simp only [geometric_mul_denominator w hw,Finset.prod_const_one]

end PaperVerification.WeightedMonomialSeries
