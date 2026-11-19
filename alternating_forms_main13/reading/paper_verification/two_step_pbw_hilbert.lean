module

public import PaperVerification.TwoStepPBWGrading
public import PaperVerification.WeightedMonomialSeries
public import TauCeti.Data.Finsupp.Weight

/-!
# The full Hilbert series of the actual two-step enveloping algebra

The degree pieces here are powers of the original generator subspace.
Their equality with weighted PBW pieces was established independently.
Counting the resulting exponent vectors gives the literal identity
`H(t) (1-t)^n (1-t^2)^2 = 1`, in all degrees at once.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.TwoStepPBWGrading

open TwoStepCentralLie QuadraticCommutatorQuotient

variable {K ν : Type*} [Field K] [CharZero K] [Fintype ν] [LinearOrder ν]
  (D : Data (K := K) (V := ν → K) (Z := K × K))
  (hD : Function.Surjective (bracketMap D))

theorem pbwDegree_eq_weight (a : (ν ⊕ Fin 2) →₀ ℕ) :
    pbwDegree a=Finsupp.weight (weight (ν := ν)) a := by
  simpa only [pbwDegree,Finsupp.toMultiset_toFinsupp] using
    (Finsupp.weight_toFinsupp (weight (ν := ν)) a.toMultiset).symm

theorem weight_ne_zero (i : ν ⊕ Fin 2) : weight i≠0 := by
  cases i <;> simp [weight]

def hilbertSeries : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (wordPiece D d) : ℤ))

include hD in
theorem hilbertSeries_eq_weightedSeries :
    hilbertSeries D=PowerSeries.mk (fun d =>
      (Nat.card (WeightedMonomialSeries.Exponents (weight (ν := ν)) d) : ℤ)) := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries,PowerSeries.coeff_mk,finrank_wordPiece D hD,
    pbwDegree_eq_weight,WeightedMonomialSeries.Exponents]

theorem weight_denominator :
    (∏ i : ν ⊕ Fin 2,(1-PowerSeries.X^(weight i) : ℤ⟦X⟧))=
      (1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2 := by
  rw [Fintype.prod_sum_type]
  simp only [weight,Sum.elim_inl,Sum.elim_inr,pow_one,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

include hD in
/-- The literal Hilbert-series formula with no degree cutoff. -/
theorem hilbertSeries_mul_denominator_eq_one :
    hilbertSeries D*((1-PowerSeries.X)^Fintype.card ν*(1-PowerSeries.X^2)^2)=1 := by
  rw [hilbertSeries_eq_weightedSeries D hD,←weight_denominator]
  exact WeightedMonomialSeries.series_mul_denominator_eq_one
    (weight (ν := ν)) weight_ne_zero

include hD in
/-- Equivalent inverse-series formulation of the printed rational expression. -/
theorem hilbertSeries_eq_inverse :
    hilbertSeries D=(PowerSeries.invOneSubPow ℤ (Fintype.card ν) : ℤ⟦X⟧)*
      PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2 : ℤ⟦X⟧) := by
  let A : ℤ⟦X⟧ := (1-PowerSeries.X)^Fintype.card ν
  let B : ℤ⟦X⟧ := (1-PowerSeries.X^2)^2
  let C : ℤ⟦X⟧ := PowerSeries.invOneSubPow ℤ (Fintype.card ν)
  let E : ℤ⟦X⟧ := PowerSeries.expand 2 (by decide) (PowerSeries.invOneSubPow ℤ 2 : ℤ⟦X⟧)
  have hAC : A*C=1 := by
    simpa only [A,C,PowerSeries.invOneSubPow_inv_eq_one_sub_pow] using
      (PowerSeries.invOneSubPow ℤ (Fintype.card ν)).inv_val
  have hBE : B*E=1 := by
    have h := (PowerSeries.invOneSubPow ℤ 2).inv_val
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
    have he := congrArg (PowerSeries.expand 2 (by decide)) h
    simpa only [B,E,map_mul,map_pow,map_sub,map_one,PowerSeries.expand_X] using he
  have hDE : (A*B)*(C*E)=1 := by
    calc
      (A*B)*(C*E)=(A*C)*(B*E) := by ac_rfl
      _=1 := by rw [hAC,hBE,mul_one]
  have hHD : hilbertSeries D*(A*B)=1 := hilbertSeries_mul_denominator_eq_one D hD
  change hilbertSeries D=C*E
  calc
    hilbertSeries D=hilbertSeries D*1 := (mul_one _).symm
    _=hilbertSeries D*((A*B)*(C*E)) := by rw [hDE]
    _=(hilbertSeries D*(A*B))*(C*E) := (mul_assoc _ _ _).symm
    _=C*E := by rw [hHD,one_mul]

end PaperVerification.TwoStepPBWGrading
