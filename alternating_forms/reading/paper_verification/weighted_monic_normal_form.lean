module

public import PaperVerification.WeightedSagbiCore

/-!
# Coefficient control in an actual distinct-leading-term expansion

Every nonzero basis coefficient lies below the input's weight bound. At
that bound its coefficient is the corresponding leading-monomial
coefficient of the input. In particular a monic input can have only its
unique matching standard leading exponent at the greatest weight.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedSagbi

open MvPolynomial
open scoped BigOperators
open AlternatingForms WeightedInitialFiber

variable {K τ C : Type*} [Field K]

variable (u : τ → ℕ) (v : C → MvPolynomial τ K)
  (a : C → τ →₀ ℕ) (degree : C → ℕ)
  (ha : Function.Injective a)
  (hv : ∀ c,IsWeightMonic (fun i => (u i : ℤ)) (v c) (a c))
  (hw : ∀ c,Finsupp.weight u (a c)=degree c)

include ha hv hw

/-- Distinct leading terms prohibit cancellation at the maximal active
weight, including when several basis terms have the same weight. -/
theorem expansion_degree_le (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c)) :
    ∀ c,coeff c≠0 → degree c≤d := by
  classical
  intro c hc
  have hS : coeff.support.Nonempty := ⟨c,Finsupp.mem_support_iff.mpr hc⟩
  obtain ⟨j,hj,hmax⟩ := coeff.support.exists_max_image degree hS
  have hcj : coeff j≠0 := Finsupp.mem_support_iff.mp hj
  have hlead : (coeff.sum fun c z => z • v c).coeff (a j)=coeff j := by
    simp only [Finsupp.sum,coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [coeff_smul,(hv j).1,smul_eq_mul,mul_one]
    · intro i hi hij
      rw [coeff_smul,(hv i).2 (a j) (fun he => hij (ha he.symm)),smul_zero]
      rw [←natCast_weight,←natCast_weight,hw,hw]
      exact_mod_cast hmax i hi
    · intro h
      exact (h hj).elim
  have hle : degree j≤d := by
    rw [←hw j]
    exact hbound (a j) (by rwa [hlead])
  exact (hmax c (Finsupp.mem_support_iff.mpr hc)).trans hle

/-- At the bound, the leading coefficient of a basis vector is not mixed
with any other vector in the full finite expansion. -/
theorem expansion_coefficient_at_bound (coeff : C →₀ K) (d : ℕ)
    (hbound : WeightBound u d (coeff.sum fun c z => z • v c))
    (c : C) (hc : degree c=d) :
    (coeff.sum fun c z => z • v c).coeff (a c)=coeff c := by
  classical
  have hdeg := expansion_degree_le u v a degree ha hv hw coeff d hbound
  simp only [Finsupp.sum,coeff_sum]
  rw [Finset.sum_eq_single c]
  · rw [coeff_smul,(hv c).1,smul_eq_mul,mul_one]
  · intro i hi hic
    rw [coeff_smul,(hv i).2 (a c) (fun he => hic (ha he.symm)),smul_zero]
    rw [←natCast_weight,←natCast_weight,hw,hw,hc]
    exact_mod_cast hdeg i (Finsupp.mem_support_iff.mp hi)
  · intro hc'
    have hz : coeff c=0 := Finsupp.notMem_support_iff.mp hc'
    rw [hz,zero_smul]
    rfl

theorem expansion_monic_top_exponent (coeff : C →₀ K)
    (p : MvPolynomial τ K) (ap : τ →₀ ℕ)
    (hp : IsWeightMonic (fun i => (u i : ℤ)) p ap)
    (hexp : coeff.sum (fun c z => z • v c)=p)
    (c : C) (hc : coeff c≠0) (hd : degree c=Finsupp.weight u ap) : a c=ap := by
  have hb : WeightBound u (Finsupp.weight u ap) (coeff.sum fun c z => z • v c) := by
    rw [hexp]
    exact weightBound_of_weightMonic u p ap hp
  have hcoeff := expansion_coefficient_at_bound u v a degree ha hv hw coeff _ hb c hd
  rw [hexp] at hcoeff
  by_contra hne
  have hz := hp.2 (a c) hne
    (by rw [←natCast_weight,←natCast_weight,hw,hd])
  exact hc (hcoeff.symm.trans hz)

theorem expansion_monic_top_coefficient (coeff : C →₀ K)
    (p : MvPolynomial τ K) (ap : τ →₀ ℕ)
    (hp : IsWeightMonic (fun i => (u i : ℤ)) p ap)
    (hexp : coeff.sum (fun c z => z • v c)=p)
    (c : C) (hc : a c=ap) : coeff c=1 := by
  have hb : WeightBound u (Finsupp.weight u ap) (coeff.sum fun c z => z • v c) := by
    rw [hexp]
    exact weightBound_of_weightMonic u p ap hp
  have hd : degree c=Finsupp.weight u ap := by rw [←hw,hc]
  have hcoeff := expansion_coefficient_at_bound u v a degree ha hv hw coeff _ hb c hd
  rw [hexp,hc,hp.1] at hcoeff
  exact hcoeff.symm

end PaperVerification.WeightedSagbi
