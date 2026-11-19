module

public import PaperVerification.WeightedInitialFiber

/-!
# Strictly lower weight errors and genuine initial variables

This linear interface is used to transport the actual supported exterior
prefix inverse into an initial-ideal containment.  The error space is defined
by the literal polynomial coefficients, and the leading-variable conclusion
is derived from the conventional initial ideal.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- Actual polynomials all of whose nonzero monomials have weight below `d`. -/
def lowerWeightSpace (w : σ → ℕ) (d : ℕ) : Submodule K P where
  carrier := {p | ∀ a : σ →₀ ℕ,p.coeff a≠0 → Finsupp.weight w a<d}
  zero_mem' := by intro a ha; exact (ha (by simp)).elim
  add_mem' {p q} hp hq := by
    intro a ha
    by_cases hpa : p.coeff a=0
    · apply hq a
      intro hqa
      exact ha (by simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hpa,hqa,add_zero])
    · exact hp a hpa
  smul_mem' c p hp := by
    intro a ha
    apply hp a
    intro hpa
    exact ha (by simp only [coeff_smul,hpa,smul_zero])

theorem lowerWeightSpace_mem_of_homogeneous (w : σ → ℕ) (p : P) (e d : ℕ)
    (hp : p.IsWeightedHomogeneous w e) (hed : e<d) : p∈lowerWeightSpace w d := by
  intro a ha
  exact (hp ha).trans_lt hed

theorem lowerWeightSpace_component_eq_zero (w : σ → ℕ) (p : P) (d e : ℕ)
    (hp : p∈lowerWeightSpace w d) (hde : d≤e) : weightedHomogeneousComponent w e p=0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro a ha
  exact ne_of_lt ((hp a (mem_support_iff.mp ha)).trans_le hde)

theorem lowerWeightSpace_weightBound (w : σ → ℕ) (p : P) (d : ℕ)
    (hp : p∈lowerWeightSpace w d) : WeightBound w d p :=
  fun a ha => (hp a ha).le

/-- A genuine relation with one leading variable puts that variable in the
actual weight initial ideal.  The nonzero coefficient is inverted in the
original field; the lower-weight error is checked coefficientwise. -/
theorem variable_mem_initialIdeal_of_lower_relation (I : Ideal P) (w : σ → ℕ)
    (i : σ) (c : K) (hc : c≠0) (g : P)
    (hg : g∈lowerWeightSpace w (w i)) (hrel : c • X i+g∈I) :
    X i∈initialIdeal I w := by
  have hlead : (c • X i : P).IsWeightedHomogeneous w (w i) :=
    (weightedHomogeneousSubmodule K w (w i)).smul_mem c (isWeightedHomogeneous_X K w i)
  have hb : WeightBound w (w i) (c • X i+g) :=
    weightBound_add w (w i) (fun a ha => (hlead ha).le)
      (lowerWeightSpace_weightBound w g (w i) hg)
  have hm := component_mem_initialIdeal I w (c • X i+g) hrel (w i) hb
  rw [map_add,map_smul,weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_X K w i),
    lowerWeightSpace_component_eq_zero w g (w i) (w i) hg le_rfl,add_zero] at hm
  have h := ((initialIdeal I w).restrictScalars K).smul_mem c⁻¹ hm
  change c⁻¹ • (c • X i : P) ∈ initialIdeal I w at h
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using h

end PaperVerification.WeightedInitialFiber
