module
public import shared_results.part005

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CoordinateIdealPowers -/
section

/-!
# Powers of a coordinate ideal, coefficient by coefficient

The exponent of a monomial in a power of a variable-generated ideal is
measured by the sum of its exponents on those variables. The reverse
inclusion, needed for the mixed primary decomposition, is proved here by
removing one selected variable at a time. No reducedness or field
hypothesis is needed.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical MvPolynomial
variable {V K : Type*} [DecidableEq V] [CommSemiring K]

theorem monomial_mem_coordinateIdeal_power (C : Finset V) (s : ℕ)
    (a : V →₀ ℕ) (ha : s ≤ coverWeight C a) :
    monomial a (1 : K) ∈ coordinateIdeal C ^ s := by
  induction s generalizing a with
  | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ s ih =>
      have hn : (∑ v ∈ C, a v) ≠ 0 := by
        change coverWeight C a ≠ 0
        omega
      obtain ⟨v, hv, hav⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      have hvle : Finsupp.single v 1 ≤ a :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hav)
      let b := a - Finsupp.single v 1
      have hba : b + Finsupp.single v 1 = a := tsub_add_cancel_of_le hvle
      have hweight : coverWeight C b + 1 = coverWeight C a := by
        have h := congrArg (coverWeight C) hba
        rw [coverWeight_add] at h
        simpa [coverWeight, Finsupp.single_apply, hv] using h
      have hb : monomial b (1 : K) ∈ coordinateIdeal C ^ s := ih b (by omega)
      have hx : X v ∈ coordinateIdeal (k := K) C :=
        Ideal.subset_span ⟨v, hv, rfl⟩
      rw [pow_succ]
      have hprod := Ideal.mul_mem_mul hb hx
      change monomial b (1 : K) * monomial (Finsupp.single v 1) 1 ∈ _ at hprod
      simpa only [monomial_mul_monomial, one_mul, hba] using hprod

/-- The actual powers of the variable-generated ideal equal the exact
coefficient support condition. -/
theorem coordinateIdeal_power_eq_coverWeightIdeal (C : Finset V) (s : ℕ) :
    coordinateIdeal (k := K) C ^ s = coverWeightIdeal C s := by
  apply le_antisymm (coordinateIdeal_power_le C s)
  intro f hf
  rw [f.as_sum]
  apply Ideal.sum_mem
  intro a ha
  have hm := monomial_mem_coordinateIdeal_power (K := K) C s a
    ((mem_coverWeightIdeal C s f).mp hf a ha)
  have h := (coordinateIdeal (k := K) C ^ s).mul_mem_left (MvPolynomial.C (f.coeff a)) hm
  simpa only [C_mul_monomial, mul_one] using h

theorem mem_coordinateIdeal_power_iff (C : Finset V) (s : ℕ)
    (f : MvPolynomial V K) :
    f ∈ coordinateIdeal C ^ s ↔ ∀ a ∈ f.support, s ≤ coverWeight C a := by
  rw [coordinateIdeal_power_eq_coverWeightIdeal, mem_coverWeightIdeal]

theorem monomial_mem_coordinateIdeal_power_iff [Nontrivial K]
    (C : Finset V) (s : ℕ) (a : V →₀ ℕ) :
    monomial a (1 : K) ∈ coordinateIdeal C ^ s ↔ s ≤ coverWeight C a := by
  constructor
  · intro h
    apply (mem_coordinateIdeal_power_iff C s (monomial a (1 : K))).mp h a
    exact MvPolynomial.mem_support_iff.mpr (by simp)
  · exact monomial_mem_coordinateIdeal_power C s a

end FourPapers

end
end
end


end
