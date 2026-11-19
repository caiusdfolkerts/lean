module

public import PaperVerification.AlternatingFormsBandMinors
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Descent of a finite monic triangular expansion

If a finite polynomial family has distinct weight-monic leading monomials,
then a linear combination with coefficients in a larger field can have all
its polynomial coefficients in a subring only when all its expansion
coefficients already lie in that subring.  This is a saturation statement,
not a dimension argument or an assumption of flatness.

The main application is descent of rational maximal-minor straightening to
integer identities, followed by arbitrary coefficient extension.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification

open scoped BigOperators Classical
open MvPolynomial
open AlternatingForms

variable {K R σ ι : Type*} [Field K] [CommRing R] [Fintype ι]

/-- A leading-coefficient argument works over an arbitrary subring of the
coefficient field.  Only the finite displayed family is ordered by weight. -/
theorem weightMonic_coefficients_mem_subring
    (S : Subring K) (w : σ → ℤ) (p : ι → MvPolynomial σ K)
    (a : ι → σ →₀ ℕ) (ha : Function.Injective a)
    (hp : ∀ i, IsWeightMonic w (p i) (a i))
    (hpS : ∀ i d, (p i).coeff d ∈ S) (c : ι → K)
    (hcomb : ∀ d, (∑ i, c i • p i).coeff d ∈ S) :
    ∀ i, c i ∈ S := by
  intro i
  by_contra hi
  let bad : Finset ι := Finset.univ.filter fun j ↦ c j ∉ S
  have hbad : bad.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨j, hj, hmax⟩ := bad.exists_max_image (fun j ↦ Finsupp.weight w (a j)) hbad
  have hjbad : c j ∉ S := (Finset.mem_filter.mp hj).2
  have hrest : (∑ k ∈ (Finset.univ : Finset ι).erase j,
      c k * (p k).coeff (a j)) ∈ S := by
    apply S.sum_mem
    intro k hk
    by_cases hkS : c k ∈ S
    · exact S.mul_mem hkS (hpS k (a j))
    · have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hkbad : k ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkS⟩
      have hzero := (hp k).2 (a j) (fun he ↦ hkj (ha he.symm)) (hmax k hkbad)
      rw [hzero, mul_zero]
      exact S.zero_mem
  have hc := hcomb (a j)
  rw [coeff_sum] at hc
  simp only [coeff_smul, smul_eq_mul] at hc
  rw [← Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun k ↦ c k * (p k).coeff (a j)) (Finset.mem_univ j), (hp j).1, mul_one] at hc
  apply hjbad
  simpa only [add_sub_cancel_left] using S.sub_mem hc hrest

/-- An honest injective coefficient extension reflects membership in the
span of a monic triangular family.  In particular, rational spanning of
integer polynomials descends to integral spanning. -/
theorem weightMonic_span_descent
    (φ : R →+* K) (hφ : Function.Injective φ)
    (w : σ → ℤ) (p : ι → MvPolynomial σ R) (a : ι → σ →₀ ℕ)
    (ha : Function.Injective a)
    (hp : ∀ i, IsWeightMonic w (MvPolynomial.map φ (p i)) (a i))
    (q : MvPolynomial σ R)
    (hq : MvPolynomial.map φ q ∈
      Submodule.span K (Set.range fun i ↦ MvPolynomial.map φ (p i))) :
    q ∈ Submodule.span R (Set.range p) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have hcoeff : ∀ i, c i ∈ φ.range := by
    apply weightMonic_coefficients_mem_subring φ.range w _ a ha hp
    · intro i d
      exact ⟨(p i).coeff d, (MvPolynomial.coeff_map φ (p i) d).symm⟩
    · intro d
      rw [hc]
      exact ⟨q.coeff d, (MvPolynomial.coeff_map φ q d).symm⟩
  let d : ι → R := fun i ↦ Classical.choose (hcoeff i)
  have hd (i : ι) : φ (d i) = c i := Classical.choose_spec (hcoeff i)
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  refine ⟨d, ?_⟩
  apply MvPolynomial.map_injective φ hφ
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  simp_rw [hd]
  simpa only [MvPolynomial.smul_eq_C_mul] using hc

end PaperVerification
