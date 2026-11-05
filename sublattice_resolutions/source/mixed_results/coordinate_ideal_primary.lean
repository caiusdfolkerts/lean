module
public import mixed_results.coordinate_ideal_powers
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Ideal.IsPrimary

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.CoordinateIdealPrimary -/
section

/-!
# Coordinate-ideal powers are primary

The proof uses the lowest total degree in the selected variables. If a
polynomial has no terms below selected-variable degree `s`, the degree
`s` part of its product with another polynomial is its degree `s` part
times the other's degree-zero part. Over a domain this proves saturation
by every polynomial outside the coordinate ideal, and hence primariness.

Only positive powers are primary. The zero power is the unit ideal and
is omitted when the mixed intersection is called a primary decomposition.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical MvPolynomial
variable {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]

/-- The component of fixed total degree in the variables of `C`. -/
def coordinateComponent (C : Finset V) (s : ℕ) :
    MvPolynomial V K →ₗ[K] MvPolynomial V K :=
  weightedHomogeneousComponent (fun v => if v ∈ C then 1 else 0) s

private theorem coordinateWeight (C : Finset V) (a : V →₀ ℕ) :
    Finsupp.weight (fun v => if v ∈ C then 1 else 0) a = coverWeight C a := by
  calc
    _ = ∑ v, if v ∈ C then a v else 0 := by
      simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_ite, mul_one, mul_zero, Nat.cast_id]
    _ = _ := by
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter, coverWeight] using
        (Finset.sum_filter (s := Finset.univ) (fun v => v ∈ C) (fun v => a v)).symm

@[simp] theorem coeff_coordinateComponent (C : Finset V) (s : ℕ)
    (f : MvPolynomial V K) (a : V →₀ ℕ) :
    (coordinateComponent C s f).coeff a =
      if coverWeight C a = s then f.coeff a else 0 := by
  rw [coordinateComponent, coeff_weightedHomogeneousComponent, coordinateWeight]

theorem coordinateComponent_zero_of_mem (C : Finset V) (s j : ℕ)
    (f : MvPolynomial V K) (hf : f ∈ coordinateIdeal C ^ s) (hj : j < s) :
    coordinateComponent C j f = 0 := by
  ext a
  rw [coeff_coordinateComponent]
  change (if coverWeight C a = j then f.coeff a else 0) = 0
  split_ifs with ha
  · by_contra h
    have hb := (mem_coordinateIdeal_power_iff C s f).mp hf a
      (MvPolynomial.mem_support_iff.mpr h)
    omega
  · rfl

/-- At the lowest possible degree, the product has just one homogeneous
convolution term. This identity is proved coefficient by coefficient. -/
theorem coordinateComponent_mul_of_mem (C : Finset V) (s : ℕ)
    (f g : MvPolynomial V K) (hf : f ∈ coordinateIdeal C ^ s) :
    coordinateComponent C s (f * g) =
      coordinateComponent C s f * coordinateComponent C 0 g := by
  ext a
  rw [coeff_coordinateComponent, coeff_mul, coeff_mul]
  by_cases ha : coverWeight C a = s
  · rw [if_pos ha]
    apply Finset.sum_congr rfl
    rintro ⟨b,c⟩ hbc
    have hbc' : b + c = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
    have hw := congrArg (coverWeight C) hbc'
    rw [coverWeight_add] at hw
    by_cases hfb : f.coeff b = 0
    · simp [coeff_coordinateComponent, hfb]
    · have hb := (mem_coordinateIdeal_power_iff C s f).mp hf b
        (MvPolynomial.mem_support_iff.mpr hfb)
      have hbs : coverWeight C b = s := by omega
      have hc : coverWeight C c = 0 := by omega
      simp only [coeff_coordinateComponent, hbs, hc, ite_true]
  · rw [if_neg ha]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨b,c⟩ hbc
    have hbc' : b + c = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
    have hw := congrArg (coverWeight C) hbc'
    rw [coverWeight_add] at hw
    by_cases hb : coverWeight C b = s
    · have hc : coverWeight C c ≠ 0 := by omega
      simp only [coeff_coordinateComponent, hb, ite_true, if_neg hc, mul_zero]
    · simp only [coeff_coordinateComponent, if_neg hb, zero_mul]

theorem coordinateComponent_zero_iff (C : Finset V) (f : MvPolynomial V K) :
    coordinateComponent C 0 f = 0 ↔ f ∈ coordinateIdeal C := by
  constructor
  · intro h
    rw [← pow_one (coordinateIdeal C), mem_coordinateIdeal_power_iff]
    intro a ha
    have hne := MvPolynomial.mem_support_iff.mp ha
    have hz := congrArg (fun p : MvPolynomial V K => p.coeff a) h
    rw [coeff_coordinateComponent] at hz
    change (if coverWeight C a = 0 then f.coeff a else 0) = 0 at hz
    by_contra hlt
    have he : coverWeight C a = 0 := by omega
    exact hne (by simpa only [he, ite_true] using hz)
  · intro hf
    apply coordinateComponent_zero_of_mem C 1 0 f _ (by omega)
    simpa only [pow_one] using hf

variable [IsDomain K]

/-- Multiplication by an element outside the coordinate ideal is
injective on the quotient by every power of that ideal. -/
theorem coordinateIdeal_power_saturated (C : Finset V) (s : ℕ)
    (f g : MvPolynomial V K) (hfg : f * g ∈ coordinateIdeal C ^ s)
    (hg : g ∉ coordinateIdeal C) : f ∈ coordinateIdeal C ^ s := by
  induction s with
  | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ s ih =>
      have hfgs : f * g ∈ coordinateIdeal C ^ s := by
        rw [mem_coordinateIdeal_power_iff] at hfg ⊢
        exact fun a ha => (Nat.le_succ s).trans (hfg a ha)
      have hfs := ih hfgs
      have hprod : coordinateComponent C s f * coordinateComponent C 0 g = 0 :=
        (coordinateComponent_mul_of_mem C s f g hfs).symm.trans
          (coordinateComponent_zero_of_mem C (s+1) s (f*g) hfg (by omega))
      have hgzero : coordinateComponent C 0 g ≠ 0 :=
        mt (coordinateComponent_zero_iff C g).mp hg
      have hfzero := (mul_eq_zero.mp hprod).resolve_right hgzero
      rw [mem_coordinateIdeal_power_iff]
      intro a ha
      have hb := (mem_coordinateIdeal_power_iff C s f).mp hfs a ha
      have hne : coverWeight C a ≠ s := by
        intro he
        have hz := congrArg (fun p : MvPolynomial V K => p.coeff a) hfzero
        rw [coeff_coordinateComponent] at hz
        change (if coverWeight C a = s then f.coeff a else 0) = 0 at hz
        exact (MvPolynomial.mem_support_iff.mp ha)
          (by simpa only [he, ite_true] using hz)
      omega

theorem coordinateIdeal_power_ne_top (C : Finset V) (s : ℕ) (hs : 0 < s) :
    coordinateIdeal (k := K) C ^ s ≠ ⊤ := by
  intro h
  have hone : (1 : MvPolynomial V K) ∈ coordinateIdeal C ^ s := by
    rw [h]
    exact Submodule.mem_top
  have hb := (mem_coordinateIdeal_power_iff C s (1 : MvPolynomial V K)).mp hone 0
    (by simp)
  simp only [coverWeight, Finsupp.zero_apply, Finset.sum_const_zero] at hb
  omega

/-- The positive powers appearing in the mixed intersection are actual
primary ideals, over every coefficient domain. -/
theorem coordinateIdeal_power_isPrimary (C : Finset V) (s : ℕ) (hs : 0 < s) :
    (coordinateIdeal (k := K) C ^ s).IsPrimary := by
  rw [Ideal.isPrimary_iff]
  refine ⟨coordinateIdeal_power_ne_top C s hs, ?_⟩
  intro f g hfg
  by_cases hg : g ∈ coordinateIdeal C
  · exact Or.inr (Ideal.mem_radical_iff.mpr ⟨s, Ideal.pow_mem_pow hg s⟩)
  · exact Or.inl (coordinateIdeal_power_saturated C s f g hfg hg)

theorem coordinateIdeal_isPrime (C : Finset V) :
    (coordinateIdeal (k := K) C).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · simpa only [pow_one] using coordinateIdeal_power_ne_top (K := K) C 1 (by omega)
  · intro f g hfg
    by_cases hg : g ∈ coordinateIdeal C
    · exact Or.inr hg
    · exact Or.inl (by
        simpa only [pow_one] using coordinateIdeal_power_saturated C 1 f g
          (by simpa only [pow_one] using hfg) hg)

theorem coordinateIdeal_power_radical (C : Finset V) (s : ℕ) (hs : 0 < s) :
    (coordinateIdeal (k := K) C ^ s).radical = coordinateIdeal C := by
  rw [Ideal.radical_pow (coordinateIdeal (k := K) C) (Nat.ne_of_gt hs)]
  exact (coordinateIdeal_isPrime C).radical

end FourPapers

end
end
end

end
