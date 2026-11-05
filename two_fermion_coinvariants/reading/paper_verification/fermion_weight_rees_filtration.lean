module

public import PaperVerification.FermionWeightRees
public import PaperVerification.FermionBlockNormalForm

/-!
# The Laurent coefficient characterization of the actual Rees algebra

Membership in the constructed algebra is equivalent to requiring the
coefficient of t^e to lie in filtration level max(-e,0). The reverse
inclusion is constructive: expand every actual Laurent coefficient in the
original basis and shift it by the nonnegative exponent e+w_i.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.WeightRees

open scoped BigOperators LaurentPolynomial PaperVerification.Fermion.WeightRees

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (weight : I → ℕ)

def CoefficientBound (z : LaurentPolynomial A) : Prop :=
  ∀ e i,b.repr (z.coeff e) i≠0 → -(weight i : ℤ)≤e

theorem coefficientBound_zero : CoefficientBound b weight (0 : LaurentPolynomial A) := by
  intro e i hi
  exact (hi (by simp)).elim

theorem coefficientBound_add {x y : LaurentPolynomial A}
    (hx : CoefficientBound b weight x) (hy : CoefficientBound b weight y) :
    CoefficientBound b weight (x+y) := by
  intro e i hi
  by_cases hxi : b.repr (x.coeff e) i=0
  · apply hy e i
    simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,map_add,Finsupp.add_apply,
      hxi,zero_add] using hi
  · exact hx e i hxi

theorem coefficientBound_monomial_smul_shifted (r : ℕ) (c : K) (i : I) :
    CoefficientBound b weight ((Polynomial.monomial r c) • shiftedBasisVector b weight i) := by
  classical
  rw [monomial_smul_shifted]
  intro e j hj
  rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply] at hj
  by_cases he : (r : ℤ)-(weight i : ℤ)=e
  · rw [if_pos he] at hj
    by_cases hji : j=i
    · subst j
      omega
    · exact (hj (by simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hji,smul_zero])).elim
  · rw [if_neg he,map_zero,Finsupp.zero_apply] at hj
    exact (hj rfl).elim

theorem coefficientBound_smul_shifted (p : Polynomial K) (i : I) :
    CoefficientBound b weight (p • shiftedBasisVector b weight i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_smul]; exact coefficientBound_add b weight hp hq
  | monomial r c => exact coefficientBound_monomial_smul_shifted b weight r c i

theorem coefficientBound_of_mem_span (z : LaurentPolynomial A) (hz : z∈span b weight) :
    CoefficientBound b weight z := by
  have H : ∀ p : Polynomial K,CoefficientBound b weight (p • z) := by
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨i,rfl⟩ := hx; exact fun p ↦ coefficientBound_smul_shifted b weight p i
    | zero => intro p; simpa only [smul_zero] using coefficientBound_zero b weight
    | add x y hx hy ihx ihy =>
        intro p
        rw [smul_add]
        exact coefficientBound_add b weight (ihx p) (ihy p)
    | smul c x hx ih =>
        intro p
        simpa only [mul_smul] using ih (p*c)
  simpa only [one_smul] using H 1

theorem mem_span_of_coefficientBound (z : LaurentPolynomial A)
    (hz : CoefficientBound b weight z) : z∈span b weight := by
  classical
  rw [←AddMonoidAlgebra.sum_coeff_single z]
  change (∑ e∈z.coeff.support,AddMonoidAlgebra.single e (z.coeff e))∈span b weight
  apply Submodule.sum_mem
  intro e he
  change (AddMonoidAlgebra.lsingle (R := K) e) (z.coeff e)∈span b weight
  rw [←b.sum_repr (z.coeff e),map_sum]
  apply Submodule.sum_mem
  intro i hi
  change AddMonoidAlgebra.single e ((b.repr (z.coeff e) i) • b i)∈span b weight
  by_cases hc : b.repr (z.coeff e) i=0
  · simpa only [hc,zero_smul,AddMonoidAlgebra.single_zero] using (span b weight).zero_mem
  · have hw := hz e i hc
    have hn : 0≤e+(weight i : ℤ) := by omega
    have hexp : (((e+(weight i : ℤ)).toNat : ℕ) : ℤ)-(weight i : ℤ)=e := by
      rw [Int.toNat_of_nonneg hn]
      omega
    have hterm := (span b weight).smul_mem
      (Polynomial.monomial (e+(weight i : ℤ)).toNat (b.repr (z.coeff e) i))
      (Submodule.subset_span ⟨i,rfl⟩)
    rw [monomial_smul_shifted,hexp] at hterm
    exact hterm

theorem mem_span_iff_coefficientBound (z : LaurentPolynomial A) :
    z∈span b weight ↔ CoefficientBound b weight z :=
  ⟨coefficientBound_of_mem_span b weight z,mem_span_of_coefficientBound b weight z⟩

/-- The intrinsic Laurent Rees condition for the descending basis filtration. -/
theorem mem_algebra_iff_filtration (hmul : Multiplicative b weight) (z : LaurentPolynomial A) :
    z∈algebra b weight hmul ↔
      ∀ e,z.coeff e∈BlockInitial.lowerSubmodule b weight (-e).toNat := by
  change z∈span b weight ↔ _
  rw [mem_span_iff_coefficientBound]
  change (∀ e i,b.repr (z.coeff e) i≠0 → -(weight i : ℤ)≤e) ↔
    ∀ e i,b.repr (z.coeff e) i≠0 → (-e).toNat≤weight i
  constructor <;> intro h e i hi <;> have hh := h e i hi <;> omega

end PaperVerification.Fermion.WeightRees
