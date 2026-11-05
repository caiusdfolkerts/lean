module

public import PaperVerification.EulerJacobian
public import Mathlib.Analysis.Complex.Basic

/-!
# The exact exceptional set in the weighted Jacobian theorem

The paper uses degrees whose homogeneous polynomial space is nonzero.
This file relates that definition to the monomial eigenvalues used by the
Euler reduction, and states the equality with precisely the paper's excluded
parameters.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace PaperVerification.EulerJacobian

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The degrees of nonzero homogeneous polynomials, namely the paper's set `S`. -/
def occurringDegrees (w : ι → ℕ) : Set ℕ :=
  {d | ∃ f : MvPolynomial ι K, f ≠ 0 ∧ f.IsWeightedHomogeneous w d}

theorem monomialWeight_eq_weight (w : ι → ℕ) (a : ι →₀ ℕ) :
    monomialWeight w a = Finsupp.weight w a := by
  simp only [monomialWeight, Finsupp.weight_eq_sum, smul_eq_mul, mul_comm]

/-- A homogeneous piece is nonzero exactly when a monomial of its degree exists. -/
theorem mem_occurringDegrees_iff (w : ι → ℕ) (d : ℕ) :
    d ∈ occurringDegrees (K := K) w ↔ ∃ a : ι →₀ ℕ, monomialWeight w a = d := by
  classical
  constructor
  · rintro ⟨f, hf, hhom⟩
    obtain ⟨a, ha⟩ := MvPolynomial.exists_coeff_ne_zero hf
    exact ⟨a, (monomialWeight_eq_weight w a).trans (hhom ha)⟩
  · rintro ⟨a, ha⟩
    refine ⟨monomial a 1, ?_, isWeightedHomogeneous_monomial w a 1 ?_⟩
    · intro hz
      have hc := congrArg (fun f : MvPolynomial ι K => f.coeff a) hz
      simpa [MvPolynomial.coeff_monomial] using hc
    · exact (monomialWeight_eq_weight w a).symm.trans ha

theorem weight_sum_pos [Nonempty ι] (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    0 < ∑ i, w i := by
  classical
  exact Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty

/-- The excluded fraction is equivalent to the vanishing of the Euler scalar. -/
theorem eigenvalue_zero_iff [CharZero K] [Nonempty ι]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (h d : ℕ) (t : K) :
    (h : K) + t * ((∑ i, w i : ℕ) + d : K) = 0 ↔
      t = -(h : K) / ((∑ i, w i : ℕ) + d : K) := by
  have hn : (∑ i, w i : ℕ) + d ≠ 0 := Nat.ne_of_gt
    (Nat.add_pos_left (weight_sum_pos w hw) d)
  have hden : ((∑ i, w i : ℕ) + d : K) ≠ 0 := by
    exact_mod_cast hn
  rw [eq_div_iff hden]
  constructor
  · intro he
    calc
      t * ((∑ i, w i : ℕ) + d : K) =
          ((h : K) + t * ((∑ i, w i : ℕ) + d : K)) - h := by ring
      _ = -(h : K) := by rw [he]; simp
  · intro he
    rw [he, add_neg_cancel]

/-- This equivalence checks the complete quantifier range in the paper's condition. -/
theorem nonresonance_iff [CharZero K] [Nonempty ι]
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) (h : ℕ) (t : K) :
    (∀ d ∈ occurringDegrees (K := K) w,
      t ≠ -(h : K) / ((∑ i, w i : ℕ) + d : K)) ↔
    (∀ a : ι →₀ ℕ,
      (h : K) + t * ((∑ i, w i : ℕ) + monomialWeight w a : K) ≠ 0) := by
  constructor
  · intro hnr a hz
    exact hnr (monomialWeight w a)
      ((mem_occurringDegrees_iff w _).mpr ⟨a, rfl⟩)
      ((eigenvalue_zero_iff w hw h _ t).mp hz)
  · intro hnr d hd he
    obtain ⟨a, ha⟩ := (mem_occurringDegrees_iff w d).mp hd
    apply hnr a
    rw [ha]
    exact (eigenvalue_zero_iff w hw h d t).mpr he

/-- Theorem 6.2 with the exact exceptional-set formulation of the paper.
It holds over every characteristic-zero field, hence in particular over `ℂ`. -/
theorem jacobian_hit_eq_of_nonresonant [CharZero K] [Nonempty ι]
    (F : MvPolynomial ι K) (t : K) (w : ι → ℕ) (h : ℕ)
    (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h)
    (hnr : ∀ d ∈ occurringDegrees (K := K) w,
      t ≠ -(h : K) / ((∑ i, w i : ℕ) + d : K)) :
    hit (fun i => pderiv i F) F t =
      (coefficientIdeal (fun i => pderiv i F)).restrictScalars K :=
  jacobian_hit_eq F t w h hh hF ((nonresonance_iff w hw h t).mp hnr)

/-- A nonzero polynomial of positive weighted degree requires at least one variable. -/
theorem nonempty_of_positive_degree (F : MvPolynomial ι K) (w : ι → ℕ) (h : ℕ)
    (hne : F ≠ 0) (hh : 0 < h) (hF : F.IsWeightedHomogeneous w h) : Nonempty ι := by
  classical
  obtain ⟨a, ha⟩ := MvPolynomial.exists_coeff_ne_zero hne
  by_contra hn
  letI : IsEmpty ι := ⟨fun i => hn ⟨i⟩⟩
  have hz : Finsupp.weight w a = 0 := by simp [Finsupp.weight_eq_sum]
  exact (Nat.ne_of_gt hh) ((hF ha).symm.trans hz)

/-- The exact complex-polynomial statement of Theorem 6.2, including all variable
counts; the positive-degree hypothesis itself excludes the empty variable set. -/
theorem paper_theorem_6_2 (N : ℕ) (F : MvPolynomial (Fin N) ℂ)
    (t : ℂ) (w : Fin N → ℕ) (h : ℕ)
    (hne : F ≠ 0) (hw : ∀ i, 0 < w i) (hh : 0 < h)
    (hF : F.IsWeightedHomogeneous w h)
    (hnr : ∀ d ∈ occurringDegrees (K := ℂ) w,
      t ≠ -(h : ℂ) / ((∑ i, w i : ℕ) + d : ℂ)) :
    hit (fun i => pderiv i F) F t =
      (coefficientIdeal (fun i => pderiv i F)).restrictScalars ℂ := by
  letI : Nonempty (Fin N) := nonempty_of_positive_degree F w h hne hh hF
  exact jacobian_hit_eq_of_nonresonant F t w h hw hh hF hnr

end PaperVerification.EulerJacobian
