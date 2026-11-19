module

public import PaperVerification.AlternatingFormsChernDescent
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous
import Lean.Elab.Tactic.Omega

/-!
# Weighted degrees of the Chern relations

The coefficient variable `cᵢ` has weight `i`, while each root variable has weight
one.  The elementary substitution intertwines those two gradings and is
injective.  Therefore the homogeneous root relation of degree `n` descends to
a polynomial of weighted degree exactly `n`.  This is the grading needed for
the complete-intersection assertion, and also proves that every positive-degree
relation vanishes at the origin.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset

variable {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]

theorem squareSubstitution_isHomogeneous {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) : (squareSubstitution p).IsHomogeneous (2 * n) := by
  exact hp.aeval _ fun i => MvPolynomial.isHomogeneous_X_pow i 2

/-- Both parity families have the claimed degree in the actual root variables. -/
theorem chernRootRelationPolynomial_isHomogeneous (n : ℕ) :
    (chernRootRelationPolynomial (K := K) (σ := σ) n).IsHomogeneous n := by
  unfold chernRootRelationPolynomial
  split_ifs with heven
  · have h := squareSubstitution_isHomogeneous
      (MvPolynomial.isHomogeneous_hsymm (σ := σ) (R := K) (n / 2))
    convert h using 1
    obtain ⟨m, hm⟩ := heven
    omega
  · apply MvPolynomial.IsHomogeneous.sum
    intro i _
    have h := (MvPolynomial.isHomogeneous_X K i).mul
      (squareSubstitution_isHomogeneous
        ((MvPolynomial.isHomogeneous_hsymm (σ := σ) (R := K) ((n + 1) / 2)).pderiv
          (i := i)))
    convert h using 1
    have hodd : n % 2 = 1 := by
      rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at heven
      omega
    omega

/-- Positive weights on the coefficient variables, indexed starting at zero. -/
def chernCoefficientWeight {s : ℕ} (i : Fin s) : ℕ := i.val + 1

@[simp] theorem chernCoefficientWeight_ne_zero {s : ℕ} (i : Fin s) :
    chernCoefficientWeight i ≠ 0 := Nat.succ_ne_zero _

/-- The elementary substitution, viewed in the full polynomial ring. -/
noncomputable def elementarySubstitution (s : ℕ) :
    MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin s) K :=
  MvPolynomial.aeval fun i => MvPolynomial.esymm (Fin s) K (i.val + 1)

theorem elementarySubstitution_injective (s : ℕ) :
    Function.Injective (elementarySubstitution (K := K) s) := by
  intro p q h
  apply MvPolynomial.esymmAlgHom_injective K (by simp : s ≤ Fintype.card (Fin s))
  apply Subtype.ext
  simpa only [MvPolynomial.esymmAlgHom_apply, elementarySubstitution] using h

theorem elementarySubstitution_monomial_isHomogeneous {s : ℕ}
    (d : Fin s →₀ ℕ) (r : K) :
    (elementarySubstitution s (MvPolynomial.monomial d r)).IsHomogeneous
      (Finsupp.weight chernCoefficientWeight d) := by
  rw [elementarySubstitution, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have h := MvPolynomial.IsHomogeneous.prod d.support
    (fun i => MvPolynomial.esymm (Fin s) K (i.val + 1) ^ d i)
    (fun i => (i.val + 1) * d i)
    (fun i _ => (MvPolynomial.isHomogeneous_esymm (σ := Fin s) (R := K)
      (i.val + 1)).pow (d i))
  convert h.C_mul r using 1 <;>
    simp [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, chernCoefficientWeight,
      smul_eq_mul, mul_comm]

/-- The grading comparison is an equality of actual homogeneous projections. -/
theorem elementarySubstitution_weightedHomogeneousComponent {s : ℕ}
    (p : MvPolynomial (Fin s) K) (n : ℕ) :
    MvPolynomial.homogeneousComponent n (elementarySubstitution s p) =
      elementarySubstitution s
        (MvPolynomial.weightedHomogeneousComponent chernCoefficientWeight n p) := by
  classical
  calc
    _ = MvPolynomial.homogeneousComponent n
        (elementarySubstitution s
          (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d))) :=
      congrArg (fun q => MvPolynomial.homogeneousComponent n (elementarySubstitution s q))
        p.as_sum
    _ = ∑ d ∈ p.support, MvPolynomial.homogeneousComponent n
        (elementarySubstitution s (MvPolynomial.monomial d (p.coeff d))) := by
      simp only [map_sum]
    _ = _ := by
      rw [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.homogeneousComponent_of_mem
        (elementarySubstitution_monomial_isHomogeneous d (p.coeff d))]
      by_cases h : Finsupp.weight chernCoefficientWeight d = n
      · simp [h]
      · simp [h, Ne.symm h]

/-- Injectivity of elementary substitution reflects the full weighted grading. -/
theorem isWeightedHomogeneous_of_elementarySubstitution {s : ℕ}
    (p : MvPolynomial (Fin s) K) {n : ℕ}
    (hp : (elementarySubstitution s p).IsHomogeneous n) :
    p.IsWeightedHomogeneous chernCoefficientWeight n := by
  have heq : MvPolynomial.weightedHomogeneousComponent chernCoefficientWeight n p = p := by
    apply elementarySubstitution_injective s
    rw [← elementarySubstitution_weightedHomogeneousComponent,
      MvPolynomial.homogeneousComponent_eq_self hp]
  rw [← heq]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n p

/-- The precise weighted degree of each descended relation. -/
theorem chernCoefficientRelation_isWeightedHomogeneous (s n : ℕ) :
    (chernCoefficientRelation (K := K) s n).IsWeightedHomogeneous
      chernCoefficientWeight n := by
  apply isWeightedHomogeneous_of_elementarySubstitution
  rw [elementarySubstitution, chernCoefficientRelation_substitution]
  exact chernRootRelationPolynomial_isHomogeneous n

/-- Positive-degree relations lie in the actual maximal ideal of the origin. -/
theorem chernCoefficientRelation_constantCoeff (s n : ℕ) (hn : n ≠ 0) :
    MvPolynomial.constantCoeff (chernCoefficientRelation (K := K) s n) = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  apply (chernCoefficientRelation_isWeightedHomogeneous s n).coeff_eq_zero 0
  simpa using hn.symm

end PaperVerification.AlternatingForms
