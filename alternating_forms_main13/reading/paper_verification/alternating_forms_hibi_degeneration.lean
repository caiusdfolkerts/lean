module

public import PaperVerification.AlternatingFormsGoodPresentation
public import PaperVerification.WeightedSagbiSubstitution
public import PaperVerification.WeightedInitialFlat
public import PaperVerification.WeightedInitialGeneralFiber

/-!
# The actual Richardson-to-Hibi weighted degeneration

The source has exactly the good Plücker variables, and its ideal is the
literal band-minor kernel. Distinct diagonal leading monomials in the full
standard basis establish the entire initial-kernel equality. The special
fiber is consequently the actual Hibi binomial quotient, and every nonzero
fiber is the actual Richardson ring. This uses the concrete Rees image and
its proved flatness, rather than an abstract degeneration assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.Hibi

open MvPolynomial
open scoped BigOperators
open WeightedInitialFiber WeightedSagbi

variable {K : Type*} [Field K] [CharZero K] {s n : ℕ}
  (α β : Fin s → Fin n)

def diagonalEntryWeight (i : Fin s × Fin n) : ℕ := i.1.val*i.2.val

def diagonalExponent (I : IntervalIndex α β) : (Fin s × Fin n) →₀ ℕ :=
  minorTermExponent I.val.val 1

def diagonalWeight : IntervalIndex α β → ℕ :=
  inducedWeight (diagonalEntryWeight (s := s) (n := n)) (diagonalExponent α β)

def standardDiagonalWeight (C : Σ r,BandChain α β r) : ℕ :=
  ∑ j,diagonalWeight α β (intervalIndexOfChain α β C.2 j)

theorem diagonalEntryWeight_cast :
    (fun i : Fin s × Fin n => (diagonalEntryWeight i : ℤ))=bandEntryWeight s n := by
  funext i
  simp only [diagonalEntryWeight,bandEntryWeight,Nat.cast_mul]

theorem standardPolynomial_diagonal_homogeneous (C : Σ r,BandChain α β r) :
    (standardPolynomial (K := K) α β C.2).IsWeightedHomogeneous
      (diagonalWeight α β) (standardDiagonalWeight α β C) := by
  apply IsWeightedHomogeneous.prod Finset.univ
  intro j hj
  exact isWeightedHomogeneous_X _ _ _

theorem chainDiagonalExponent_weight (C : Σ r,BandChain α β r) :
    Finsupp.weight (diagonalEntryWeight (s := s) (n := n)) (chainDiagonalExponent C.2.val)=
      standardDiagonalWeight α β C := by
  simp only [chainDiagonalExponent,chainTermExponent,map_sum,standardDiagonalWeight,
    diagonalWeight,inducedWeight,diagonalExponent,intervalIndexOfChain]

theorem bandMinor_diagonal_weightMonic (I : IntervalIndex α β) :
    IsWeightMonic (fun i => (diagonalEntryWeight i : ℤ))
      (bandMinor (K := K) α β I.val.val) (diagonalExponent α β I) := by
  rw [diagonalEntryWeight_cast]
  exact bandMinor_weightMonic α β I.val.val I.val.property I.property

set_option maxHeartbeats 800000 in
theorem goodBandInitial_eq_hibi (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    initialIdeal (goodBandIdeal (K := K) α β) (diagonalWeight α β)=relationIdeal α β := by
  rw [relationIdeal_eq_kernel α β hs]
  apply initial_kernel_eq (K := K) (diagonalWeight α β) diagonalEntryWeight
    (goodBandMap α β) (diagonalMap α β)
    (fun C : Σ r,BandChain α β r => standardPolynomial α β C.2)
    (standardDiagonalWeight α β) (fun C => chainDiagonalExponent C.2.val)
    (allChainDiagonalExponent_injective α β hs)
    (standardPolynomial_diagonal_homogeneous α β)
  · intro C
    rw [goodBandMap_standardPolynomial,diagonalEntryWeight_cast]
    exact bandStandardProduct_weightMonic α β C.2
  · exact chainDiagonalExponent_weight α β
  · exact goodBandMap_mem_standardSpan (K := K) α β hα hβ
  · intro p d hp
    exact substitution_bound (K := K) (diagonalEntryWeight (s := s) (n := n))
      (fun I : IntervalIndex α β => bandMinor (K := K) α β I.val.val)
      (diagonalExponent α β) (bandMinor_diagonal_weightMonic (K := K) α β) p d hp
  · intro p d hp
    exact substitution_top (K := K) (diagonalEntryWeight (s := s) (n := n))
      (fun I : IntervalIndex α β => bandMinor (K := K) α β I.val.val)
      (diagonalExponent α β) (bandMinor_diagonal_weightMonic (K := K) α β) p d hp
  · intro p d
    exact monomialSubstitution_graded (K := K)
      (diagonalEntryWeight (s := s) (n := n)) (diagonalExponent α β) p d

/-- The special fiber is the literal binomial Hibi quotient. -/
def hibiSpecialFiberEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    ZeroFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) ≃ₐ[K]
      (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β) :=
  (initialQuotientEquiv (goodBandIdeal α β) (diagonalWeight α β)).symm.trans
    (Ideal.quotientEquivAlgOfEq K (goodBandInitial_eq_hibi α β hα hβ hs))

def hibiNonzeroFiberEquiv (hα : Monotone α) (hβ : Monotone β) (hs : 0<s)
    (c : K) (hc : c≠0) :
    ParameterFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β) :=
  (nonzeroFiberEquiv (goodBandIdeal α β) (diagonalWeight α β) c hc).trans
    (goodBandQuotientEquiv α β hα hβ hs)

/-- The actual flat family, with every fiber identified in the original
presentations. Positive row count is the only size condition. -/
theorem richardson_hibi_flat_family (hα : Monotone α) (hβ : Monotone β) (hs : 0<s) :
    Module.Flat (Polynomial K)
      (reesAlgebra (goodBandIdeal (K := K) α β) (diagonalWeight α β)) ∧
    Nonempty (ZeroFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) ≃ₐ[K]
      (MvPolynomial (IntervalIndex α β) K⧸relationIdeal α β)) ∧
    ∀ c : K,c≠0 → Nonempty
      (ParameterFiber (goodBandIdeal (K := K) α β) (diagonalWeight α β) c ≃ₐ[K]
        (MvPolynomial (PluckerIndex s n) K⧸intervalPluckerIdeal α β)) :=
  ⟨inferInstance,⟨hibiSpecialFiberEquiv α β hα hβ hs⟩,
    fun c hc => ⟨hibiNonzeroFiberEquiv α β hα hβ hs c hc⟩⟩

end PaperVerification.AlternatingForms.Hibi
