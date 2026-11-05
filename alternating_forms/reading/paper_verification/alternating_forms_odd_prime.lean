module

public import PaperVerification.AlternatingFormsOddStandardPieces
public import PaperVerification.AlternatingFormsOnePlane
public import PaperVerification.WeightedInitialPrime

/-!
# Primality of the actual odd common-isotropic Plücker ideal

The initial ideal is the actual prime Richardson ideal.  General weighted
descent therefore proves primality of the original ideal itself.  A concrete
lower-interval coordinate survives: its class is an actual degree-one standard
basis vector.  Thus the irrelevant ideal is not contained in the isotropy
ideal, which is the needed input to its projective saturation statement.

The chart isomorphisms by themselves would not exclude homogeneous torsion
supported at the irrelevant ideal.  This file supplies the missing global
algebraic input, without assuming primality or a projective coordinate-ring
identification as an application hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K] [CharZero K]

def oddLowerPluckerIndex (k s : ℕ) (hs : s≤k+1) : PluckerIndex s (2*k+1) :=
  ⟨oddIntervalLower k s hs,oddIntervalLower_strictMono k s hs⟩

def oddLowerChain (k s : ℕ) (hs : s≤k+1) :
    BandChain (oddIntervalLower k s hs) (oddIntervalUpper k s hs) 1 :=
  ⟨fun _ ↦ oddIntervalLower k s hs,
    (fun _ ↦ oddIntervalLower_strictMono k s hs),
    (fun _ i ↦ ⟨le_rfl,oddIntervalLower_le_upper k s hs i⟩),monotone_const⟩

theorem odd_lowerCoordinate_not_mem (k t : ℕ) (hs : t+2≤k+1) :
    X (oddLowerPluckerIndex k (t+2) hs)∉
      isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k) := by
  intro hmem
  have hne := (oddPluckerDegreeBasis (K := K) k t hs 1).ne_zero
    (oddLowerChain k (t+2) hs)
  apply hne
  apply Subtype.ext
  rw [oddPluckerDegreeBasis_apply]
  change Ideal.Quotient.mk _
    (chainPluckerProduct _ _ (oddLowerChain k (t+2) hs))=0
  simpa only [chainPluckerProduct,Fin.prod_univ_one,oddLowerChain,
    oddLowerPluckerIndex] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- Primality is proved for the literal original isotropy ideal. -/
theorem odd_isotropicPluckerIdeal_isPrime (k t : ℕ) (hs : t+2≤k+1) :
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime := by
  apply isPrime_of_initialIdeal_isPrime _ (pluckerVertexWeight (oddNatVertexWeight k))
  rw [odd_isotropic_initial_eq_interval k t hs]
  exact intervalPluckerIdeal_isPrime
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)

/-- The actual irrelevant ideal in the displayed Plücker polynomial ring. -/
def pluckerIrrelevantIdeal (s n : ℕ) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  Ideal.span (Set.range (X : PluckerIndex s n → MvPolynomial (PluckerIndex s n) K))

theorem odd_irrelevant_not_le (k t : ℕ) (hs : t+2≤k+1) :
    ¬pluckerIrrelevantIdeal (K := K) (t+2) (2*k+1)≤
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  intro h
  exact odd_lowerCoordinate_not_mem k t hs
    (h (Ideal.subset_span ⟨oddLowerPluckerIndex k (t+2) hs,rfl⟩))

theorem onePlane_ideal_isPrime (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsPrime :=
  RingHom.ker_isPrime _

theorem onePlane_irrelevant_not_le (k : ℕ) :
    ¬pluckerIrrelevantIdeal (K := K) 1 (2*k+1)≤matrixPluckerIdeal := by
  intro h
  have hx := h (Ideal.subset_span
    ⟨onePlaneIndex (0 : Fin (2*k+1)),rfl⟩)
  rw [onePlane_matrixPluckerIdeal] at hx
  exact X_ne_zero (onePlaneIndex (0 : Fin (2*k+1))) (Ideal.mem_bot.mp hx)

/-- The exact original homogeneous ideal is saturated against the full
irrelevant ideal, so its projective coordinate ring has no omitted torsion. -/
theorem odd_isotropicPluckerIdeal_saturated (k t : ℕ) (hs : t+2≤k+1) :
    IsSaturatedWithRespectTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerIrrelevantIdeal (t+2) (2*k+1)) :=
  isSaturatedWithRespectTo_of_isPrime _ _
    (odd_isotropicPluckerIdeal_isPrime k t hs) (odd_irrelevant_not_le k t hs)

theorem onePlane_PluckerIdeal_saturated (k : ℕ) :
    IsSaturatedWithRespectTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerIrrelevantIdeal 1 (2*k+1)) :=
  isSaturatedWithRespectTo_of_isPrime _ _
    (onePlane_ideal_isPrime (2*k+1)) (onePlane_irrelevant_not_le k)

end PaperVerification.AlternatingForms
