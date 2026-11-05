module

public import PaperVerification.PowerFischerPairing
public import PaperVerification.PowerConjugation

/-!
# Harmonic functionals on the actual joint-image quotient

The Fischer pairing descends through the literal original tail hit space.
This is the bridge from the resonant differential calculation to the
quotient; its nonzero functional is derived from pairing nondegeneracy.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module

namespace PaperVerification.PowerFischerPairing

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem originalTailHit_le_fischer_ker
    (α : K) (m : ℕ) (q : P)
    (hq : ∀ k : ℕ, m ≤ k → PowerHarmonicWitness.adjointOriginal α k q = 0) :
    PowerOperators.originalTailHit (fun _ => (1 : K)) α m ≤
      LinearMap.ker (fischer.flip q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, hk, p, rfl⟩
  change fischer (PowerOperators.original (fun _ => (1 : K)) α k p) q = 0
  rw [fischer_original, hq k hk, map_zero]

def harmonicQuotientFunctional
    (α : K) (m : ℕ) (q : P)
    (hq : ∀ k : ℕ, m ≤ k → PowerHarmonicWitness.adjointOriginal α k q = 0) :
    (P ⧸ PowerOperators.originalTailHit (fun _ => (1 : K)) α m) →ₗ[K] K :=
  (PowerOperators.originalTailHit (fun _ => (1 : K)) α m).liftQ
    (fischer.flip q) (originalTailHit_le_fischer_ker α m q hq)

@[simp] theorem harmonicQuotientFunctional_mkQ
    (α : K) (m : ℕ) (q : P)
    (hq : ∀ k : ℕ, m ≤ k → PowerHarmonicWitness.adjointOriginal α k q = 0)
    (p : P) :
    harmonicQuotientFunctional α m q hq
      ((PowerOperators.originalTailHit (fun _ => (1 : K)) α m).mkQ p) =
      fischer p q := rfl

theorem harmonicQuotientFunctional_ne_zero [CharZero K]
    (α : K) (m : ℕ) (q : P) (hqne : q ≠ 0)
    (hq : ∀ k : ℕ, m ≤ k → PowerHarmonicWitness.adjointOriginal α k q = 0) :
    harmonicQuotientFunctional α m q hq ≠ 0 := by
  intro hz
  apply hqne
  apply fischer_right_nondegenerate
  intro p
  have h := LinearMap.congr_fun hz
    ((PowerOperators.originalTailHit (fun _ => (1 : K)) α m).mkQ p)
  exact h

/-- Every exceptional witness produces a nonzero functional on the genuine
quotient. Its degree is retained by the orthogonality theorem, rather than
discarded in an ungraded dimension argument. -/
theorem resonant_harmonic_quotient_functional [CharZero K]
    (α : K) (m : ℕ) (hm : 0 < m) (a b : ι) (hab : a ≠ b) (q : ℕ)
    (hres : (Fintype.card ι : K) + α*(q+1 : ℕ) = 0) :
    ∃ f : (P ⧸ PowerOperators.originalTailHit (fun _ => (1 : K)) α m) →ₗ[K] K,
      f ≠ 0 ∧ ∀ p : P,
        f ((PowerOperators.originalTailHit (fun _ => (1 : K)) α m).mkQ p) =
          fischer p (PowerHarmonicWitness.harmonicWitness a b q) := by
  let w : P := PowerHarmonicWitness.harmonicWitness a b q
  have hw : ∀ k : ℕ, m ≤ k → PowerHarmonicWitness.adjointOriginal α k w = 0 :=
    fun k hk => PowerHarmonicWitness.harmonicWitness_all_adjoint_zero
      α a b q hres k (hm.trans_le hk)
  refine ⟨harmonicQuotientFunctional α m w hw, ?_, fun _ => rfl⟩
  exact harmonicQuotientFunctional_ne_zero α m w
    (PowerHarmonicWitness.harmonicWitness_ne_zero a b hab q) hw

end PaperVerification.PowerFischerPairing
