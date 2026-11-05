module

public import PaperVerification.AlternatingFormsFrobeniusDimension
public import PaperVerification.AlternatingFormsMatchingInjectivity
public import PaperVerification.AlternatingFormsStripWalks
public import Mathlib.Algebra.Ring.Parity

/-!
# The complete characteristic-p excess theorem

This file joins the actual exterior-algebra and actual bounded-walk chains.
It retains every prime and every odd dimension in the printed range. The
all-odd-dimension statement uses the ordinary vector space `Fin n → K` and
explicitly transported integer indices; the index transport changes no
coordinate value. No rank, nilpotence, projection, or walk formula is an
additional hypothesis of the principal statement.

All new declarations remain candidates until the recorded fresh compiler
run, actual proof-body audit, and independent statement review succeed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The full integer lower bound for the canonical odd pencil, now with
matching injectivity proved rather than assumed. -/
theorem oddPath_quotient_excess_charP [FiniteDimensional K M] {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    ((2*k+1).choose (2*p) : ℤ) - 2*((2*k+1).choose (2*p-2) : ℤ) +
      ((2*k+1).choose (2*p-4) : ℤ) + 2 ≤
      (Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) : ℤ) :=
  oddPath_quotient_excess_of_injective b p hk
    (oddPath_first_low_degree_injective b p hk)

/-- The exact walk-count version for the parameterization `n=2k+1`. -/
theorem oddPath_quotient_excess_walks [FiniteDimensional K M] {k : ℕ}
    (b : Module.Basis (Fin (2*k+1)) K M)
    (p : ℕ) [Fact p.Prime] [CharP K p] (hk : 3*p-2 ≤ k) :
    StripWalks.paperWalkCount (2*k+1) (2*p) + 2 ≤
      Module.finrank K (ExteriorQuotientDegree
        (oddPathFirstQuadratic (K := K) b) (oddPathSecondQuadratic (K := K) b) (2*p)) := by
  have hp := (Fact.out : p.Prime).two_le
  have hdim := oddPath_quotient_excess_charP b p hk
  have hwalk := StripWalks.high_strip_count (2*k+1) (2*p)
    (by omega : 4 ≤ 2*p) (by omega : 3*(2*p)-3 ≤ 2*k+1)
  rw [← hwalk] at hdim
  exact_mod_cast hdim

/-- The half-dimension parameterization covers every odd natural dimension. -/
theorem odd_half_dimension {n : ℕ} (hn : Odd n) : 2*(n/2)+1 = n := by
  obtain ⟨k, hk⟩ := hn.exists_bit1
  omega

/-- The coordinate index transport has exactly the original natural value. -/
def canonicalOddIndex {n : ℕ} (hn : Odd n) : Fin (2*(n/2)+1) → Fin n :=
  Fin.cast (odd_half_dimension hn)

@[simp] theorem canonicalOddIndex_val {n : ℕ} (hn : Odd n)
    (i : Fin (2*(n/2)+1)) : (canonicalOddIndex hn i).val = i.val := rfl

/-- The literal first canonical matching in an arbitrary odd dimension:
its summands use zero-based indices `2i,2i+1`. -/
def canonicalOddFirst {n : ℕ} (hn : Odd n) (b : Module.Basis (Fin n) K M) :
    ⋀[K]^2 M :=
  oddPathFirstQuadratic (fun i => b (canonicalOddIndex hn i))

/-- The literal second canonical matching, with zero-based indices
`2i+1,2i+2`, in the same actual vector space. -/
def canonicalOddSecond {n : ℕ} (hn : Odd n) (b : Module.Basis (Fin n) K M) :
    ⋀[K]^2 M :=
  oddPathSecondQuadratic (fun i => b (canonicalOddIndex hn i))

/-- Basis transport identifies the arbitrary-odd-dimensional canonical
forms with the `2k+1` forms without changing any vector or coefficient. -/
theorem canonicalOdd_reindex_forms {n : ℕ} (hn : Odd n)
    (b : Module.Basis (Fin n) K M) :
    let b' := b.reindex (finCongr (odd_half_dimension hn)).symm
    oddPathFirstQuadratic (K := K) b' = canonicalOddFirst hn b ∧
    oddPathSecondQuadratic (K := K) b' = canonicalOddSecond hn b := by
  dsimp only
  have hb : (b.reindex (finCongr (odd_half_dimension hn)).symm :
      Fin (2*(n/2)+1) → M) = fun i => b (canonicalOddIndex hn i) := by
    funext i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm]
    rfl
  rw [hb]
  exact ⟨rfl, rfl⟩

/-- Theorem 7.2, in every odd dimension and every prime characteristic.
The quotient and the bounded-path walk count have their actual mathematical
definitions. Algebraic closure is unnecessary for this stronger statement. -/
theorem paper_theorem_7_2
    (p n : ℕ) [Fact p.Prime] [CharP K p] (hn : Odd n) (hlarge : 6*p-3 ≤ n) :
    StripWalks.paperWalkCount n (2*p) + 2 ≤
      Module.finrank K
        (ExteriorQuotientDegree
          (canonicalOddFirst hn (Pi.basisFun K (Fin n)))
          (canonicalOddSecond hn (Pi.basisFun K (Fin n))) (2*p)) := by
  let b := Pi.basisFun K (Fin n)
  let b' := b.reindex (finCongr (odd_half_dimension hn)).symm
  have hp := (Fact.out : p.Prime).two_le
  have hk : 3*p-2 ≤ n/2 := by
    have hhalf := odd_half_dimension hn
    omega
  have h := oddPath_quotient_excess_walks b' p hk
  obtain ⟨hf, hg⟩ := canonicalOdd_reindex_forms hn b
  change oddPathFirstQuadratic (K := K) b' = canonicalOddFirst hn b at hf
  change oddPathSecondQuadratic (K := K) b' = canonicalOddSecond hn b at hg
  rw [hf, hg, odd_half_dimension hn] at h
  exact h

end PaperVerification.AlternatingForms
