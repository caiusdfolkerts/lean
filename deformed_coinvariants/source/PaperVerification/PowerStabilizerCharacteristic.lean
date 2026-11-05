module

public import PaperVerification.PowerParameters
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.CharP.Defs

/-!
# Nonresonance makes the coefficient stabilizer order invertible

The arbitrary-field equivariance assertion in Theorem 2.2 does not require
an additional Maschke hypothesis. In positive characteristic, nonresonance
forbids every zero subset sum. A permutation of prime order preserving the
coefficients would have a nontrivial cycle of that prime length, giving just
such a zero subset sum. Cauchy's theorem therefore excludes divisibility
of the stabilizer order by the characteristic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K ι : Type*} [Field K]

/-- In characteristic `p>0`, the unbounded parameter condition already
excludes every vanishing nonempty subset sum, by testing a large multiple
of the characteristic. -/
theorem Nonresonant.subset_sum_ne_zero_charP
    {c : ι → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (p : ℕ) [CharP K p] (hp : 0 < p) (I : Finset ι) (hI : I.Nonempty) :
    (∑ i ∈ I, c i) ≠ 0 := by
  intro hz
  have hs : m * I.card ≤ (m * I.card) * p := by
    calc
      m * I.card = (m * I.card) * 1 := (Nat.mul_one _).symm
      _ ≤ (m * I.card) * p := Nat.mul_le_mul_left _ hp
  apply hnr I hI ((m * I.card) * p) hs
  simp only [hz, Nat.cast_mul, CharP.cast_eq_zero, mul_zero, add_zero]

section FiniteStabilizer

variable [Fintype ι]
local instance stabilizerDecidableEq : DecidableEq ι := Classical.decEq ι

/-- A nontrivial cycle of a prime-order permutation has exactly that
prime length. The support here is the actual support of `cycleOf`. -/
theorem prime_order_cycle_card (σ : Equiv.Perm ι) (p : ℕ) (hp : p.Prime)
    (hσ : orderOf σ = p) (i : ι) (hi : σ i ≠ i) :
    (σ.cycleOf i).support.card = p := by
  have hc := Equiv.Perm.isCycle_cycleOf σ hi
  have hd := Equiv.Perm.orderOf_cycleOf_dvd_orderOf σ i
  rw [hσ] at hd
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · have htwo := hc.two_le_card_support
    rw [← hc.orderOf, h] at htwo
    omega
  · exact hc.orderOf.symm.trans h

/-- The prime characteristic cannot divide the order of any permutation
subgroup preserving the actual coefficient tuple. -/
theorem Nonresonant.not_dvd_stabilizer_card_charP
    {c : ι → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm ι))
    (hfix : ∀ g : G, ∀ i : ι, c ((g : Equiv.Perm ι) i) = c i)
    (p : ℕ) [Fact p.Prime] [CharP K p] : ¬p ∣ Nat.card G := by
  classical
  intro hdiv
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdiv
  let σ : Equiv.Perm ι := g
  have hσ : orderOf σ = p :=
    (orderOf_injective G.subtype Subtype.coe_injective g).trans hg
  have hσne : σ ≠ 1 := by
    intro heq
    have horder : orderOf σ = 1 := by rw [heq, orderOf_one]
    exact (Fact.out : p.Prime).ne_one (hσ.symm.trans horder)
  obtain ⟨i, hi⟩ : ∃ i : ι, σ i ≠ i := by
    by_contra! h
    exact hσne (Equiv.ext h)
  let I := (σ.cycleOf i).support
  have hI : I.Nonempty := Equiv.Perm.support_cycleOf_nonempty.mpr hi
  have hcard : I.card = p := prime_order_cycle_card σ p Fact.out hσ i hi
  have hequal : ∀ j ∈ I, c j = c i := by
    intro j hj
    obtain ⟨z, hz⟩ := ((Equiv.Perm.mem_support_cycleOf_iff' hi).mp hj : σ.SameCycle i j)
    rw [← hz]
    simpa only [σ, Subgroup.coe_zpow] using hfix (g ^ z) i
  have hsum : (∑ j ∈ I, c j) = 0 := by
    rw [Finset.sum_congr rfl hequal, Finset.sum_const, nsmul_eq_mul, hcard,
      CharP.cast_eq_zero, zero_mul]
  exact (hnr.subset_sum_ne_zero_charP p (Fact.out : p.Prime).pos I hI) hsum

/-- The coefficient-stabilizing subgroup automatically satisfies the exact
order-invertibility hypothesis for Maschke's theorem, over every field. -/
theorem Nonresonant.isUnit_stabilizer_card
    {c : ι → K} {lam : K} {m : ℕ} (hnr : Nonresonant c lam m)
    (G : Subgroup (Equiv.Perm ι))
    (hfix : ∀ g : G, ∀ i : ι, c ((g : Equiv.Perm ι) i) = c i) :
    IsUnit (Nat.card G : K) := by
  rcases CharP.exists' K with hzero | ⟨p, hp, hchar⟩
  · letI : CharZero K := hzero
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos))
  · letI : Fact p.Prime := hp
    letI : CharP K p := hchar
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact (hnr.not_dvd_stabilizer_card_charP G hfix p)
      ((CharP.cast_eq_zero_iff K p (Nat.card G)).mp hz)

end FiniteStabilizer

end PaperVerification.PowerOperators
