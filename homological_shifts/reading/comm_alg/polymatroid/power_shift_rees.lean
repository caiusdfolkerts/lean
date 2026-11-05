import CommAlg.Polymatroid.PowerShiftInterval
import Mathlib.RingTheory.ReesAlgebra

/-!
# The actual power-shift Rees ideal and its minimal monomials

The degree-zero component is zero, as in the module in Theorem 4.4.
Minimality means divisibility by another module monomial through a monomial
of the genuine Rees algebra. This includes degree-zero polynomial factors.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

def powerShiftPiece (ρ : RankFunction V) (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else rankShiftIdeal k (RankFunction.scale s ρ) i

@[simp] theorem powerShiftPiece_zero (ρ : RankFunction V) (i : ℕ) :
    powerShiftPiece (k := k) ρ i 0 = ⊥ := by simp [powerShiftPiece]

theorem powerShiftPiece_pos (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s) :
    powerShiftPiece (k := k) ρ i s = rankShiftIdeal k (RankFunction.scale s ρ) i := by
  simp [powerShiftPiece, Nat.ne_of_gt hs]

theorem powerShiftPiece_le_pow (ρ : RankFunction V) (i s : ℕ) :
    powerShiftPiece (k := k) ρ i s ≤ (rankIdeal k ρ) ^ s := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece, if_neg hs, ← rankIdeal_scale]
    exact rankShiftIdeal_le_rankIdeal _ _

theorem powerShiftPiece_action (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * powerShiftPiece ρ i s ≤ powerShiftPiece ρ i (n + s) := by
  by_cases hs : s = 0
  · simp [hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [powerShiftPiece, if_neg hs, if_neg hns]
    exact powerShiftIdeal_mul_le ρ i n s

/-- The ordinary coefficientwise ideal inside Mathlib's actual Rees algebra.
Its underlying graded module is precisely the direct sum of the positive
power-shift pieces. -/
def shiftReesIdeal (ρ : RankFunction V) (i : ℕ) : Ideal (reesAlgebra (rankIdeal k ρ)) where
  carrier := {p | ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (powerShiftPiece ρ i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ powerShiftPiece ρ i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact powerShiftPiece_action ρ i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_shiftReesIdeal (ρ : RankFunction V) (i : ℕ)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔ ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s := Iff.rfl

def shiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    reesAlgebra (rankIdeal k ρ) :=
  ⟨Polynomial.monomial s (MvPolynomial.monomial a 1),
    reesAlgebra.monomial_mem.mpr (powerShiftPiece_le_pow ρ i s ha)⟩

theorem shiftReesMonomial_mem (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    shiftReesMonomial ρ i s a ha ∈ shiftReesIdeal ρ i := by
  intro t
  change (Polynomial.monomial s (MvPolynomial.monomial a 1)).coeff t ∈ _
  by_cases ht : t = s
  · subst t
    simpa using ha
  · simp [Polynomial.coeff_monomial, ht, Ne.symm ht]

/-- The exponent factorization is literal multiplication of monomials in
the ambient polynomial ring, not a stipulated combinatorial action. -/
theorem rees_monomial_factorization {s r : ℕ} (hrs : r ≤ s)
    {a b : Exponent V} (hba : b ≤ a) :
    Polynomial.monomial (s - r) (MvPolynomial.monomial (a - b) (1 : k)) *
      Polynomial.monomial r (MvPolynomial.monomial b 1) =
        Polynomial.monomial s (MvPolynomial.monomial a 1) := by
  rw [Polynomial.monomial_mul_monomial, MvPolynomial.monomial_mul]
  simp only [Nat.sub_add_cancel hrs, tsub_add_cancel_of_le hba, one_mul]

/-- A genuine minimal module monomial: every divisor that belongs to the
module and whose quotient belongs to the Rees algebra is the same monomial.
The pair `(s,a)` records its actual Rees and ordinary multidegrees. -/
def IsMinimalShiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - r) →
      r = s ∧ b = a

theorem minimalShiftRees_positive {ρ : RankFunction V} {i s : ℕ} {a : Exponent V}
    (h : IsMinimalShiftReesMonomial (k := k) ρ i s a) : 0 < s := by
  by_contra hn
  have hs : s = 0 := by omega
  have hm := h.1
  simp [hs] at hm

theorem earlier_powerShift_product_le (ρ : RankFunction V) (i : ℕ) {r s : ℕ}
    (hrs : r < s) :
    (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r ≤
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have he : s - r = 1 + (s - 1 - r) := by omega
  have ht : s - 1 - r + r = s - 1 := by omega
  rw [he, pow_add, pow_one, mul_assoc]
  have h := powerShiftPiece_action (k := k) ρ i (s - 1 - r) r
  rw [ht] at h
  exact Ideal.mul_mono le_rfl h

/-- Exact intrinsic criterion for the new minimal monomials in a positive
Rees degree: ordinary minimal bases outside the preceding Rees product. -/
theorem minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s)
    (a : Exponent V) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      a ∈ rankShiftFamily (RankFunction.scale s ρ) i ∧
        MvPolynomial.monomial a (1 : k) ∉ rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have hpiece := powerShiftPiece_pos (k := k) ρ i hs
  constructor
  · intro h
    have ha := h.1
    rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have hbPiece : MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i s := by
      rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨b, hb, le_rfl⟩
    have he := (h.2 s b le_rfl hba hbPiece (by simp)).2
    refine ⟨he ▸ hb, ?_⟩
    intro hp
    by_cases hs1 : s = 1
    · simp [hs1] at hp
    have hprev : 0 < s - 1 := by omega
    rw [powerShiftPiece_pos ρ i hprev, rankIdeal, rankShiftIdeal_eq_monomialIdeal,
      monomialIdeal_mul, monomial_mem_iff] at hp
    obtain ⟨c, hc, hca⟩ := hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hc
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    have hya : y ≤ a := (le_add_left le_rfl).trans hca
    have hxa : x ≤ a - y := by
      intro j
      have hj := hca j
      simp only [Finsupp.add_apply] at hj
      change x j ≤ a j - y j
      omega
    have hyPiece : MvPolynomial.monomial y (1 : k) ∈ powerShiftPiece ρ i (s - 1) := by
      rw [powerShiftPiece_pos ρ i hprev, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨y, hy, le_rfl⟩
    have hxPower : MvPolynomial.monomial (a - y) (1 : k) ∈ (rankIdeal k ρ) ^ (s - (s - 1)) := by
      rw [show s - (s - 1) = 1 by omega, pow_one]
      exact (monomial_mem_iff (rankBases ρ) (a - y)).mpr ⟨x, hx, hxa⟩
    have he := (h.2 (s - 1) y (by omega) hya hyPiece hxPower).1
    omega
  · rintro ⟨ha, hnew⟩
    refine ⟨?_, ?_⟩
    · rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨a, ha, le_rfl⟩
    · intro r b hrs hba hb hf
      by_cases hrsEq : r = s
      · subst r
        rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at hb
        obtain ⟨c, hc, hcb⟩ := hb
        have he := (rankShiftFamily_equigenerated (RankFunction.scale s ρ) i).antichain
          c hc a ha (hcb.trans hba)
        exact ⟨rfl, le_antisymm hba (he ▸ hcb)⟩
      · have hrsLt : r < s := by omega
        have hp := Ideal.mul_mem_mul hf hb
        have hp' : MvPolynomial.monomial a (1 : k) ∈
            (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r := by
          simpa only [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hba] using hp
        exact (hnew (earlier_powerShift_product_le ρ i hrsLt hp')).elim

end CommAlg.Polymatroid
