module

public import Ellipsoid.RootCounts
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realTupleCount {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter fun i => a i < c).card

theorem realTupleCount_eq_countP {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    realTupleCount a c = (Finset.univ.val.map (fun i => (a i : ℂ))).countP
      (fun z => z.re < c) := by
  rw [Multiset.countP_map]
  change (Finset.univ.filter fun i => a i < c).card =
    (Multiset.filter (fun i => a i < c) Finset.univ.val).card
  rw [← Finset.filter_val]
  rfl

theorem realTupleCount_perm {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (c : ℝ) : realTupleCount (a ∘ σ) c = realTupleCount a c := by
  rw [realTupleCount_eq_countP, realTupleCount_eq_countP]
  have hm : Finset.univ.val.map (fun i => ((a ∘ σ) i : ℂ)) =
      Finset.univ.val.map (fun i => (a i : ℂ)) := by
    change Finset.univ.val.map ((fun i => (a i : ℂ)) ∘ σ) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [hm]

theorem realTupleCount_ge_of_monotone {n : ℕ} {a : Fin n → ℝ}
    (ha : Monotone a) {k : Fin n} {c : ℝ} (hk : a k < c) :
    k.val + 1 ≤ realTupleCount a c := by
  rw [← Fin.card_Iic k]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
    (ha (Finset.mem_Iic.mp hi)).trans_lt hk⟩

theorem realTupleCount_le_of_monotone {n : ℕ} {a : Fin n → ℝ}
    (ha : Monotone a) {k : Fin n} {c : ℝ} (hk : c ≤ a k) :
    realTupleCount a c ≤ k.val := by
  rw [← Fin.card_Iio k]
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_Iio.mpr
  by_contra hki
  have h := ha (le_of_not_gt hki)
  have hic := (Finset.mem_filter.mp hi).2
  linarith

/-- A root-count identity at a cut in every sufficiently long interval
forces uniform matching of the sorted tuples. -/
theorem exists_perm_dist_le_of_cut_counts {n : ℕ} (a b : Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hcut : ∀ u v : ℝ, L < v - u →
      ∃ c ∈ Ioo u v, realTupleCount a c = realTupleCount b c) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ L := by
  let A := a ∘ Tuple.sort a
  let B := b ∘ Tuple.sort b
  have hA : Monotone A := Tuple.monotone_sort a
  have hB : Monotone B := Tuple.monotone_sort b
  have hdist (k : Fin n) : |A k - B k| ≤ L := by
    apply abs_le.mpr
    constructor
    · by_contra h
      have hlt : L < B k - A k := by linarith
      obtain ⟨c, hc, heq⟩ := hcut (A k) (B k) hlt
      have hleft := realTupleCount_ge_of_monotone hA hc.1
      have hright := realTupleCount_le_of_monotone hB hc.2.le
      rw [realTupleCount_perm] at hleft hright
      omega
    · by_contra h
      have hlt : L < A k - B k := by linarith
      obtain ⟨c, hc, heq⟩ := hcut (B k) (A k) hlt
      have hleft := realTupleCount_ge_of_monotone hB hc.1
      have hright := realTupleCount_le_of_monotone hA hc.2.le
      rw [realTupleCount_perm] at hleft hright
      omega
  refine ⟨(Tuple.sort a).symm.trans (Tuple.sort b), fun i => ?_⟩
  simpa [A, B, Function.comp_def] using hdist ((Tuple.sort a).symm i)

/-- Quantitative multiplicity-preserving matching from a continuous
polynomial homotopy whose roots stay within `rho` of the initial real roots.
The homotopy itself may have nonreal roots. -/
theorem exists_perm_dist_le_of_polynomial_homotopy {n : ℕ}
    (a b : Fin n → ℝ) {F : Icc (0 : ℝ) 1 → ℂ[X]}
    (hF : ∀ k ≤ n, Continuous (fun t => (F t).coeff k))
    (hdeg : ∀ t, (F t).degree = n)
    (hzero : (F ⟨0, by simp⟩).roots = Finset.univ.val.map (fun i => (a i : ℂ)))
    (hone : (F ⟨1, by simp⟩).roots = Finset.univ.val.map (fun i => (b i : ℂ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnear : ∀ t z, z ∈ (F t).roots → ∃ i, ‖z - (a i : ℂ)‖ < ρ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ 2 * n * ρ := by
  letI : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  apply exists_perm_dist_le_of_cut_counts a b (by positivity)
  intro u v huv
  obtain ⟨c, hc, hsep⟩ := exists_cut_away_from_finite_centres a hρ huv
  refine ⟨c, hc, ?_⟩
  have havoid : ∀ t z, z ∈ (F t).roots → z.re ≠ c := by
    intro t z hz hzc
    obtain ⟨i, hi⟩ := hnear t z hz
    have hreal := Complex.abs_re_le_norm (z - (a i : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, hzc] at hreal
    exact (not_lt_of_ge hreal) (hi.trans (hsep i))
  have hh := rootCount_left_eq_on_connected hF hdeg c havoid
    (⟨0, by simp⟩ : Icc (0 : ℝ) 1) (⟨1, by simp⟩ : Icc (0 : ℝ) 1)
  rw [hzero, hone, ← realTupleCount_eq_countP, ← realTupleCount_eq_countP] at hh
  exact hh

end EllipsoidVerification
