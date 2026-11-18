module

public import VolumePolynomials.BinarySimplexRealization
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Order.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Positive approximation of every allowed binary zero pattern

The support interval is derived from the separated-index inequalities. The
padding is the one in Appendix A. Its ratios are proved to be ordered for
all sufficiently small positive parameters, including a support consisting
of a single coefficient.
-/

open Set Filter
open scoped BigOperators Topology

namespace VolumePolynomials.BinarySimplex

open BinarySequences

structure IntervalSupport (d : ℕ) (a : ℕ → ℝ) where
  left : ℕ
  right : ℕ
  left_le_right : left ≤ right
  right_le_degree : right ≤ d
  positive : ∀ i, left ≤ i → i ≤ right → 0 < a i
  vanishes : ∀ i ≤ d, (i < left ∨ right < i) → a i = 0

theorem intervalSupport_of_criterion {d : ℕ} {a : ℕ → ℝ}
    (hc : Criterion d a) (hne : ∃ i ≤ d, a i ≠ 0) : Nonempty (IntervalSupport d a) := by
  first
  | classical
    let S := (Finset.range (d + 1)).filter (fun i => 0 < a i)
    have hS : S.Nonempty := by
      first
      | obtain ⟨i, hid, hi⟩ := hne
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
          lt_of_le_of_ne (hc.1 i hid) (Ne.symm hi)⟩⟩
    let l := S.min' hS
    let r := S.max' hS
    have hlS : l ∈ S := Finset.min'_mem S hS
    have hrS : r ∈ S := Finset.max'_mem S hS
    have hlr : l ≤ r := Finset.min'_le_max' S hS
    have hrd : r ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hrS).1)
    have hlpos : 0 < a l := (Finset.mem_filter.mp hlS).2
    have hrpos : 0 < a r := (Finset.mem_filter.mp hrS).2
    refine ⟨⟨l, r, hlr, hrd, ?_, ?_⟩⟩
    · intro i hli hir
      exact hc.noInternalZeros l i r hli hir hrd hlpos hrpos
    · intro i hid hout
      apply le_antisymm _ (hc.1 i hid)
      apply le_of_not_gt
      intro hipos
      have hiS : i ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hipos⟩
      have hli : l ≤ i := Finset.min'_le S i hiS
      have hir : i ≤ r := Finset.le_max' S i hiS
      rcases hout with h | h <;> omega

def padded (a : ℕ → ℝ) (l r : ℕ) (eps : ℝ) (i : ℕ) : ℝ :=
  if i < l then a l * eps ^ (l - i)
  else if r < i then a r * eps ^ (i - r)
  else a i

theorem padded_eq_left (a : ℕ → ℝ) {l r i : ℕ} (hlr : l ≤ r) (hi : i ≤ l) (eps : ℝ) :
    padded a l r eps i = a l * eps ^ (l - i) := by
  first
  | by_cases hil : i < l
    · simp only [padded, if_pos hil]
    · have heq : i = l := by omega
      subst i
      simp [padded, not_lt_of_ge hlr]

theorem padded_eq_right (a : ℕ → ℝ) {l r i : ℕ} (hlr : l ≤ r) (hi : r ≤ i) (eps : ℝ) :
    padded a l r eps i = a r * eps ^ (i - r) := by
  first
  | by_cases hri : r < i
    · simp only [padded, if_neg (by omega : ¬i < l), if_pos hri]
    · have heq : i = r := by omega
      subst i
      simp [padded, not_lt_of_ge hlr]

theorem padded_eq_middle (a : ℕ → ℝ) {l r i : ℕ}
    (hli : l ≤ i) (hir : i ≤ r) (eps : ℝ) : padded a l r eps i = a i := by
  first
  | simp only [padded, if_neg (not_lt_of_ge hli), if_neg (not_lt_of_ge hir)]

theorem IntervalSupport.padded_pos {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {eps : ℝ} (heps : 0 < eps) : ∀ i ≤ d, 0 < padded a h.left h.right eps i := by
  first
  | intro i hid
    by_cases hil : i < h.left
    · rw [padded_eq_left a h.left_le_right hil.le]
      exact mul_pos (h.positive _ le_rfl h.left_le_right) (pow_pos heps _)
    by_cases hri : h.right < i
    · rw [padded_eq_right a h.left_le_right hri.le]
      exact mul_pos (h.positive _ h.left_le_right le_rfl) (pow_pos heps _)
    rw [padded_eq_middle a (by omega) (by omega)]
    exact h.positive i (by omega) (by omega)

theorem padded_ratio_left {a : ℕ → ℝ} {l r i : ℕ} (hlr : l ≤ r)
    (ha : 0 < a l) (hi : i < l) {eps : ℝ} (heps : 0 < eps) :
    padded a l r eps (i + 1) / padded a l r eps i = 1 / eps := by
  first
  | rw [padded_eq_left a hlr (by omega), padded_eq_left a hlr hi.le]
    have hpow : l - i = (l - (i + 1)) + 1 := by omega
    rw [hpow, pow_succ]
    field_simp [ha.ne', heps.ne', pow_ne_zero _ heps.ne']

theorem padded_ratio_middle (a : ℕ → ℝ) {l r i : ℕ}
    (hli : l ≤ i) (hir : i < r) (eps : ℝ) :
    padded a l r eps (i + 1) / padded a l r eps i = a (i + 1) / a i := by
  first
  | rw [padded_eq_middle a (by omega) (by omega), padded_eq_middle a hli hir.le]

theorem padded_ratio_right {a : ℕ → ℝ} {l r i : ℕ} (hlr : l ≤ r)
    (ha : 0 < a r) (hi : r ≤ i) {eps : ℝ} (heps : 0 < eps) :
    padded a l r eps (i + 1) / padded a l r eps i = eps := by
  first
  | rw [padded_eq_right a hlr (by omega), padded_eq_right a hlr hi]
    have hpow : i + 1 - r = (i - r) + 1 := by omega
    rw [hpow, pow_succ]
    field_simp [ha.ne', heps.ne', pow_ne_zero _ heps.ne']

theorem padded_decreasingRatios {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    (hc : Criterion d a) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hsmall : ∀ i : ℕ, h.left ≤ i → i < h.right →
      eps ≤ a (i + 1) / a i ∧ a (i + 1) / a i ≤ 1 / eps) :
    DecreasingRatios d (padded a h.left h.right eps) := by
  first
  | intro i j hij hjd
    have hrd := h.right_le_degree
    have hlpos := h.positive h.left le_rfl h.left_le_right
    have hrpos := h.positive h.right h.left_le_right le_rfl
    by_cases hjl : j < h.left
    · rw [padded_ratio_left h.left_le_right hlpos hjl heps,
        padded_ratio_left h.left_le_right hlpos (by omega) heps]
    by_cases hri : h.right ≤ i
    · rw [padded_ratio_right h.left_le_right hrpos hri heps,
        padded_ratio_right h.left_le_right hrpos (by omega) heps]
    by_cases hil : i < h.left
    · rw [padded_ratio_left h.left_le_right hlpos hil heps]
      by_cases hjr : j < h.right
      · rw [padded_ratio_middle a (by omega) hjr]
        exact (hsmall j (by omega) hjr).2
      · rw [padded_ratio_right h.left_le_right hrpos (by omega) heps]
        apply (le_div_iff₀ heps).mpr
        nlinarith
    have hli : h.left ≤ i := by omega
    have hir : i < h.right := by omega
    rw [padded_ratio_middle a hli hir]
    by_cases hjr : j < h.right
    · rw [padded_ratio_middle a (by omega) hjr]
      exact ratios_antitone_on_interval h.positive
        (fun k hlk hkr => hc.adjacent (by omega) (by omega)) i j hli hij hjr
    · rw [padded_ratio_right h.left_le_right hrpos (by omega) heps]
      exact (hsmall i hli hir).1

theorem eventually_padding_bounds {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), 0 < eps ∧ eps ≤ 1 ∧
      ∀ i : ℕ, h.left ≤ i → i < h.right →
        eps ≤ a (i + 1) / a i ∧ a (i + 1) / a i ≤ 1 / eps := by
  first
  | have hfinite : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        ∀ i : Fin d, h.left ≤ i.val → i.val < h.right →
          eps ≤ a (i.val + 1) / a i.val ∧ a (i.val + 1) / a i.val ≤ 1 / eps := by
      first
      | apply Filter.eventually_all.mpr
        intro i
        by_cases hli : h.left ≤ i.val
        · by_cases hir : i.val < h.right
          · have hratio : 0 < a (i.val + 1) / a i.val :=
              div_pos (h.positive _ (by omega) (by omega)) (h.positive _ hli hir.le)
            filter_upwards [(eventually_lt_nhds hratio).filter_mono nhdsWithin_le_nhds,
              (eventually_lt_nhds (one_div_pos.mpr hratio)).filter_mono nhdsWithin_le_nhds,
              self_mem_nhdsWithin] with eps he1 he2 hepos
            intro _ _
            refine ⟨he1.le, (le_div_iff₀ hepos).mpr ?_⟩
            have hm := (lt_div_iff₀ hratio).mp he2
            nlinarith
          · exact Filter.Eventually.of_forall (fun _ _ hi => False.elim (hir hi))
        · exact Filter.Eventually.of_forall (fun _ hi _ => False.elim (hli hi))
    filter_upwards [hfinite, self_mem_nhdsWithin,
      (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with eps hbounds heps heps1
    refine ⟨heps, heps1.le, ?_⟩
    intro i hli hir
    exact hbounds ⟨i, hir.trans_le h.right_le_degree⟩ hli hir

theorem eventually_padded_decreasingRatios {d : ℕ} {a : ℕ → ℝ}
    (h : IntervalSupport d a) (hc : Criterion d a) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      DecreasingRatios d (padded a h.left h.right eps) := by
  first
  | filter_upwards [eventually_padding_bounds h] with eps heps
    exact padded_decreasingRatios h hc heps.1 heps.2.1 heps.2.2

theorem continuous_padded (a : ℕ → ℝ) (l r i : ℕ) :
    Continuous (fun eps : ℝ => padded a l r eps i) := by
  first
  | unfold padded
    split_ifs <;> fun_prop

theorem IntervalSupport.padded_zero {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a)
    {i : ℕ} (hi : i ≤ d) : padded a h.left h.right 0 i = a i := by
  first
  | by_cases hil : i < h.left
    · rw [padded_eq_left a h.left_le_right hil.le,
        zero_pow (by omega : h.left - i ≠ 0), mul_zero,
        h.vanishes i hi (Or.inl hil)]
    by_cases hri : h.right < i
    · rw [padded_eq_right a h.left_le_right hri.le,
        zero_pow (by omega : i - h.right ≠ 0), mul_zero,
        h.vanishes i hi (Or.inr hri)]
    exact padded_eq_middle a (by omega) (by omega) 0

theorem value_padded_tendsto {d : ℕ} {a : ℕ → ℝ} (h : IntervalSupport d a) (t s : ℝ) :
    Tendsto (fun eps : ℝ => value d (padded a h.left h.right eps) t s)
      (𝓝[>] (0 : ℝ)) (𝓝 (value d a t s)) := by
  first
  | have hc : Continuous (fun eps : ℝ => value d (padded a h.left h.right eps) t s) := by
      first
      | unfold value
        apply continuous_finsetSum
        intro i _
        exact (((continuous_padded a h.left h.right i).const_mul _).mul continuous_const).mul continuous_const
    have hz : value d (padded a h.left h.right 0) t s = value d a t s := by
      first
      | apply Finset.sum_congr rfl
        intro i hi
        rw [h.padded_zero (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    simpa only [hz] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

end VolumePolynomials.BinarySimplex
