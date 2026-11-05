module

public import sunlet.height_obstructions
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Push

/-! The remaining one-level obstruction and its exact subgroup index. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight

variable {G C : Type*} [AddCommGroup G]

theorem index_two_of_complement_differences (H : AddSubgroup G) (a : G) (ha : a ∉ H)
    (hcos : ∀ b c, b ∉ H → c ∉ H → c - b ∈ H) : H.index = 2 := by
  apply H.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨-a, by simpa using ha, ?_⟩
  intro b
  by_cases hb : b ∈ H
  · exact Or.inr hb
  · exact Or.inl (by simpa only [sub_eq_add_neg] using hcos a b ha hb)

namespace InverseStablePartition

variable [Fintype G] [Fintype C] [LinearOrder C]
  (P : InverseStablePartition G C)
  {x : C → ℚ} (hx : x ∈ P.heightSpace) (hn : ∀ i, 0 ≤ x i)

include hx hn in
theorem equal_positive_difference_zero {α : ℚ} (b c : G)
    (hb : x (P.classOf b) = α) (hc : x (P.classOf c) = α)
    (hbc : P.classOf b ≠ P.classOf c) : x (P.classOf (c - b)) = 0 := by
  simpa only [hb, hc, sub_self, abs_zero] using P.difference_absolute hx hn b c hbc

include hx hn in
theorem one_level_difference_zero {α : ℚ}
    (hlevels : ∀ i, x i = 0 ∨ x i = α)
    (a b : G) (ha : 0 < x (P.classOf a)) (hb : 0 < x (P.classOf b))
    (hab : P.classOf a ≠ P.classOf b)
    (p q : G) (hp : 0 < x (P.classOf p)) (hq : 0 < x (P.classOf q)) :
    x (P.classOf (q - p)) = 0 := by
  have level (g : G) (hg : 0 < x (P.classOf g)) : x (P.classOf g) = α := by
    rcases hlevels (P.classOf g) with h | h
    · exact ((ne_of_gt hg) h).elim
    · exact h
  by_cases hpq : P.classOf p = P.classOf q
  · obtain ⟨r, hr, hpr⟩ : ∃ r : G, 0 < x (P.classOf r) ∧ P.classOf p ≠ P.classOf r := by
      by_cases hpa : P.classOf p = P.classOf a
      · exact ⟨b, hb, fun h => hab (hpa.symm.trans h)⟩
      · exact ⟨a, ha, hpa⟩
    have hqr : P.classOf q ≠ P.classOf r := by simpa only [← hpq] using hpr
    have hz₁ := P.equal_positive_difference_zero hx hn r p (level r hr) (level p hp) (Ne.symm hpr)
    have hz₂ := P.equal_positive_difference_zero hx hn r q (level r hr) (level q hq) (Ne.symm hqr)
    have hm₁ : p - r ∈ P.zeroSubgroup x hx hn := hz₁
    have hm₂ : q - r ∈ P.zeroSubgroup x hx hn := hz₂
    have hm := (P.zeroSubgroup x hx hn).sub_mem hm₂ hm₁
    have he : q - r - (p - r) = q - p := by abel
    rw [he] at hm
    exact hm
  · exact P.equal_positive_difference_zero hx hn p q (level p hp) (level q hq) hpq

include hx hn in
theorem one_level_index_two {α : ℚ}
    (hlevels : ∀ i, x i = 0 ∨ x i = α)
    (a b : G) (ha : 0 < x (P.classOf a)) (hb : 0 < x (P.classOf b))
    (hab : P.classOf a ≠ P.classOf b) : (P.zeroSubgroup x hx hn).index = 2 := by
  have haH : a ∉ P.zeroSubgroup x hx hn := ne_of_gt ha
  apply index_two_of_complement_differences _ a haH
  intro p q hp hq
  have hpp : 0 < x (P.classOf p) := lt_of_le_of_ne (hn _) (Ne.symm hp)
  have hqp : 0 < x (P.classOf q) := lt_of_le_of_ne (hn _) (Ne.symm hq)
  exact P.one_level_difference_zero hx hn hlevels a b ha hb hab p q hpp hqp

include hx hn in
/-- A nonzero one-level height either has a single complement class, or its
zero subgroup has index two. No finite configuration search is used. -/
theorem one_level_structure {α : ℚ}
    (hlevels : ∀ i, x i = 0 ∨ x i = α) (hzero : x ≠ 0) :
    (∃ i, ∀ a, a ∉ P.zeroSubgroup x hx hn ↔ P.classOf a = i) ∨
      (P.zeroSubgroup x hx hn).index = 2 := by
  classical
  by_cases hsame : ∀ a b : G, 0 < x (P.classOf a) → 0 < x (P.classOf b) →
      P.classOf a = P.classOf b
  · left
    obtain ⟨i, hi⟩ : ∃ i, 0 < x i := by
      by_contra h
      push_neg at h
      apply hzero
      funext i
      exact le_antisymm (h i) (hn i)
    obtain ⟨a, ha⟩ := P.surjective i
    refine ⟨i, ?_⟩
    intro b
    constructor
    · intro hb
      have hbp : 0 < x (P.classOf b) := lt_of_le_of_ne (hn _) (Ne.symm hb)
      exact (hsame b a hbp (by simpa only [ha] using hi)).trans ha
    · intro hb
      change x (P.classOf b) ≠ 0
      rw [hb]
      exact ne_of_gt hi
  · push_neg at hsame
    obtain ⟨a, b, ha, hb, hab⟩ := hsame
    exact Or.inr (P.one_level_index_two hx hn hlevels a b ha hb hab)

include hx hn in
/-- In the bad two-level case the subgroup has the literal index two used
in the exceptional orbit partition of Theorem 7.1. -/
theorem two_level_bad_structure_index
    (hlevels : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = 2) (hbad : P.BadHeight x)
    (a c : G) (ha : x (P.classOf a) = 1) (hc : x (P.classOf c) = 2) :
    ∃ H : AddSubgroup G, H.index = 2 ∧
      (∀ b, b ∉ H ↔ P.classOf b = P.classOf a) ∧
      (∀ b, x (P.classOf b) = 2 ↔ P.classOf b = P.classOf c) := by
  obtain ⟨H, hH, hcos, htwo⟩ := P.two_level_bad_structure hx hn hlevels hbad a c ha hc
  exact ⟨H, index_two_of_complement_differences H a ((hH a).mpr rfl) hcos, hH, htwo⟩

end InverseStablePartition

end Sunlet.OrbitHeight
