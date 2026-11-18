module

public import sunlet.orbit_height_completion

/-! The subgroup and class structure behind the bad orders in §7.2. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)

variable {x : C → ℚ} (hx : x ∈ P.heightSpace) (hn : ∀ i, 0 ≤ x i)

include hx hn

/-- With a level-two element available, zero-height translation preserves
the actual class of a level-one element, not merely its height. -/
theorem zero_translation_class (a z c : G)
    (ha : x (P.classOf a) = 1) (hz : x (P.classOf z) = 0)
    (hc : x (P.classOf c) = 2) :
    P.classOf (a - z) = P.classOf a := by
  have haz : x (P.classOf (a - z)) = 1 := by
    rw [P.zero_translation hx hn z hz a, ha]
  have hnz : x (P.classOf (-z)) = 0 := by rw [P.neg_class, hz]
  have hcz : x (P.classOf (c + z)) = 2 := by
    simpa only [sub_neg_eq_add, hc] using P.zero_translation hx hn (-z) hnz c
  have h₁ := (P.larger_positive_eq_twice hx hn (a - z) c
    (by rw [haz]; norm_num) (by rw [haz, hc]; norm_num)).2
  have h₂ := (P.larger_positive_eq_twice hx hn a (c + z)
    (by rw [ha]; norm_num) (by rw [ha, hcz]; norm_num)).2
  rw [P.neg_class] at h₁ h₂
  have he : c - (a - z) = c + z - a := by abel
  rw [he] at h₁
  exact h₁.symm.trans h₂

/-- Whenever both positive levels occur, all level-one elements form one class. -/
theorem level_one_single_class (a b c : G)
    (ha : x (P.classOf a) = 1) (hb : x (P.classOf b) = 1)
    (hc : x (P.classOf c) = 2) : P.classOf a = P.classOf b := by
  by_contra hab
  have hz : x (P.classOf (a - b)) = 0 := by
    simpa only [ha, hb, sub_self, abs_zero] using
      P.difference_absolute hx hn b a (Ne.symm hab)
  have h := P.zero_translation_class hx hn a (a - b) c ha hz hc
  have he : a - (a - b) = b := by abel
  rw [he] at h
  exact hab h.symm

/-- Every element outside level one preserves level one by translation. -/
theorem preserves_level_one
    (hlevels : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = 2)
    (z a : G) (hz : x (P.classOf z) ≠ 1) (ha : x (P.classOf a) = 1) :
    x (P.classOf (a + z)) = 1 := by
  rcases hlevels (P.classOf z) with hz0 | hz1 | hz2
  · have hnz : x (P.classOf (-z)) = 0 := by rw [P.neg_class, hz0]
    simpa only [sub_neg_eq_add, ha] using P.zero_translation hx hn (-z) hnz a
  · exact (hz hz1).elim
  · have hna : x (P.classOf (-a)) = 1 := by rw [P.neg_class, ha]
    have he := (P.larger_positive_eq_twice hx hn (-a) z
      (by rw [hna]; norm_num) (by rw [hna, hz2]; norm_num)).2
    have hg : z - -a = a + z := by abel
    rw [hg, neg_neg] at he
    rw [he, ha]

/-- If heights belong to `{0,1,2}`, the complement of level one is a subgroup. -/
def nonOneSubgroup
    (hlevels : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = 2) : AddSubgroup G where
  carrier := {a | x (P.classOf a) ≠ 1}
  zero_mem' := by
    change x (P.classOf 0) ≠ 1
    rw [P.zero_class, hx.1]
    norm_num
  neg_mem' := by
    intro a ha
    change x (P.classOf a) ≠ 1 at ha
    change x (P.classOf (-a)) ≠ 1
    simpa only [P.neg_class] using ha
  add_mem' := by
    intro a b ha hb
    change x (P.classOf (a + b)) ≠ 1
    intro hab
    have hnab : x (P.classOf (-(a + b))) = 1 := by rw [P.neg_class, hab]
    have he := P.preserves_level_one hx hn hlevels a (-(a + b)) ha hnab
    have hg : -(a + b) + a = -b := by abel
    rw [hg, P.neg_class] at he
    exact hb he

/-- An order is bad precisely when all positive same-class difference
coordinates are confined to at most one class. -/
def BadHeight (x : C → ℚ) : Prop :=
  ∀ i j, P.sameClassDifference i → P.sameClassDifference j →
    0 < x i → 0 < x j → i = j

theorem level_two_unique (hbad : P.BadHeight x)
    (a b c : G) (ha : x (P.classOf a) = 1)
    (hb : x (P.classOf b) = 2) (hc : x (P.classOf c) = 2) :
    P.classOf b = P.classOf c := by
  have hap : 0 < x (P.classOf a) := by rw [ha]; norm_num
  have hRb := P.upper_level_mem_sameClassDifference hx hn a b hap (by rw [hb, ha]; norm_num)
  have hRc := P.upper_level_mem_sameClassDifference hx hn a c hap (by rw [hc, ha]; norm_num)
  exact hbad _ _ hRb hRc (by rw [hb]; norm_num) (by rw [hc]; norm_num)

theorem level_one_not_sameClassDifference (hbad : P.BadHeight x)
    (a c : G) (ha : x (P.classOf a) = 1) (hc : x (P.classOf c) = 2) :
    ¬ P.sameClassDifference (P.classOf a) := by
  intro hRa
  have hap : 0 < x (P.classOf a) := by rw [ha]; norm_num
  have hRc := P.upper_level_mem_sameClassDifference hx hn a c hap (by rw [hc, ha]; norm_num)
  have he := hbad _ _ hRa hRc hap (by rw [hc]; norm_num)
  have := congrArg x he
  rw [ha, hc] at this
  norm_num at this

/-- The complement of the subgroup is one coset in the two-level bad case.
This is the group-theoretic content of the index-two obstruction. -/
theorem level_one_difference_in_subgroup (hbad : P.BadHeight x)
    (a b c : G) (ha : x (P.classOf a) = 1)
    (hb : x (P.classOf b) = 1) (hc : x (P.classOf c) = 2) :
    x (P.classOf (b - a)) ≠ 1 := by
  intro hd
  have hR : P.sameClassDifference (P.classOf (b - a)) := by
    refine ⟨?_, a, b, P.level_one_single_class hx hn a b c ha hb hc, ?_, rfl⟩
    · intro he
      rw [he, hx.1] at hd
      norm_num at hd
    · intro he
      rw [he, hx.1] at ha
      norm_num at ha
  exact P.level_one_not_sameClassDifference hx hn hbad (b - a) c hd hc hR

/-- The two-level bad obstruction consists of exactly one class outside an
actual subgroup, and exactly one class at level two inside it. -/
theorem two_level_bad_structure
    (hlevels : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = 2) (hbad : P.BadHeight x)
    (a c : G) (ha : x (P.classOf a) = 1) (hc : x (P.classOf c) = 2) :
    ∃ H : AddSubgroup G,
      (∀ b, b ∉ H ↔ P.classOf b = P.classOf a) ∧
      (∀ b d, b ∉ H → d ∉ H → d - b ∈ H) ∧
      (∀ b, x (P.classOf b) = 2 ↔ P.classOf b = P.classOf c) := by
  refine ⟨P.nonOneSubgroup hx hn hlevels, ?_, ?_, ?_⟩
  · intro b
    change ¬ x (P.classOf b) ≠ 1 ↔ _
    simp only [not_not]
    constructor
    · intro hb
      exact P.level_one_single_class hx hn b a c hb ha hc
    · intro he
      rw [he, ha]
  · intro b d hb hd
    have hb1 : x (P.classOf b) = 1 := not_not.mp hb
    have hd1 : x (P.classOf d) = 1 := not_not.mp hd
    exact P.level_one_difference_in_subgroup hx hn hbad b d c hb1 hd1 hc
  · intro b
    constructor
    · intro hb
      exact P.level_two_unique hx hn hbad a b c ha hb hc
    · intro he
      rw [he, hc]

end Sunlet.OrbitHeight.InverseStablePartition
