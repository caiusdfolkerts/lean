module

public import sunlet.one_level_obstructions
public import Mathlib.Order.CompleteLattice.Basic

/-! Actual subgroup structure of class partitions, independent of class order. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitHeight.InverseStablePartition

variable {G C : Type*} [AddCommGroup G] (P : InverseStablePartition G C)

/-- Membership in the subgroup is constant on each literal class. -/
def ClassSaturated (H : AddSubgroup G) : Prop :=
  ∀ a b, P.classOf a = P.classOf b → (a ∈ H ↔ b ∈ H)

/-- A class equal to the complement of an actual subgroup. -/
def ComplementClass (i : C) : Prop :=
  ∃ H : AddSubgroup G, ∀ a, a ∉ H ↔ P.classOf a = i

theorem complementClass_ne_zero {i : C} (hi : P.ComplementClass i) : i ≠ P.zeroClass := by
  obtain ⟨H, hH⟩ := hi
  intro he
  have : (0 : G) ∉ H := (hH 0).mpr (((P.zero_iff 0).mpr rfl).trans he.symm)
  exact this H.zero_mem

/-- There cannot be two distinct complement classes. The proof uses the
subgroup laws directly, rather than a cardinality bound. -/
theorem complementClass_unique {i j : C} (hi : P.ComplementClass i)
    (hj : P.ComplementClass j) : i = j := by
  obtain ⟨H, hH⟩ := hi
  obtain ⟨J, hJ⟩ := hj
  obtain ⟨a, ha⟩ := P.surjective i
  obtain ⟨b, hb⟩ := P.surjective j
  by_contra hij
  have haH : a ∉ H := (hH a).mpr ha
  have hbJ : b ∉ J := (hJ b).mpr hb
  have haJ : a ∈ J := by
    by_contra han
    exact hij (ha.symm.trans ((hJ a).mp han))
  have hbH : b ∈ H := by
    by_contra hbn
    exact hij (((hH b).mp hbn).symm.trans hb)
  have habH : a + b ∉ H := by
    intro h
    exact haH (by simpa using H.sub_mem h hbH)
  have habJ : a + b ∉ J := by
    intro h
    exact hbJ (by simpa using J.sub_mem h haJ)
  exact hij (((hH (a + b)).mp habH).symm.trans ((hJ (a + b)).mp habJ))

/-- The complement of a proper subgroup generates the whole group. -/
theorem subgroup_eq_top_of_contains_complement (H J : AddSubgroup G)
    (a : G) (ha : a ∉ H) (hHJ : ∀ b, b ∉ H → b ∈ J) : J = ⊤ := by
  apply top_unique
  intro b _
  by_cases hb : b ∈ H
  · have hab : a + b ∉ H := by
      intro h
      exact ha (by simpa using H.sub_mem h hb)
    simpa using J.sub_mem (hHJ _ hab) (hHJ _ ha)
  · exact hHJ b hb

/-- Intersection of all class-saturated subgroups of index two. This gives
the same separation needed in the paper without presupposing a character basis. -/
def indexTwoCore : AddSubgroup G :=
  sInf {H : AddSubgroup G | H.index = 2 ∧ P.ClassSaturated H}

theorem mem_indexTwoCore (a : G) : a ∈ P.indexTwoCore ↔
    ∀ H : AddSubgroup G, H.index = 2 → P.ClassSaturated H → a ∈ H := by
  simp only [indexTwoCore, AddSubgroup.mem_sInf, Set.mem_setOf_eq]
  constructor
  · intro h H hH hs
    exact h H ⟨hH, hs⟩
  · intro h H hH
    exact h H hH.1 hH.2

theorem indexTwoCore_saturated : P.ClassSaturated P.indexTwoCore := by
  intro a b hab
  rw [P.mem_indexTwoCore, P.mem_indexTwoCore]
  constructor
  · intro h H hH hs
    exact (hs a b hab).mp (h H hH hs)
  · intro h H hH hs
    exact (hs a b hab).mpr (h H hH hs)

theorem same_class_sub_mem_indexTwoCore (a b : G)
    (hab : P.classOf a = P.classOf b) : a - b ∈ P.indexTwoCore := by
  rw [P.mem_indexTwoCore]
  intro H hH hs
  rw [sub_eq_add_neg, AddSubgroup.add_mem_iff_of_index_two hH, AddSubgroup.neg_mem_iff]
  exact hs a b hab

theorem two_smul_mem_indexTwoCore (a : G) : (2 : ℕ) • a ∈ P.indexTwoCore := by
  rw [P.mem_indexTwoCore]
  intro H hH _
  exact H.two_smul_mem_of_index_two hH a

/-- If the separating intersection vanishes, every class is a singleton. -/
theorem classOf_injective_of_indexTwoCore_bot (hbot : P.indexTwoCore = ⊥) :
    Function.Injective P.classOf := by
  intro a b hab
  have h := P.same_class_sub_mem_indexTwoCore a b hab
  rw [hbot, AddSubgroup.mem_bot] at h
  exact sub_eq_zero.mp h

section Ordered

variable [Fintype G] [Fintype C] [LinearOrder C]

theorem zeroSubgroup_saturated {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) : P.ClassSaturated (P.zeroSubgroup x hx hn) := by
  intro a b hab
  change (x (P.classOf a) = 0 ↔ x (P.classOf b) = 0)
  rw [hab]

/-- All normalized bad heights have one of the two genuine group-theoretic
obstructions: a complement class, or an index-two zero subgroup. -/
theorem normalized_bad_obstruction {x : C → ℚ} (hx : x ∈ P.heightSpace)
    (hn : ∀ i, 0 ≤ x i) (hzero : x ≠ 0)
    (hlevels : ∀ i, x i = 0 ∨ x i = 1 ∨ x i = 2) (hbad : P.BadHeight x) :
    (∃ i, P.ComplementClass i) ∨ (P.zeroSubgroup x hx hn).index = 2 := by
  classical
  by_cases htwo : ∃ c : G, x (P.classOf c) = 2
  · obtain ⟨c, hc⟩ := htwo
    by_cases hone : ∃ a : G, x (P.classOf a) = 1
    · obtain ⟨a, ha⟩ := hone
      obtain ⟨H, _, hH, _⟩ := P.two_level_bad_structure_index hx hn hlevels hbad a c ha hc
      exact Or.inl ⟨P.classOf a, H, hH⟩
    · have hl : ∀ i, x i = 0 ∨ x i = 2 := by
        intro i
        rcases hlevels i with h | h | h
        · exact Or.inl h
        · obtain ⟨a, ha⟩ := P.surjective i
          exact (hone ⟨a, by simpa only [ha] using h⟩).elim
        · exact Or.inr h
      rcases P.one_level_structure hx hn hl hzero with ⟨i, hi⟩ | h
      · exact Or.inl ⟨i, _, hi⟩
      · exact Or.inr h
  · have hl : ∀ i, x i = 0 ∨ x i = 1 := by
      intro i
      rcases hlevels i with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨a, ha⟩ := P.surjective i
        exact (htwo ⟨a, by simpa only [ha] using h⟩).elim
    rcases P.one_level_structure hx hn hl hzero with ⟨i, hi⟩ | h
    · exact Or.inl ⟨i, _, hi⟩
    · exact Or.inr h

end Ordered
end Sunlet.OrbitHeight.InverseStablePartition
