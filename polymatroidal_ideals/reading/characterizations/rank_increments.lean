import Characterizations.LowerBases

/-! # Rank increments on intervals of coordinate localizations -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem equigenerated_localize_degree {B : Family V} (hB : B.Nonempty)
    {U : Finset V} {d : ℕ} (hd : Equigenerated (localize B U) d)
    {b : Exponent V} (hb : b ∈ localize B U) : b.degree = lowerRank B U := by
  obtain ⟨a, ha, hmin⟩ := lowerRank_attained (localize_nonempty hB U) U
  rw [lowerRank_localize hB le_rfl] at hmin
  have haD : a.degree = subsetSum a U := by rw [← degree_project, localize_supported ha]
  exact (hd b hb).trans ((hd a ha).symm.trans (haD.trans hmin))

theorem lowerRank_supermodular_at_union {B : Family V} (hB : B.Nonempty)
    (A C : Finset V) (he : ∃ d, Equigenerated (localize B (A ∪ C)) d) :
    lowerRank B A + lowerRank B C ≤ lowerRank B (A ∪ C) + lowerRank B (A ∩ C) := by
  obtain ⟨d, hd⟩ := he
  obtain ⟨b, hb, hmin⟩ := lowerRank_attained (localize_nonempty hB (A ∪ C)) (A ∩ C)
  rw [lowerRank_localize hB (Finset.inter_subset_left.trans Finset.subset_union_left)] at hmin
  have hsum : subsetSum b (A ∪ C) = lowerRank B (A ∪ C) := by
    rw [← degree_project, localize_supported hb]
    exact equigenerated_localize_degree hB hd hb
  calc
    lowerRank B A + lowerRank B C ≤ subsetSum b A + subsetSum b C :=
      Nat.add_le_add (localize_sum_ge Finset.subset_union_left hb)
        (localize_sum_ge Finset.subset_union_right hb)
    _ = subsetSum b (A ∪ C) + subsetSum b (A ∩ C) := subsetSum_union_inter b A C
    _ = _ := by rw [hsum, hmin]

def SupermodularAbove (r : Finset V → ℕ) (U : Finset V) : Prop :=
  ∀ A C, U ⊆ A → U ⊆ C → r A + r C ≤ r (A ∪ C) + r (A ∩ C)

theorem lowerRank_supermodular_above {B : Family V} (hB : B.Nonempty) (U : Finset V)
    (he : ∀ W, U ⊂ W → ∃ d, Equigenerated (localize B W) d) :
    SupermodularAbove (lowerRank B) U := by
  intro A C hUA hUC
  by_cases h : A ∪ C = U
  · have hA : A = U := Finset.Subset.antisymm (h ▸ Finset.subset_union_left) hUA
    have hC : C = U := Finset.Subset.antisymm (h ▸ Finset.subset_union_right) hUC
    simp [hA, hC]
  · exact lowerRank_supermodular_at_union hB A C
      (he _ ((hUA.trans Finset.subset_union_left).ssubset_of_ne (Ne.symm h)))

theorem supermodular_rank_increments {r : Finset V → ℕ} {U : Finset V}
    (hr : SupermodularAbove r U) (hinc : ∀ i ∉ U, r U + 1 ≤ r (insert i U))
    (C : Finset V) (hC : Disjoint U C) : r U + C.card ≤ r (U ∪ C) := by
  induction C using Finset.induction_on with
  | empty => simp
  | @insert i C hi ih =>
    have hdis : Disjoint U C := hC.mono_right (Finset.subset_insert _ _)
    have hiU : i ∉ U := fun h => (Finset.disjoint_left.mp hC) h (Finset.mem_insert_self _ _)
    have hih := ih hdis
    have hs := hr (U ∪ C) (insert i U) Finset.subset_union_left (Finset.subset_insert _ _)
    have hun : (U ∪ C) ∪ insert i U = insert i (U ∪ C) := by ext x; simp; tauto
    have hin : (U ∪ C) ∩ insert i U = U := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨hxU | hxC, hxi | hxU'⟩
        · exact hxU
        · exact hxU
        · subst x; exact (hi hxC).elim
        · exact hxU'
      · intro hx; exact ⟨Or.inl hx, Or.inr hx⟩
    rw [hun, hin] at hs
    have hs1 := hinc i hiU
    rw [Finset.card_insert_of_notMem hi, Finset.union_insert]
    omega

theorem supermodular_rank_codimension_bound {r : Finset V → ℕ} {U : Finset V}
    (hr : SupermodularAbove r U) (hinc : ∀ i ∉ U, r U + 1 ≤ r (insert i U)) :
    r U + (Fintype.card V - U.card) ≤ r Finset.univ := by
  simpa only [Finset.card_compl, Finset.card_univ, Finset.union_compl] using
    supermodular_rank_increments hr hinc Uᶜ disjoint_compl_right

/-- A zero rank increment at an equigenerated larger localization forces the
whole ambient exponent family to be unchanged; the added variables do not occur. -/
theorem localize_eq_of_rank_eq {B : Family V} (hB : B.Nonempty)
    {U W : Finset V} (hUW : U ⊆ W)
    (he : ∃ d, Equigenerated (localize B W) d) (hr : lowerRank B U = lowerRank B W) :
    localize B W = localize B U := by
  obtain ⟨d, hd⟩ := he
  have hsupp : ∀ b ∈ localize B W, project U b = b := by
    intro b hb
    apply eq_of_le_of_degree_eq (project_le U b)
    rw [degree_project]
    apply le_antisymm
    · simpa only [degree_project] using degree_mono (project_le U b)
    · rw [equigenerated_localize_degree hB hd hb, ← hr]
      exact localize_sum_ge hUW hb
  apply family_eq_of_contains_iff (localize_antichain B W) (localize_antichain B U)
  intro a
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, hcb⟩ := localize_member hb
    apply (contains_localize B U a).mpr
    refine ⟨c, hc, ?_⟩
    have hproj : project U c = b := by
      rw [← project_project hUW c, hcb, hsupp b hb]
    rwa [hproj]
  · intro ha
    obtain ⟨c, hc, hca⟩ := (contains_localize B U a).mp ha
    obtain ⟨b, hb, hbc⟩ := localize_below (U := W) hc
    refine ⟨b, hb, ?_⟩
    have hp := project_mono U hbc
    rw [hsupp b hb, project_project hUW] at hp
    exact hp.trans hca

end Characterizations
