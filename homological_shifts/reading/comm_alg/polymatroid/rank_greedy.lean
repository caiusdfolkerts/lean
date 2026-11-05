import CommAlg.Polymatroid.RankBases

/-! # Base extension and recovery of every canonical rank value -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def UpperTight (g : RankFunction V) (a : Exponent V) (U : Finset V) : Prop :=
  subsetSum a U = g U

theorem upper_tight_union_inter (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) {U W : Finset V}
    (hU : UpperTight g a U) (hW : UpperTight g a W) :
    UpperTight g a (U ∪ W) ∧ UpperTight g a (U ∩ W) := by
  have hm := subsetSum_union_inter a U W
  have hs := g.submodular U W
  have h1 := ha (U ∪ W)
  have h2 := ha (U ∩ W)
  unfold UpperTight at *
  omega

theorem upper_failed_increment (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (i : V) (hbad : ¬ UpperFeasible g (a + Finsupp.single i 1)) :
    ∃ U, UpperTight g a U ∧ i ∈ U := by
  simp only [UpperFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hs : subsetSum (a + Finsupp.single i 1) U =
      subsetSum a U + (if i ∈ U then 1 else 0) := by
    rw [subsetSum_add]
    simp [subsetSum, Finsupp.single_apply]
  have hf := ha U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    omega
  rw [if_pos hiU] at hs
  exact ⟨U, by unfold UpperTight; omega, hiU⟩

theorem upper_tight_cover (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (D : Finset V)
    (h : ∀ i ∈ D, ∃ U, UpperTight g a U ∧ i ∈ U) :
    ∃ U, UpperTight g a U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [UpperTight], Finset.empty_subset _⟩
  | @insert i D hi ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, hiW⟩ := h i (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (upper_tight_union_inter g ha hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hiW,
        hDU.trans Finset.subset_union_left⟩⟩

theorem upperFeasible_le_const (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : a ≤ constExponent (g Finset.univ) := by
  intro i
  have hi := ha {i}
  simp only [subsetSum, Finset.sum_singleton] at hi
  exact hi.trans (g.monotone (Finset.subset_univ _))

theorem exists_rankBase_above (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : ∃ b, a ≤ b ∧ IsRankBase g b := by
  let T : Set (Exponent V) := {b | a ≤ b ∧ UpperFeasible g b}
  have hfin : T.Finite := (Set.finite_Iic (constExponent (g Finset.univ))).subset
    (fun _ h => upperFeasible_le_const g h.2)
  obtain ⟨b, hb, hmax⟩ := hfin.exists_maximal ⟨a, le_rfl, ha⟩
  have hcover : ∀ i ∈ (Finset.univ : Finset V), ∃ U, UpperTight g b U ∧ i ∈ U := by
    intro i hi
    apply upper_failed_increment g hb.2 i
    intro hgood
    have hmem : b + Finsupp.single i 1 ∈ T := ⟨hb.1.trans (le_add_right le_rfl), hgood⟩
    have hle := hmax hmem (le_add_right le_rfl)
    have hc := hle i
    simp at hc
  obtain ⟨U, hU, hfull⟩ := upper_tight_cover g hb.2 Finset.univ hcover
  have he : U = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) hfull
  have hdeg : b.degree = g Finset.univ := by
    simpa only [UpperTight, he, subsetSum_univ] using hU
  exact ⟨b, hb.1, hdeg, hb.2⟩

def RankFunction.restrict (g : RankFunction V) (A : Finset V) : RankFunction V where
  toFun U := g (U ∩ A)
  empty := by simp
  monotone := by
    intro U W hUW
    apply g.monotone
    exact Finset.inter_subset_inter_right hUW
  submodular := by
    intro U W
    have hu : (U ∪ W) ∩ A = (U ∩ A) ∪ (W ∩ A) := by ext x; simp; tauto
    have hi : (U ∩ W) ∩ A = (U ∩ A) ∩ (W ∩ A) := by ext x; simp <;> tauto
    rw [hu, hi]
    exact g.submodular _ _

/-- Every individual upper bound is attained by an integer base. -/
theorem exists_rankBase_attaining (g : RankFunction V) (U : Finset V) :
    ∃ a, IsRankBase g a ∧ subsetSum a U = g U := by
  obtain ⟨b, hb⟩ := rankBases_nonempty (g.restrict U)
  have hb := (mem_rankBases _ b).mp hb
  have hbU : project U b = b := by
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have hs := hb.2 {i}
      have he : ({i} : Finset V) ∩ U = ∅ := by ext j; simp; aesop
      change subsetSum b {i} ≤ g ({i} ∩ U) at hs
      simp only [subsetSum, Finset.sum_singleton, he, RankFunction.map_empty] at hs
      have hzero : b i = 0 := Nat.eq_zero_of_le_zero hs
      simp [hi, hzero]
  have hbdeg : b.degree = g U := by
    simpa only [RankFunction.restrict, Finset.univ_inter] using hb.1
  have hbupper : UpperFeasible g b := by
    intro W
    exact (hb.2 W).trans (g.monotone Finset.inter_subset_left)
  obtain ⟨a, hba, ha⟩ := exists_rankBase_above g hbupper
  have hsum : subsetSum b U = g U := by rw [← degree_project, hbU, hbdeg]
  have hsumle : subsetSum b U ≤ subsetSum a U := Finset.sum_le_sum (fun i _ => hba i)
  exact ⟨a, ha, Nat.le_antisymm (ha.2 U) (hsum ▸ hsumle)⟩

@[simp] theorem upperRank_rankBases (g : RankFunction V) (U : Finset V) :
    upperRank (rankBases g) U = g U := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact ((mem_rankBases g a).mp ha).2 U
  · obtain ⟨a, ha, hU⟩ := exists_rankBase_attaining g U
    rw [← hU]
    exact le_upperRank ((mem_rankBases g a).mpr ha) U

theorem rankBases_injective : Function.Injective (rankBases (V := V)) := by
  intro g h he
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      funext U
      have hg := upperRank_rankBases (RankFunction.mk g g0 gm gs) U
      have hh := upperRank_rankBases (RankFunction.mk h h0 hm hs) U
      rw [he] at hg
      exact hg.symm.trans hh

end CommAlg.Polymatroid
