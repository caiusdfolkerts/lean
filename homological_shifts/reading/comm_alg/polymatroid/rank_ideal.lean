import CommAlg.Polymatroid.CloneRank

/-! # From rank inequalities to actual monomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetSum_add_compl (a : Exponent V) (U : Finset V) :
    subsetSum a U + subsetSum a Uᶜ = a.degree := by
  simpa only [subsetSum, Finsupp.degree_eq_sum] using U.sum_add_sum_compl a

def RankFunction.lower (g : RankFunction V) (U : Finset V) : ℕ :=
  g Finset.univ - g Uᶜ

theorem RankFunction.lower_add_compl (g : RankFunction V) (U : Finset V) :
    g.lower U + g Uᶜ = g Finset.univ :=
  Nat.sub_add_cancel (g.monotone (Finset.subset_univ _))

@[simp] theorem RankFunction.lower_empty (g : RankFunction V) : g.lower ∅ = 0 := by
  simp [RankFunction.lower]

@[simp] theorem RankFunction.lower_univ (g : RankFunction V) :
    g.lower Finset.univ = g Finset.univ := by simp [RankFunction.lower]

theorem RankFunction.lower_le (g : RankFunction V) (U : Finset V) :
    g.lower U ≤ g Finset.univ := Nat.sub_le _ _

theorem RankFunction.lower_supermodular (g : RankFunction V) : Supermodular g.lower := by
  intro U W
  have hs := g.submodular Uᶜ Wᶜ
  have hU := g.lower_add_compl U
  have hW := g.lower_add_compl W
  have hUn := g.lower_add_compl (U ∪ W)
  have hIn := g.lower_add_compl (U ∩ W)
  simp only [compl_union, compl_inter] at hUn hIn
  omega

def UpperFeasible (g : RankFunction V) (a : Exponent V) : Prop :=
  ∀ U, subsetSum a U ≤ g U

theorem upperFeasible_iff_lowerFeasible (g : RankFunction V) {a : Exponent V}
    (ha : a.degree = g Finset.univ) :
    UpperFeasible g a ↔ LowerFeasible g.lower a := by
  constructor
  · intro h U
    have hu := h Uᶜ
    have hs := subsetSum_add_compl a U
    have hg := g.lower_add_compl U
    omega
  · intro h U
    have hu := h Uᶜ
    have hs := subsetSum_add_compl a U
    have hg := g.lower_add_compl Uᶜ
    simp only [compl_compl] at hg
    omega

theorem single_one_le {a : Exponent V} {i : V} (hi : 0 < a i) :
    Finsupp.single i 1 ≤ a := by
  intro j
  by_cases hji : j = i
  · subst j; simpa using (show 1 ≤ a i by omega)
  · simp [Finsupp.single_apply, hji, Ne.symm hji]

theorem subsetSum_sub_single {a : Exponent V} {i : V} (hi : 0 < a i) (U : Finset V) :
    subsetSum (a - Finsupp.single i 1) U + (if i ∈ U then 1 else 0) = subsetSum a U := by
  have he := tsub_add_cancel_of_le (single_one_le hi)
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  simpa [subsetSum, Finset.sum_add_distrib, Finsupp.single_apply] using hs

theorem failed_decrement_tight {r : Finset V → ℕ} {a : Exponent V}
    (ha : LowerFeasible r a) {i : V} (hi : 0 < a i)
    (hbad : ¬ LowerFeasible r (a - Finsupp.single i 1)) :
    ∃ U, Tight r a U ∧ i ∈ U := by
  simp only [LowerFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hs := subsetSum_sub_single hi U
  have hf := ha U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    omega
  refine ⟨U, ?_, hiU⟩
  rw [if_pos hiU] at hs
  unfold Tight
  omega

theorem tight_cover {r : Finset V → ℕ} (hr : Supermodular r) (hr0 : r ∅ = 0)
    {a : Exponent V} (ha : LowerFeasible r a) (D : Finset V)
    (h : ∀ i ∈ D, ∃ U, Tight r a U ∧ i ∈ U) :
    ∃ U, Tight r a U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [Tight, hr0], Finset.empty_subset _⟩
  | @insert i D hi ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, hiW⟩ := h i (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (tight_union_inter hr ha hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hiW,
        hDU.trans Finset.subset_union_left⟩⟩

/-- Integral descent to a base: all larger feasible vectors dominate a
feasible vector of the precise total rank. -/
theorem exists_lower_base_below {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d)
    {a : Exponent V} (ha : LowerFeasible r a) :
    ∃ b, b ≤ a ∧ b.degree = d ∧ LowerFeasible r b := by
  let T : Set (Exponent V) := {b | b ≤ a ∧ LowerFeasible r b}
  have hfin : T.Finite := (Set.finite_Iic a).subset (fun _ h => h.1)
  obtain ⟨b, hb, hmin⟩ := hfin.exists_minimal ⟨a, le_rfl, ha⟩
  have hcover : ∀ i ∈ b.support, ∃ U, Tight r b U ∧ i ∈ U := by
    intro i hi
    have hip : 0 < b i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    apply failed_decrement_tight hb.2 hip
    intro hgood
    have hmem : b - Finsupp.single i 1 ∈ T := ⟨tsub_le_self.trans hb.1, hgood⟩
    have hle := hmin hmem tsub_le_self
    have hc := hle i
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hc
    omega
  obtain ⟨U, hU, hsupp⟩ := tight_cover hr hr0 hb.2 b.support hcover
  have hp : project U b = b := by
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have hb0 : b i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hsupp h))
      simp [hi, hb0]
  have hdegU : b.degree = subsetSum b U := by rw [← degree_project, hp]
  have hlo := hb.2 Finset.univ
  have hhi := hrle U
  simp only [subsetSum_univ, hrd] at hlo
  unfold Tight at hU
  exact ⟨b, hb.1, by omega, hb.2⟩

theorem lowerRank_add_upperRank_compl {B : Family V} (hBne : B.Nonempty) {d : ℕ}
    (hdeg : Equigenerated B d) (U : Finset V) :
    lowerRank B U + upperRank B Uᶜ = d := by
  obtain ⟨a, ha, hamin⟩ := lowerRank_attained hBne U
  obtain ⟨b, hb, hbmax⟩ := upperRank_attained hBne Uᶜ
  have haSum := subsetSum_add_compl a U
  have hbSum := subsetSum_add_compl b U
  have hbMin := lowerRank_le hb U
  have haMax := le_upperRank ha Uᶜ
  have haDeg := hdeg a ha
  have hbDeg := hdeg b hb
  omega

theorem lowerRank_eq_canonical_lower (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (U : Finset V) :
    lowerRank B U = (canonicalRank B hBne d hdeg hB).lower U := by
  have hsum := lowerRank_add_upperRank_compl hBne hdeg U
  have htop : upperRank B Finset.univ = d := by
    obtain ⟨a, ha, he⟩ := upperRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg a ha] using he.symm
  change lowerRank B U = upperRank B Finset.univ - upperRank B Uᶜ
  omega

/-- Complete monomial membership for an arbitrary exchange family. -/
theorem contains_iff_canonical_lower (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (a : Exponent V) :
    Contains B a ↔ LowerFeasible (lowerRank B) a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    let g := canonicalRank B hBne d hdeg hB
    have hr : lowerRank B = g.lower := funext (lowerRank_eq_canonical_lower B hBne d hdeg hB)
    have htop : g Finset.univ = d := by
      change upperRank B Finset.univ = d
      obtain ⟨b, hb, he⟩ := upperRank_attained hBne Finset.univ
      simpa only [subsetSum_univ, hdeg b hb] using he.symm
    have ha' : LowerFeasible g.lower a := by rwa [← hr]
    obtain ⟨b, hba, hbdeg, hb⟩ := exists_lower_base_below g.lower_supermodular
      g.lower_empty g.lower_univ (g.lower_le) ha'
    refine ⟨b, (mem_iff_canonical_rank B hBne d hdeg hB b).mpr ⟨hbdeg.trans htop, ?_⟩, hba⟩
    exact (upperFeasible_iff_lowerFeasible g hbdeg).mpr hb

end CommAlg.Polymatroid
