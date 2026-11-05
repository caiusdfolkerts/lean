import CommAlg.Polymatroid.LinearQuotients
import CommAlg.Polymatroid.HomogenizedBases
import CommAlg.KoszulComplex.FaceCombinatorics

/-! # Bounding every actual linear quotient by the homological rank gap

For a base `b`, add one to each colon variable. The resulting exponent obeys
the full partition inequalities. The key strict inequality on a nonempty set
of colon variables follows by choosing its largest variable: a legal transfer
into that variable must have its donor still larger.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem subsetSum_faceExponent (C A : Finset V) :
    subsetSum (Koszul.faceExponent C) A = (A ∩ C).card := by
  simp [subsetSum, Koszul.faceExponent_apply, ← Finset.sum_filter]

@[simp] theorem degree_faceExponent (C : Finset V) :
    (Koszul.faceExponent C).degree = C.card := by
  rw [← subsetSum_univ, subsetSum_faceExponent, univ_inter]

def revlexColonWitness (B : Family V) (b : Exponent V) : Exponent V :=
  b + Koszul.faceExponent (revlexColonVariables B b)

/-- A nonempty set of colon variables cannot be tight at the current base. -/
theorem rankBase_strict_on_colon_subset (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty)
    (hAC : A ⊆ revlexColonVariables (rankBases g) b) : subsetSum b A < g A := by
  have hbound := ((mem_rankBases g b).mp hb).2 A
  by_contra hbad
  have htight : subsetSum b A = g A := by omega
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  obtain ⟨i, hji, hbi, hex⟩ :=
    (mem_revlexColonVariables (rankBases g) b j).mp (hAC hjA)
  have hiA : i ∈ A := by
    by_contra hiA
    have hs := subsetSum_exchange b i j hbi A
    rw [if_neg hiA, if_pos hjA] at hs
    have hc := ((mem_rankBases g _).mp hex).2 A
    omega
  exact (not_lt_of_ge (A.le_max' i hiA)) hji

theorem revlexColonWitness_subset_bound (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (revlexColonWitness (rankBases g) b) A ≤ g A + A.card - 1 := by
  rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
  have hbA := ((mem_rankBases g b).mp hb).2 A
  have hc : (A ∩ revlexColonVariables (rankBases g) b).card ≤ A.card :=
    card_le_card inter_subset_left
  by_cases hAC : A ⊆ revlexColonVariables (rankBases g) b
  · have hlt := rankBase_strict_on_colon_subset g hb hA hAC
    omega
  · have hlt : (A ∩ revlexColonVariables (rankBases g) b).card < A.card := by
      by_contra h
      have he : A ∩ revlexColonVariables (rankBases g) b = A :=
        eq_of_subset_of_card_le inter_subset_left (by omega)
      apply hAC
      rw [← he]
      exact inter_subset_right
    omega

theorem revlexColonWitness_upperFeasible (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    UpperFeasible (universalAugmentedRank g) (revlexColonWitness (rankBases g) b) :=
  (universal_bounds_iff g _).mp (fun _ hA => revlexColonWitness_subset_bound g hb hA)

/-- The size of each genuine colon generating set is bounded by the exact
partition-rank gap. There is no activity hypothesis. -/
theorem revlexColonVariables_card_le_shiftLength (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    (revlexColonVariables (rankBases g) b).card ≤ shiftLength g := by
  have h := revlexColonWitness_upperFeasible g hb univ
  rw [subsetSum_univ, revlexColonWitness, map_add, degree_faceExponent,
    ((mem_rankBases g b).mp hb).1] at h
  have hp := shiftLength_add_degree g
  omega

/-- The same construction is a base in the exact shift layer of the colon
cardinality, which later gives a genuine Tor nonvanishing witness. -/
theorem revlexColonWitness_mem_shiftFamily (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    revlexColonWitness (rankBases g) b ∈
      rankShiftFamily g (revlexColonVariables (rankBases g) b).card := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rw [revlexColonWitness, map_add, degree_faceExponent, ((mem_rankBases g b).mp hb).1]
  · intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g _ (nonempty_iff_ne_empty.mpr hA)]
    refine le_min ?_ (revlexColonWitness_upperFeasible g hb A)
    rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
    exact Nat.add_le_add (((mem_rankBases g b).mp hb).2 A)
      (card_le_card inter_subset_right)

end CommAlg.Polymatroid
