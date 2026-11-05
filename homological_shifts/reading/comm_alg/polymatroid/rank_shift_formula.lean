import CommAlg.Polymatroid.UniversalRank
import CommAlg.Polymatroid.RankGreedy

/-! # The right-hand side of the homological-shift rank formula

`rankShiftIdeal` is the explicitly described ideal on the right-hand side of
Theorem 1.2. It is not a definition of a homological shift: the separate
graded-Tor theorem proves that the genuine homological shift equals it.
This module proves its exact monomial membership and all partition inequalities,
including inactive variables and the unit rank.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankShiftFamily (g : RankFunction V) (i : ℕ) : Family V :=
  if universalHomologicalRank g i univ = g univ + i then
    rankBases (universalHomologicalRank g i) else ∅

def rankShiftIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) (i : ℕ) :
    Ideal (MvPolynomial V k) :=
  if universalHomologicalRank g i univ = g univ + i then
    rankIdeal k (universalHomologicalRank g i) else ⊥

theorem rankShiftIdeal_eq_monomialIdeal (k : Type*) [CommSemiring k]
    (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i = monomialIdeal k (rankShiftFamily g i) := by
  unfold rankShiftIdeal rankShiftFamily
  split_ifs
  · rfl
  · simp [monomialIdeal]

theorem rankShiftFamily_nonempty_iff (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ universalHomologicalRank g i univ = g univ + i := by
  unfold rankShiftFamily
  split_ifs with h
  · simp [h, rankBases_nonempty]
  · simp [h]

theorem rankShiftFamily_equigenerated (g : RankFunction V) (i : ℕ) :
    Equigenerated (rankShiftFamily g i) (g univ + i) := by
  intro a ha
  unfold rankShiftFamily at ha
  split_ifs at ha with h
  · exact ((mem_rankBases _ a).mp ha).1.trans h
  · simp at ha

theorem mem_rankShiftFamily_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔
      a.degree = g univ + i ∧ UpperFeasible (universalHomologicalRank g i) a := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · simp [rankShiftFamily, h, mem_rankBases, IsRankBase]
  · have hle := universalHomologicalRank_le_add g i univ
    simp only [rankShiftFamily, if_neg h, notMem_empty, false_iff, not_and]
    intro hdeg hbound
    have hb := hbound univ
    rw [subsetSum_univ, hdeg] at hb
    omega

theorem rankShiftFamily_polymatroidal (g : RankFunction V) (i : ℕ) :
    IsPolymatroidal (rankShiftFamily g i) := by
  unfold rankShiftFamily
  split_ifs
  · exact rankBases_polymatroidal _
  · exact ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩

theorem rankShiftFamily_upperRank (g : RankFunction V) (i : ℕ)
    (h : (rankShiftFamily g i).Nonempty) (A : Finset V) :
    upperRank (rankShiftFamily g i) A = universalHomologicalRank g i A := by
  rw [rankShiftFamily, if_pos ((rankShiftFamily_nonempty_iff g i).mp h)]
  exact upperRank_rankBases _ A

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_mem_rankShiftIdeal_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      ∀ A, g univ + i ≤ subsetSum a Aᶜ + universalHomologicalRank g i A := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · rw [rankShiftIdeal, if_pos h, monomial_mem_rankIdeal_iff]
    constructor
    · intro hb A
      have hB := hb Aᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl Aᶜ
      simp only [compl_compl, h] at hL
      omega
    · intro hb U
      have hB := hb Uᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl U
      simp only [compl_compl] at hB
      rw [h] at hL
      omega
  · rw [rankShiftIdeal, if_neg h]
    constructor
    · intro hb
      have : False := by simpa using hb
      exact this.elim
    · intro hb
      have hB := hb univ
      simp only [compl_univ, subsetSum_empty, Nat.zero_add] at hB
      have hU := universalHomologicalRank_le_add g i univ
      omega

/-- Exact expanded membership, valid even when the indicated shift is zero.
Every block is nonempty because `P` is an actual `Finpartition A`. -/
theorem monomial_mem_rankShiftIdeal_partition_iff (g : RankFunction V) (i : ℕ)
    (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      g univ + i ≤ a.degree ∧ LowerFeasible g.lower a ∧
        ∀ A, A.Nonempty → ∀ P : Finpartition A,
          g univ + i + P.parts.card ≤ subsetSum a Aᶜ + A.card + ∑ C ∈ P.parts, g C := by
  rw [monomial_mem_rankShiftIdeal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h ∅
    · intro U
      have hb := h Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      simp only [compl_compl] at hb
      omega
    · intro A hA P
      have hb := h A
      have hR : universalHomologicalRank g i A ≤ universalAugmentedRank g A :=
        shiftRankValue_le_u g (universalAugmentedRank g) i A
      have hP := universalAugmentedRank_le_cost g P
      have hCost := cardinalLift_cost_add_parts g P
      omega
  · rintro ⟨hdeg, hLower, hParts⟩ A
    by_cases hA : A = ∅
    · simpa [hA] using hdeg
    have hA' := Finset.nonempty_iff_ne_empty.mpr hA
    have hL := hLower Aᶜ
    have hLC := g.lower_add_compl Aᶜ
    simp only [compl_compl] at hLC
    obtain ⟨P, hP⟩ := universalAugmentedRank_attained g A
    have hPart := hParts A hA' P
    have hCost := cardinalLift_cost_add_parts g P
    rw [hP] at hCost
    rw [universalHomologicalRank_apply g i hA']
    omega

theorem mem_rankShiftIdeal_iff_coeff (g : RankFunction V) (i : ℕ)
    (f : MvPolynomial V k) :
    f ∈ rankShiftIdeal k g i ↔
      ∀ a ∈ f.support, MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i := by
  simp_rw [rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
  exact mem_monomialIdeal_iff _ _

theorem rankShiftIdeal_le_rankIdeal (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≤ rankIdeal k g := by
  intro f hf
  apply (mem_monomialIdeal_iff (rankBases g) f).mpr
  intro a ha
  have hmon := (mem_rankShiftIdeal_iff_coeff g i f).mp hf a ha
  exact (contains_rankBases_iff g a).mpr
    ((monomial_mem_rankShiftIdeal_partition_iff g i a).mp hmon).2.1

end Ideals

end CommAlg.Polymatroid
