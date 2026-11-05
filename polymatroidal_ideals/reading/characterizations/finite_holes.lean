import Characterizations.RankIncrements
import Characterizations.AmbientLocalization
import Characterizations.IntegralClosure

/-! # Finite holes in a minimal coordinate obstruction -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetSum_project_inter (U W : Finset V) (a : Exponent V) :
    subsetSum (project U a) W = subsetSum a (W ∩ U) := by
  simp only [subsetSum, project_apply]
  rw [Finset.sum_ite_mem]

theorem lowerRank_localize_inter {B : Family V} (hB : B.Nonempty) (U W : Finset V) :
    lowerRank (localize B U) W = lowerRank B (W ∩ U) := by
  have hsame : lowerRank (localize B U) W = lowerRank (localize B U) (W ∩ U) := by
    have hs : ∀ b ∈ localize B U, subsetSum b W = subsetSum b (W ∩ U) := by
      intro b hb
      calc
        subsetSum b W = subsetSum (project U b) W := by rw [localize_supported hb]
        _ = _ := subsetSum_project_inter U W b
    apply le_antisymm
    · obtain ⟨b, hb, he⟩ := lowerRank_attained (localize_nonempty hB U) (W ∩ U)
      calc
        lowerRank (localize B U) W ≤ subsetSum b W := lowerRank_le hb W
        _ = lowerRank (localize B U) (W ∩ U) := (hs b hb).trans he
    · obtain ⟨b, hb, he⟩ := lowerRank_attained (localize_nonempty hB U) W
      calc
        lowerRank (localize B U) (W ∩ U) ≤ subsetSum b (W ∩ U) := lowerRank_le hb _
        _ = lowerRank (localize B U) W := (hs b hb).symm.trans he
  rw [hsame, lowerRank_localize hB Finset.inter_subset_right]

theorem lowerFeasible_project_mem {B : Family V} (hB : B.Nonempty) {a : Exponent V}
    (ha : LowerFeasible (lowerRank B) a) (U : Finset V)
    (hp : IsPolymatroidal (localize B U)) : Contains (localize B U) (project U a) := by
  obtain ⟨d, hd⟩ := hp.1
  apply (contains_iff_canonical_lower _ (localize_nonempty hB U) d hd hp _).mpr
  intro W
  rw [lowerRank_localize_inter hB U W, subsetSum_project_inter U W a]
  exact ha (W ∩ U)

theorem hole_coordinate_lt_degree {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    {a : Exponent V} (ha : LowerFeasible (lowerRank B) a) (hout : ¬ Contains B a)
    (i : V) : a i < d := by
  by_contra hn
  have hdi : d ≤ a i := by omega
  let U : Finset V := Finset.univ.erase i
  have hU : U ⊂ Finset.univ := Finset.erase_ssubset (Finset.mem_univ i)
  obtain ⟨b, hb, hba⟩ := (contains_localize B U _).mp
    (lowerFeasible_project_mem hB ha U (hloc U hU))
  apply hout
  refine ⟨b, hb, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact (coordinate_le_degree b i).trans ((hd b hb).le.trans hdi)
  · have hjU : j ∈ U := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    simpa only [project_apply, if_pos hjU] using hba j

def holeSet (B : Family V) : Set (Exponent V) :=
  {a | LowerFeasible (lowerRank B) a ∧ ¬ Contains B a}

theorem holeSet_finite {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    (holeSet B).Finite := by
  apply (Set.finite_Iic (constExponent d)).subset
  intro a ha i
  exact (hole_coordinate_lt_degree hB hd hloc ha.1 ha.2 i).le

theorem exists_top_hole {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hh : (holeSet B).Nonempty) :
    ∃ a ∈ holeSet B, (∀ b ∈ holeSet B, b.degree ≤ a.degree) ∧ d ≤ a.degree ∧
      ∀ i, Contains B (a + Finsupp.single i 1) := by
  obtain ⟨a, ha, hmax⟩ := (holeSet_finite hB hd hloc).exists_maximalFor
    (fun a : Exponent V => a.degree) _ hh
  have hbound : ∀ b ∈ holeSet B, b.degree ≤ a.degree := by
    intro b hb
    by_contra hn
    have hab : a.degree ≤ b.degree := by omega
    exact (not_le_of_gt (by omega : a.degree < b.degree)) (hmax hb hab)
  refine ⟨a, ha, hbound, ?_, ?_⟩
  · have h := ha.1 Finset.univ
    rw [lowerRank_univ_of_equigenerated hB hd, subsetSum_univ] at h
    exact h
  · intro i
    by_contra hout
    have hlo : LowerFeasible (lowerRank B) (a + Finsupp.single i 1) := by
      intro U
      exact (ha.1 U).trans (Finset.sum_le_sum (fun j _ => by simp only [Finsupp.add_apply]; omega))
    have h := hbound _ ⟨hlo, hout⟩
    simp only [map_add, Finsupp.degree_single] at h
    omega

end Characterizations
