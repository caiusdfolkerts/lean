import Characterizations.FiniteHoles
import Characterizations.SmallCases

/-! # Exact support identities for coordinate minors -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem project_eq_self_iff_support_subset (a : Exponent V) (U : Finset V) :
    project U a = a ↔ a.support ⊆ U := by
  constructor
  · intro h i hi
    by_contra hn
    have he := congrArg (fun b : Exponent V => b i) h
    simp only [project_apply, if_neg hn] at he
    exact (Finsupp.mem_support_iff.mp hi) he.symm
  · intro h
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have haz : a i = 0 := Finsupp.notMem_support_iff.mp (fun hc => hi (h hc))
      simp [hi,haz]

theorem supported_of_subsetSum_compl_zero {a : Exponent V} {U : Finset V}
    (h : subsetSum a Uᶜ = 0) : project U a = a := by
  apply (project_eq_self_iff_support_subset a U).mpr
  intro i hi
  by_contra hiU
  have hle : a i ≤ subsetSum a Uᶜ := Finset.single_le_sum
    (fun j _ => Nat.zero_le (a j)) (Finset.mem_compl.mpr hiU)
  exact (Finsupp.mem_support_iff.mp hi) (by omega)

theorem subsetSum_supported_inter {a : Exponent V} {U : Finset V}
    (h : project U a = a) (W : Finset V) : subsetSum a W = subsetSum a (W ∩ U) := by
  calc
    subsetSum a W = subsetSum (project U a) W := by rw [h]
    _ = _ := subsetSum_project_inter U W a

theorem lowerRank_supported_inter {B : Family V} (hB : B.Nonempty) (U : Finset V)
    (hs : ∀ a ∈ B, project U a = a) (W : Finset V) :
    lowerRank B W = lowerRank B (W ∩ U) := by
  apply le_antisymm
  · obtain ⟨a,ha,he⟩ := lowerRank_attained hB (W ∩ U)
    exact (lowerRank_le ha W).trans_eq ((subsetSum_supported_inter (hs a ha) W).trans he)
  · obtain ⟨a,ha,he⟩ := lowerRank_attained hB W
    exact (lowerRank_le ha (W ∩ U)).trans_eq ((subsetSum_supported_inter (hs a ha) W).symm.trans he)

theorem lowerRank_on_support {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a) :
    lowerRank B U = d := by
  obtain ⟨a,ha,he⟩ := lowerRank_attained hB U
  calc
    lowerRank B U = subsetSum a U := he.symm
    _ = a.degree := by rw [← degree_project, hs a ha]
    _ = d := hd a ha

theorem lowerBase_supported {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a)
    {a : Exponent V} (ha : a ∈ lowerBaseFamily (lowerRank B) d) : project U a = a := by
  obtain ⟨had,hlo⟩ := (mem_lowerBaseFamily _ _ _).mp ha
  apply eq_of_le_of_degree_eq (project_le U a)
  apply le_antisymm (degree_mono (project_le U a))
  rw [degree_project, had, ← lowerRank_on_support hB hd U hs]
  exact hlo U

theorem supported_equigenerated_polymatroidal_card_le_one {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (U : Finset V) (hs : ∀ a ∈ B, project U a = a)
    (hc : U.card ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hd⟩,?_⟩
  intro a ha b hb i hi
  obtain ⟨j,hj⟩ := exists_surplus ((hd a ha).trans (hd b hb).symm) hi
  have hiU : i ∈ U := (project_eq_self_iff_support_subset a U).mp (hs a ha)
    (Finsupp.mem_support_iff.mpr (by omega))
  have hjU : j ∈ U := (project_eq_self_iff_support_subset b U).mp (hs b hb)
    (Finsupp.mem_support_iff.mpr (by omega))
  have hij : i ≠ j := by intro he; subst j; omega
  have hp : ({i,j} : Finset V) ⊆ U :=
    Finset.insert_subset_iff.mpr ⟨hiU,Finset.singleton_subset_iff.mpr hjU⟩
  have hcard := Finset.card_le_card hp
  simp only [Finset.card_pair hij] at hcard
  omega

end Characterizations
