import Characterizations.RankIncrements
import Characterizations.AmbientLocalization

/-! # The sharp codimension range needed to force local equigeneration -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem localize_equigenerated_of_rank_zero {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (hr : lowerRank B U = 0) : Equigenerated (localize B U) 0 := by
  obtain ⟨a,ha,hmin⟩ := lowerRank_attained hB U
  have hpa : project U a = 0 := (Finsupp.degree_eq_zero_iff _).mp
    ((degree_project U a).trans (hmin.trans hr))
  obtain ⟨b,hb,hba⟩ := localize_below (U := U) ha
  have hb0 : b = 0 := le_antisymm (hpa ▸ hba) zero_le
  intro c hc
  have hbc := localize_antichain B U b hb c hc (by rw [hb0]; exact zero_le)
  rw [← hbc, hb0]
  simp

theorem localize_equigenerated_of_card_le_one {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (hcard : U.card ≤ 1) : ∃ d, Equigenerated (localize B U) d := by
  obtain ⟨a,ha⟩ := localize_nonempty hB U
  refine ⟨a.degree,?_⟩
  intro b hb
  have hsame : a = b := by
    by_cases hU : U.Nonempty
    · obtain ⟨i,hi⟩ := hU
      have hsingle : U = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj => by
        by_contra hji
        have htwo : ({i,j} : Finset V) ⊆ U :=
          Finset.insert_subset_iff.mpr ⟨hi,Finset.singleton_subset_iff.mpr hj⟩
        have hc := Finset.card_le_card htwo
        simp [Ne.symm hji] at hc
        omega⟩
      have hcomp (c e : Exponent V) (hc : c ∈ localize B U) (he : e ∈ localize B U)
          (hce : c i ≤ e i) : c ≤ e := by
        intro j
        by_cases hji : j = i
        · simpa [hji] using hce
        · have hcj := congrArg (fun f : Exponent V => f j) (localize_supported hc)
          have hjU : j ∉ U := by simpa [hsingle] using hji
          simp only [project_apply, if_neg hjU] at hcj
          rw [← hcj]
          exact Nat.zero_le _
      rcases le_total (a i) (b i) with h | h
      · exact localize_antichain B U a ha b hb (hcomp a b ha hb h)
      · exact (localize_antichain B U b hb a ha (hcomp b a hb ha h)).symm
    · have hU0 := Finset.not_nonempty_iff_eq_empty.mp hU
      have ha0 := localize_supported ha
      have hb0 := localize_supported hb
      simp only [hU0, project_empty] at ha0 hb0
      exact ha0.symm.trans hb0
  exact congrArg Finsupp.degree hsame.symm

theorem maximal_nonequigenerated_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ ∃ e, Equigenerated (localize B U) e)
    (hmax : ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hbad (localize_equigenerated_of_card_le_one hB U (by omega))
  have hpos : 1 ≤ lowerRank B U := by
    by_contra h
    exact hbad ⟨0,localize_equigenerated_of_rank_zero hB U (by omega)⟩
  have hinc : ∀ i ∉ U, lowerRank B U+1 ≤ lowerRank B (insert i U) := by
    intro i hi
    have hsub : U ⊂ insert i U := Finset.ssubset_insert hi
    have he := hmax _ hsub
    have hm := lowerRank_mono hB (Finset.subset_insert i U)
    by_contra h
    have hr : lowerRank B U = lowerRank B (insert i U) := by omega
    have hf := localize_eq_of_rank_eq hB (Finset.subset_insert i U) he hr
    rw [hf] at he
    exact hbad he
  have hbound := supermodular_rank_codimension_bound (lowerRank_supermodular_above hB U hmax) hinc
  rw [lowerRank_univ_of_equigenerated hB hd] at hbound
  exact ⟨hcard,hpos,hbound⟩

theorem locallyEquigenerated_of_band_tests {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (htest : ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      ∃ e, Equigenerated (localize B U) e) : LocallyEquigenerated B := by
  by_contra hn
  unfold LocallyEquigenerated at hn
  obtain ⟨U,hU⟩ := not_forall.mp hn
  let bad : Finset (Finset V) := Finset.univ.filter
    (fun W => ¬∃ e, Equigenerated (localize B W) e)
  have hb : bad.Nonempty := ⟨U,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hU⟩⟩
  obtain ⟨W,hW,hmax⟩ := bad.exists_maximal hb
  have hbad := (Finset.mem_filter.mp hW).2
  have hs : ∀ T, W ⊂ T → ∃ e, Equigenerated (localize B T) e := by
    intro T hWT
    by_contra hT
    have hTW := hmax (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hT⟩) hWT.subset
    exact hWT.not_superset hTW
  obtain ⟨hc,hp,hcost⟩ := maximal_nonequigenerated_rank_cost hB hd W hbad hs
  exact hbad (htest W hc (by omega))

end Characterizations
