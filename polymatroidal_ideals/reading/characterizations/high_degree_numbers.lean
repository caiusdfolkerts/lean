import Characterizations.SmallTestNumbers

/-! # The exact test number once the degree reaches n-2 -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coversPatterns_top_iff (F : Set (VariableOrder V)) :
    CoversPatterns (Fintype.card V-3) F ↔ CoversFinalTriples F := by
  constructor
  · intro hF i q j hiq hij hqj
    have hc : (tripleCap i q j).card = Fintype.card V-3 := by
      rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
      simp [hiq,hij,hqj]
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj (tripleCap i q j) le_rfl hc
    exact ⟨o,ho,hp.1,hp.2.1,fun x hxi hxq hxj => hp.2.2 x
      ((mem_tripleCap _ _ _ _).mpr ⟨hxi,hxq,hxj⟩)⟩
  · intro hF i q j hiq hij hqj C hC hc
    obtain ⟨o,ho,hp⟩ := hF i q j hiq hij hqj
    refine ⟨o,ho,hp.1,hp.2.1,?_⟩
    intro x hx
    obtain ⟨hxi,hxq,hxj⟩ := (mem_tripleCap _ _ _ _).mp (hC hx)
    exact hp.2.2 x hxi hxq hxj

theorem exact_high_degree_test_number {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : 4 ≤ Fintype.card V) (d : ℕ) (hd : Fintype.card V-2 ≤ d) :
    (∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card = Fintype.card V * (Fintype.card V-1).choose 2) ∧
    (∀ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) →
      Fintype.card V * (Fintype.card V-1).choose 2 ≤ F.card) := by
  constructor
  · obtain ⟨F,hF,hc⟩ := (exact_universal_test_number (k := k) (V := V) hcard).1
    exact ⟨F,fun B hB hL => hF B d hB hL,hc⟩
  · intro F hF
    have hp := ((degreeOrderTests_iff_coverage d (by omega) hcard _).mp hF).1
    have he : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
    rw [he] at hp
    exact triple_coverage_card_lower_bound F ((coversPatterns_top_iff _).mp hp)

end Characterizations
