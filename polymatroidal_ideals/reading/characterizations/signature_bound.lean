import Characterizations.OptimalOrders
import Mathlib.Combinatorics.SetFamily.LYM

/-! # The sharp Boolean-antichain constraint on any degree-sensitive test family -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem relative_triples_of_patterns {s : ℕ} {F : Set (VariableOrder V)}
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s F) (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ o ∈ F, o x < o y ∧ o y < o z := by
  have hthree : ({x,y,z} : Finset V).card = 3 := by simp [hxy,hxz,hyz]
  obtain ⟨q, _, hq⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x,y,z} : Finset V).card < (univ : Finset V).card by simp; omega)
  have hqx : q ≠ x := fun h => hq (by simp [h])
  have hqy : q ≠ y := fun h => hq (by simp [h])
  have hqz : q ≠ z := fun h => hq (by simp [h])
  have hxcap : x ∈ tripleCap y q z := (mem_tripleCap _ _ _ _).mpr ⟨hxy,hqx.symm,hxz⟩
  have hcapcard : (tripleCap y q z).card = Fintype.card V - 3 := by
    rw [tripleCap, card_sdiff_of_subset (subset_univ _)]
    simp [hqy.symm, hyz, hqz]
  obtain ⟨C,hxC,hCcap,hCc⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hxcap)
    (show ({x} : Finset V).card ≤ s by simpa using hs)
    (show s ≤ (tripleCap y q z).card by omega)
  obtain ⟨o,ho,hp⟩ := hF y q z hqy.symm hyz hqz C hCcap hCc
  exact ⟨o,ho,(hp.2.2 x (hxC (by simp))).1,hp.1⟩

/-- Corollary 5.5, inequality (5.3), for every finite family satisfying the
full degree-sensitive test criterion. -/
theorem pattern_signature_bound {s : ℕ} (F : Finset (VariableOrder V))
    (hcard : 4 ≤ Fintype.card V) (hs : 1 ≤ s) (hsn : s ≤ Fintype.card V - 3)
    (hF : CoversPatterns s (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  obtain ⟨x,y,hxy⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let signature (x : Except y) : Finset F := univ.filter (fun o => o.val x.val < o.val y)
  have hnot (x z : Except y) (hxz : x ≠ z) : ¬ signature x ⊆ signature z := by
    intro hsub
    obtain ⟨o,ho,hxyO,hyzO⟩ := relative_triples_of_patterns hcard hs hsn hF x.val y z.val
      x.property (fun he => hxz (Subtype.ext he)) z.property.symm
    have hxmem : (⟨o,ho⟩ : F) ∈ signature x := by simp [signature,hxyO]
    have hzmem := hsub hxmem
    have hzyO : o z.val < o y := by simpa [signature] using hzmem
    exact (lt_irrefl _ (hyzO.trans hzyO))
  have hinj : Function.Injective signature := by
    intro x z he
    by_contra hn
    exact hnot x z hn (by rw [he])
  let A : Finset (Finset F) := univ.image signature
  have hA : IsAntichain (· ⊆ ·) (A : Set (Finset F)) := by
    intro a ha b hb hab hsub
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    have hxz : x ≠ z := fun he => hab (congrArg signature he)
    exact hnot x z hxz hsub
  have hAc : A.card = Fintype.card V - 1 := by
    dsimp only [A]
    rw [card_image_of_injective _ hinj, card_univ, card_except]
  have hh := hA.sperner
  simpa [hAc] using hh

theorem degree_test_signature_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    Fintype.card V - 1 ≤ F.card.choose (F.card / 2) := by
  exact pattern_signature_bound F hcard (by omega) (Nat.min_le_right _ _)
    ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1

end Characterizations
