import bier.isolated
import bier.construction_data

/-! # Dimensions and actual vertex counts after making the ghost an isolated vertex -/

noncomputable section

namespace Bier

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isolatedExtension_maxFaceCard (K : Complex V) :
    K.isolatedExtension.maxFaceCard = max K.maxFaceCard 1 := by
  apply Nat.le_antisymm
  · apply K.isolatedExtension.maxFaceCard_le
    intro s hs
    rcases hs with hs | rfl
    · have h := K.ghost.card_le_maxFaceCard hs
      rw [ghost_maxFaceCard] at h
      exact h.trans (le_max_left _ _)
    · simpa using (le_max_right K.maxFaceCard 1)
  · apply max_le
    · apply K.maxFaceCard_le
      intro s hs
      have h := K.isolatedExtension.card_le_maxFaceCard
        (Or.inl ((ghost_map_some K s).mpr hs))
      simpa using h
    · have h := K.isolatedExtension.card_le_maxFaceCard (s := {none}) (Or.inr rfl)
      simpa using h

theorem isolated_bier_dimension (K : Complex V) (hK : K.Proper)
    (hv : ∀ v, K.face {v}) (hc : 2 ≤ Fintype.card V) :
    (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).dimension =
      (Fintype.card V : ℤ) - 1 := by
  have hex : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hex
  have hnot : ¬ ghostTopFace (∅ : Finset V) ⊆ ghostTopFace {v} := by
    intro h
    have hh := (top_empty_subset_iff _).mp h v
    simpa [ghostTopFace] using hh
  have hface := (isolated_bier_stellar K hK (ghostTopFace {v})).mpr
    ⟨hnot, Or.inl (ghostTopFace_face K (hv v))⟩
  have hlo := (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).card_le_maxFaceCard hface
  have hhi := (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).maxFaceCard_le
    (n := Fintype.card V) (by
      intro F hF
      have hh := bier_card_lt K.isolatedExtension (K.isolatedExtension_proper hK) hF
      simpa only [Fintype.card_option, Nat.lt_succ_iff] using hh)
  have heq : (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).maxFaceCard =
      Fintype.card V := Nat.le_antisymm hhi (by simpa using hlo)
  simp [dimension, heq]

theorem isolated_bier_isSphere (K : Complex V) (hK : K.Proper)
    (hc : 1 ≤ Fintype.card V) :
    (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).IsSphere
      (Fintype.card V - 1) := by
  have h := bier_isSphere K.isolatedExtension (K.isolatedExtension_proper hK)
    (by simpa using hc : 2 ≤ Fintype.card (Option V))
  simpa using h

end Complex

def allLabelsInput := principalCore.isolatedExtension

def allLabelsSphere := allLabelsInput.bier
  (principalCore.isolatedExtension_proper principalCore_proper)

theorem allLabelsInput_all_vertices : allLabelsInput.vertices = Finset.univ := by
  apply Complex.isolatedExtension_all_vertices
  intro v
  rw [← Complex.mem_vertices, principalCore_vertices]
  exact Finset.mem_univ _

theorem allLabelsInput_dimension : allLabelsInput.dimension = 9 := by
  have hc : principalCore.maxFaceCard = 10 := by
    have h := principalCore_dimension
    unfold Complex.dimension at h
    omega
  simp [allLabelsInput, Complex.dimension, Complex.isolatedExtension_maxFaceCard, hc]

theorem allLabelsSphere_all_vertices : allLabelsSphere.vertices = Finset.univ := by
  apply Complex.isolated_bier_all_vertices principalCore principalCore_proper
  · intro v
    rw [← Complex.mem_vertices, principalCore_vertices]
    exact Finset.mem_univ _
  · simp [Fintype.card_sum]

theorem allLabelsSphere_vertex_count : allLabelsSphere.vertices.card = 290366 := by
  rw [allLabelsSphere_all_vertices]
  simp [Fintype.card_sum, Fintype.card_option]

theorem allLabelsSphere_dimension : allLabelsSphere.dimension = 145181 := by
  have hv : ∀ v, principalCore.face {v} := by
    intro v
    rw [← Complex.mem_vertices, principalCore_vertices]
    exact Finset.mem_univ _
  simpa [allLabelsSphere, allLabelsInput, Fintype.card_sum] using
    Complex.isolated_bier_dimension principalCore principalCore_proper hv (by simp [Fintype.card_sum])

theorem allLabelsSphere_isSphere : allLabelsSphere.IsSphere 145181 := by
  simpa [allLabelsSphere, allLabelsInput, Fintype.card_sum] using
    Complex.isolated_bier_isSphere principalCore principalCore_proper (by simp [Fintype.card_sum])

end Bier
