import bier.isolated

/-! # Complete combinatorial data for subdividing a facet at a new vertex -/

noncomputable section

namespace Bier

variable {V : Type*} [Fintype V] [DecidableEq V]

structure StellarFacetData (K L : Complex V) (T : Finset V) (v : V) : Prop where
  ghost : v ∉ K.vertices
  oldFace : K.face T
  oldCard : ∀ F, K.face F → F.card ≤ T.card
  card_two : 2 ≤ T.card
  faces : ∀ F, L.face F ↔ ¬ T ⊆ F ∧ (K.face F ∨ F ⊆ insert v T)

namespace StellarFacetData

variable {K L : Complex V} {T : Finset V} {v : V} (h : StellarFacetData K L T v)

include h

theorem not_mem_old_face {F : Finset V} (hF : K.face F) : v ∉ F := by
  intro hv
  apply h.ghost
  rw [Complex.mem_vertices]
  exact K.downward (Finset.singleton_subset_iff.mpr hv) hF

theorem not_mem_facet : v ∉ T := h.not_mem_old_face h.oldFace

theorem old_iff (F : Finset V) :
    K.face F ↔ F = T ∨ (L.face F ∧ v ∉ F) := by
  constructor
  · intro hF
    by_cases ht : T ⊆ F
    · exact Or.inl (Finset.eq_of_subset_of_card_le ht (h.oldCard F hF)).symm
    · exact Or.inr ⟨(h.faces F).mpr ⟨ht, Or.inl hF⟩, h.not_mem_old_face hF⟩
  · rintro (rfl | ⟨hF, hv⟩)
    · exact h.oldFace
    · rcases ((h.faces F).mp hF).2 with ho | hc
      · exact ho
      · apply K.downward (t := T) ?_ h.oldFace
        intro x hx
        rcases Finset.mem_insert.mp (hc hx) with he | ht
        · exact False.elim (hv (he ▸ hx))
        · exact ht

theorem corner_face {i : V} (hi : i ∈ T) : L.face (insert v (T.erase i)) := by
  apply (h.faces _).mpr
  refine ⟨?_, Or.inr (Finset.insert_subset_insert _ (Finset.erase_subset _ _))⟩
  intro ht
  have hiv : i ≠ v := by intro he; exact h.not_mem_facet (he ▸ hi)
  have hh := ht hi
  simpa [hiv] using hh

theorem corner_card {i : V} (hi : i ∈ T) : (insert v (T.erase i)).card = T.card := by
  rw [Finset.card_insert_of_notMem (fun hv => h.not_mem_facet (Finset.mem_of_mem_erase hv)),
    Finset.card_erase_of_mem hi]
  have hp := Finset.card_pos.mpr ⟨i, hi⟩
  omega

theorem face_card_le {F : Finset V} (hF : L.face F) : F.card ≤ T.card := by
  obtain ⟨ht, ho | hc⟩ := (h.faces F).mp hF
  · exact h.oldCard F ho
  · have hn : F ≠ insert v T := by
      intro he
      exact ht (he ▸ Finset.subset_insert _ _)
    have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hc, hn⟩)
    rw [Finset.card_insert_of_notMem h.not_mem_facet] at hh
    omega

theorem vertices : L.vertices = insert v K.vertices := by
  ext w
  simp only [Complex.mem_vertices, Finset.mem_insert]
  constructor
  · intro hw
    by_cases he : w = v
    · exact Or.inl he
    · right
      exact (h.old_iff {w}).mpr (Or.inr ⟨hw, by simpa [eq_comm] using he⟩)
  · rintro (he | hw)
    · subst w
      apply (h.faces {v}).mpr
      refine ⟨?_, Or.inr (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))⟩
      intro ht
      have hh := Finset.card_le_card ht
      simp only [Finset.card_singleton] at hh
      have hc := h.card_two
      omega
    · apply (h.faces {w}).mpr
      refine ⟨?_, Or.inl hw⟩
      intro ht
      have hh := Finset.card_le_card ht
      simp only [Finset.card_singleton] at hh
      have hc := h.card_two
      omega

theorem old_vertex_mem {w : V} (hw : w ∈ K.vertices) : w ∈ L.vertices := by
  rw [h.vertices]
  exact Finset.mem_insert_of_mem hw

theorem new_vertex_mem : v ∈ L.vertices := by rw [h.vertices]; simp

theorem vertices_card : L.vertices.card = K.vertices.card + 1 := by
  rw [h.vertices, Finset.card_insert_of_notMem h.ghost]

end StellarFacetData

namespace Complex

theorem isolated_stellarData (K : Complex V) (hK : K.Proper) (hc : 2 ≤ Fintype.card V) :
    StellarFacetData (K.ghost.bier K.ghost_proper)
      (K.isolatedExtension.bier (K.isolatedExtension_proper hK))
      (ghostTopFace (∅ : Finset V)) (Sum.inl none) where
  ghost := by simp [ghost]
  oldFace := ghostTopFace_face K K.empty
  oldCard := fun F hF => by simpa using ghost_bier_card_le K hF
  card_two := by simpa using hc
  faces := isolated_bier_stellar K hK

end Complex
end Bier
