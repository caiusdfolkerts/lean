import bier.facets

/-! # Replacing the ghost by an isolated vertex is exactly a facet subdivision -/

noncomputable section

namespace Bier.Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjoin the singleton ghost and no other new nonempty faces. -/
def isolatedExtension (K : Complex V) : Complex (Option V) where
  face s := K.ghost.face s ∨ s = {none}
  empty := Or.inl K.ghost.empty
  downward := by
    intro s t hst ht
    rcases ht with ht | rfl
    · exact Or.inl (K.ghost.downward hst ht)
    · rcases Finset.subset_singleton_iff.mp hst with hs | hs
      · exact Or.inl (hs ▸ K.ghost.empty)
      · exact Or.inr hs

@[simp] theorem isolatedExtension_face (K : Complex V) (s : Finset (Option V)) :
    K.isolatedExtension.face s ↔ K.ghost.face s ∨ s = {none} := Iff.rfl

theorem isolatedExtension_proper (K : Complex V) (hK : K.Proper) :
    K.isolatedExtension.Proper := by
  intro h
  rcases h with h | h
  · exact K.ghost_proper h
  · have he : (Finset.univ : Finset V) = ∅ := by
      ext v
      have hh := congrArg (fun s => some v ∈ s) h
      simp at hh
    exact hK (he ▸ K.empty)

theorem top_empty_subset_iff (F : Finset (Option V ⊕ Option V)) :
    ghostTopFace (∅ : Finset V) ⊆ F ↔ ∀ v, some v ∈ F.toRight := by
  constructor
  · intro h v
    exact Finset.mem_toRight.mpr (h (by simp [ghostTopFace]))
  · intro h z hz
    have hz' : ∃ v : V, z = Sum.inr (some v) := by
      simpa [ghostTopFace, Finset.mem_map, eq_comm] using hz
    obtain ⟨v, rfl⟩ := hz'
    exact Finset.mem_toRight.mp (h v)

theorem complement_eq_none_of_all_some {K : Complex V} {B : Finset (Option V)}
    (hB : ∀ v, some v ∈ B) (hn : ¬ K.ghost.face Bᶜ) : Bᶜ = {none} := by
  have hs : Bᶜ ⊆ {none} := by
    intro x hx
    cases x with
    | none => simp
    | some v => exact False.elim (Finset.mem_compl.mp hx (hB v))
  rcases Finset.subset_singleton_iff.mp hs with he | he
  · exact False.elim (hn (he ▸ K.ghost.empty))
  · exact he

theorem top_empty_subset_of_complement_eq_none
    {F : Finset (Option V ⊕ Option V)} (h : F.toRightᶜ = {none}) :
    ghostTopFace (∅ : Finset V) ⊆ F := by
  rw [top_empty_subset_iff]
  intro v
  by_contra hv
  have hh : some v ∈ F.toRightᶜ := Finset.mem_compl.mpr hv
  rw [h] at hh
  simpa using hh

theorem corner_subset_iff (F : Finset (Option V ⊕ Option V)) :
    F ⊆ insert (Sum.inl none) (ghostTopFace (∅ : Finset V)) ↔
      F.toLeft ⊆ {none} ∧ none ∉ F.toRight := by
  constructor
  · intro h
    constructor
    · intro x hx
      have hh := h (Finset.mem_toLeft.mp hx)
      simpa [ghostTopFace] using hh
    · intro hn
      have hh := h (Finset.mem_toRight.mp hn)
      simpa [ghostTopFace] using hh
  · rintro ⟨hA, hB⟩ x hx
    cases x with
    | inl v =>
      have hv := Finset.mem_singleton.mp (hA (Finset.mem_toLeft.mpr hx))
      simp [hv]
    | inr v =>
      cases v with
      | none => exact False.elim (hB (Finset.mem_toRight.mpr hx))
      | some v => simp [ghostTopFace]

/-- The complete face formula for stellar subdivision at the all-primed facet. -/
theorem isolated_bier_stellar (K : Complex V) (hK : K.Proper)
    (F : Finset (Option V ⊕ Option V)) :
    (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).face F ↔
      ¬ ghostTopFace (∅ : Finset V) ⊆ F ∧
        ((K.ghost.bier K.ghost_proper).face F ∨
          F ⊆ insert (Sum.inl none) (ghostTopFace (∅ : Finset V))) := by
  constructor
  · rintro ⟨hA, hB, hd⟩
    have hbOld : ¬ K.ghost.face F.toRightᶜ := fun h => hB (Or.inl h)
    have hbNew : F.toRightᶜ ≠ {none} := fun h => hB (Or.inr h)
    refine ⟨fun h => hbNew (complement_eq_none_of_all_some
      ((top_empty_subset_iff F).mp h) hbOld), ?_⟩
    rcases hA with hA | hA
    · exact Or.inl ⟨hA, hbOld, hd⟩
    · right
      rw [corner_subset_iff]
      refine ⟨by simp [hA], ?_⟩
      intro hn
      exact Finset.disjoint_left.mp hd (by simp [hA]) hn
  · rintro ⟨hT, hOld | hCorner⟩
    · refine ⟨Or.inl hOld.1, ?_, hOld.2.2⟩
      rintro (h | h)
      · exact hOld.2.1 h
      · exact hT (top_empty_subset_of_complement_eq_none h)
    · obtain ⟨hA, hB⟩ := (corner_subset_iff F).mp hCorner
      refine ⟨?_, ?_, ?_⟩
      · rcases Finset.subset_singleton_iff.mp hA with he | he
        · exact Or.inl (he ▸ K.ghost.empty)
        · exact Or.inr he
      · rintro (h | h)
        · exact h.1 (Finset.mem_compl.mpr hB)
        · exact hT (top_empty_subset_of_complement_eq_none h)
      · rw [Finset.disjoint_left]
        intro x hx hb
        have he := Finset.mem_singleton.mp (hA hx)
        exact hB (he ▸ hb)

theorem isolatedExtension_all_vertices (K : Complex V) (hv : ∀ v, K.face {v}) :
    K.isolatedExtension.vertices = Finset.univ := by
  ext v
  simp only [mem_vertices, Finset.mem_univ, iff_true]
  cases v with
  | none => exact Or.inr rfl
  | some v =>
    left
    have h := (ghost_map_some K {v}).mpr (hv v)
    simpa using h

theorem isolated_bier_all_vertices (K : Complex V) (hK : K.Proper)
    (hv : ∀ v, K.face {v}) (hc : 2 ≤ Fintype.card V) :
    (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).vertices = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  cases v with
  | inl v =>
    rw [bier_inl_vertex, ← mem_vertices, isolatedExtension_all_vertices K hv]
    exact Finset.mem_univ _
  | inr v =>
    rw [bier_inr_vertex]
    rintro (h | h)
    · cases v with
      | none =>
        have he : ({none}ᶜ : Finset (Option V)).eraseNone = Finset.univ := by ext; simp
        exact hK (he ▸ h.2)
      | some v => exact h.1 (by simp)
    · have hh := congrArg Finset.card h
      simp only [Finset.card_compl, Finset.card_singleton, Fintype.card_option] at hh
      omega

theorem isolated_bier_vertex_count (K : Complex V) (hK : K.Proper)
    (hv : ∀ v, K.face {v}) (hc : 2 ≤ Fintype.card V) :
    (K.isolatedExtension.bier (K.isolatedExtension_proper hK)).vertices.card =
      2 * Fintype.card V + 2 := by
  rw [isolated_bier_all_vertices K hK hv hc]
  simp [Fintype.card_sum, Fintype.card_option]
  omega

end Bier.Complex
