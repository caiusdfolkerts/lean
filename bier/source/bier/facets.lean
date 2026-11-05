import bier.encoding

/-! # Bier faces, facet sizes, and the actual vertex set with one ghost -/

noncomputable section

namespace Bier.Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bier_card_lt (K : Complex V) (hK : K.Proper)
    {F : Finset (V ⊕ V)} (hF : (K.bier hK).face F) :
    F.card < Fintype.card V := by
  have hs : F.toLeft ⊆ F.toRightᶜ := by
    intro v hv
    exact Finset.mem_compl.mpr (fun hb => Finset.disjoint_left.mp hF.2.2 hv hb)
  have hn : F.toLeft ≠ F.toRightᶜ := by
    intro h
    exact hF.2.1 (h ▸ hF.1)
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hn⟩)
  rw [Finset.card_compl] at hc
  have he := Finset.card_toLeft_add_card_toRight (u := F)
  omega

theorem ghost_bier_card_le (K : Complex V)
    {F : Finset (Option V ⊕ Option V)}
    (hF : (K.ghost.bier K.ghost_proper).face F) : F.card ≤ Fintype.card V := by
  have h := bier_card_lt K.ghost K.ghost_proper hF
  simpa only [Fintype.card_option, Nat.lt_succ_iff] using h

/-- The simplex with unprimed labels in A and primed labels in its complement. -/
def ghostTopFace (A : Finset V) : Finset (Option V ⊕ Option V) :=
  (A.map Function.Embedding.some).disjSum (Aᶜ.map Function.Embedding.some)

/-- The transition simplex through the primed ghost label. -/
def ghostTransitionFace (B : Finset V) (a : V) : Finset (Option V ⊕ Option V) :=
  (B.map Function.Embedding.some).disjSum
    (insert none ((insert a B)ᶜ.map Function.Embedding.some))

@[simp] theorem ghostTopFace_card (A : Finset V) :
    (ghostTopFace A).card = Fintype.card V := by
  simp only [ghostTopFace, Finset.card_disjSum, Finset.card_map]
  exact Finset.card_add_card_compl A

@[simp] theorem ghostTransitionFace_card (B : Finset V) (a : V) (ha : a ∉ B) :
    (ghostTransitionFace B a).card = Fintype.card V := by
  simp only [ghostTransitionFace, Finset.card_disjSum]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, Finset.card_map,
    Finset.card_compl, Finset.card_insert_of_notMem ha]
  have h := Finset.card_le_univ (insert a B)
  rw [Finset.card_insert_of_notMem ha] at h
  omega

theorem ghostTopFace_face (K : Complex V) {A : Finset V} (hA : K.face A) :
    (K.ghost.bier K.ghost_proper).face (ghostTopFace A) := by
  simp only [bier_face_iff, ghostTopFace, Finset.toLeft_disjSum, Finset.toRight_disjSum]
  refine ⟨(ghost_map_some K A).mpr hA, ?_, ?_⟩
  · intro h
    exact h.1 (by simp)
  · rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    have hb : a ∈ Aᶜ := by simpa using hw
    exact Finset.mem_compl.mp hb ha

theorem ghostTransitionFace_face (K : Complex V) {B : Finset V} {a : V}
    (hB : K.face B) (hBa : ¬ K.face (insert a B)) :
    (K.ghost.bier K.ghost_proper).face (ghostTransitionFace B a) := by
  simp only [bier_face_iff, ghostTransitionFace,
    Finset.toLeft_disjSum, Finset.toRight_disjSum]
  refine ⟨(ghost_map_some K B).mpr hB, ?_, ?_⟩
  · intro h
    apply hBa
    have he : (insert none ((insert a B)ᶜ.map Function.Embedding.some))ᶜ.eraseNone =
        insert a B := by
      ext v
      simp
    exact he ▸ h.2
  · rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
    have hh : b ∉ insert a B := by simpa using hw
    exact hh (Finset.mem_insert_of_mem hb)

@[simp] theorem bier_inl_vertex (K : Complex V) (hK : K.Proper) (v : V) :
    Sum.inl v ∈ (K.bier hK).vertices ↔ K.face {v} := by
  have hl : ({Sum.inl v} : Finset (V ⊕ V)).toLeft = {v} := by ext; simp
  have hr : ({Sum.inl v} : Finset (V ⊕ V)).toRight = ∅ := by ext; simp
  simp only [mem_vertices, bier_face_iff, hl, hr, Finset.compl_empty,
    Finset.disjoint_empty_right, and_true]
  exact and_iff_left hK

@[simp] theorem bier_inr_vertex (K : Complex V) (hK : K.Proper) (v : V) :
    Sum.inr v ∈ (K.bier hK).vertices ↔ ¬ K.face {v}ᶜ := by
  have hl : ({Sum.inr v} : Finset (V ⊕ V)).toLeft = ∅ := by ext; simp
  have hr : ({Sum.inr v} : Finset (V ⊕ V)).toRight = {v} := by ext; simp
  simp [bier, hl, hr, K.empty]

theorem ghost_bier_x_vertex (K : Complex V) {v : V} (hv : K.face {v}) :
    Sum.inl (some v) ∈ (K.ghost.bier K.ghost_proper).vertices := by
  rw [bier_inl_vertex]
  have h := (ghost_map_some K {v}).mpr hv
  simpa using h

theorem ghost_bier_p_vertex (K : Complex V) (v : V) :
    Sum.inr (some v) ∈ (K.ghost.bier K.ghost_proper).vertices := by
  rw [bier_inr_vertex]
  intro h
  exact h.1 (by simp)

theorem ghost_bier_z_vertex (K : Complex V) (hK : K.Proper) :
    Sum.inr none ∈ (K.ghost.bier K.ghost_proper).vertices := by
  rw [bier_inr_vertex]
  intro h
  apply hK
  have he : ({none}ᶜ : Finset (Option V)).eraseNone = Finset.univ := by ext; simp
  exact he ▸ h.2

theorem ghost_bier_vertices (K : Complex V) (hK : K.Proper)
    (hv : ∀ v, K.face {v}) :
    (K.ghost.bier K.ghost_proper).vertices = Finset.univ.erase (Sum.inl none) := by
  ext v
  cases v with
  | inl v =>
    cases v with
    | none => simp [ghost]
    | some v => simp [ghost_bier_x_vertex K (hv v)]
  | inr v =>
    cases v with
    | none => simp [ghost_bier_z_vertex K hK]
    | some v => simp [ghost_bier_p_vertex K v]

theorem ghost_bier_vertex_count (K : Complex V) (hK : K.Proper)
    (hv : ∀ v, K.face {v}) :
    (K.ghost.bier K.ghost_proper).vertices.card = 2 * Fintype.card V + 1 := by
  rw [ghost_bier_vertices K hK hv, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_sum, Fintype.card_option]
  omega

theorem ghost_bier_dimension (K : Complex V) :
    (K.ghost.bier K.ghost_proper).dimension = (Fintype.card V : ℤ) - 1 := by
  have hlo := (K.ghost.bier K.ghost_proper).card_le_maxFaceCard
    (ghostTopFace_face K K.empty)
  have hhi := (K.ghost.bier K.ghost_proper).maxFaceCard_le
    (fun _ h => ghost_bier_card_le K h)
  have heq : (K.ghost.bier K.ghost_proper).maxFaceCard = Fintype.card V := by
    exact Nat.le_antisymm hhi (by simpa using hlo)
  simp [dimension, heq]

end Bier.Complex
