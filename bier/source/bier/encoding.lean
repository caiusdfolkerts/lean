import bier.complex
import bier.sign_rank
import Mathlib.Data.Finset.Option

/-! # Encoding strict signs by faces and adjoining a ghost label -/

noncomputable section

namespace Bier

namespace Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend the ground set by one label which belongs to no face. -/
def ghost (K : Complex V) : Complex (Option V) where
  face s := none ∉ s ∧ K.face s.eraseNone
  empty := by simpa using K.empty
  downward := fun hst ht =>
    ⟨fun hs => ht.1 (hst hs), K.downward (Finset.eraseNone.monotone hst) ht.2⟩

@[simp] theorem ghost_face (K : Complex V) (s : Finset (Option V)) :
    K.ghost.face s ↔ none ∉ s ∧ K.face s.eraseNone := Iff.rfl

theorem ghost_proper (K : Complex V) : K.ghost.Proper := by
  intro h
  exact h.1 (Finset.mem_univ _)

@[simp] theorem ghost_map_some (K : Complex V) (s : Finset V) :
    K.ghost.face (s.map Function.Embedding.some) ↔ K.face s := by
  simp [ghost]

@[simp] theorem ghost_none_not_vertex (K : Complex V) : none ∉ K.ghost.vertices := by
  simp [ghost]

@[simp] theorem ghost_some_vertex (K : Complex V) (v : V) :
    some v ∈ K.ghost.vertices ↔ v ∈ K.vertices := by
  have he : ({some v} : Finset (Option V)).eraseNone = {v} := by ext; simp
  simp [ghost, he]

end Complex

variable {U R C : Type*} [Fintype U] [Fintype R] [Fintype C]
  [DecidableEq U] [DecidableEq R] [DecidableEq C]

/-- A core skeleton, an anchor skeleton, and exactly the selected positive faces. -/
def signComplex (k : ℕ) (S : R → Finset U) (hS : ∀ r, (S r).card = k)
    (H : Matrix R C ℝ) : Complex (U ⊕ C) where
  face F := F.toLeft.card ≤ k ∧
    (F.toRight = ∅ ∨ ∃ t, F.toRight = {t} ∧
      (F.toLeft.card < k ∨ ∃ r, F.toLeft = S r ∧ H r t = 1))
  empty := by simp [Finset.toLeft, Finset.toRight]
  downward := by
    intro A B hAB hB
    have hL := Finset.toLeft_subset_toLeft hAB
    have hR := Finset.toRight_subset_toRight hAB
    refine ⟨(Finset.card_le_card hL).trans hB.1, ?_⟩
    rcases hB.2 with hb | ⟨t, ht, hk | ⟨r, hr, hrt⟩⟩
    · exact Or.inl (Finset.subset_empty.mp (hb ▸ hR))
    · rcases Finset.subset_singleton_iff.mp (ht ▸ hR) with ha | ha
      · exact Or.inl ha
      · exact Or.inr ⟨t, ha, Or.inl ((Finset.card_le_card hL).trans_lt hk)⟩
    · rcases Finset.subset_singleton_iff.mp (ht ▸ hR) with ha | ha
      · exact Or.inl ha
      · refine Or.inr ⟨t, ha, ?_⟩
        by_cases he : A.toLeft = B.toLeft
        · exact Or.inr ⟨r, he.trans hr, hrt⟩
        · left
          have hc : A.toLeft.card < B.toLeft.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hL, he⟩)
          simpa [hr, hS r] using hc

@[simp] theorem signComplex_face (k : ℕ) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ) (F : Finset (U ⊕ C)) :
    (signComplex k S hS H).face F ↔ F.toLeft.card ≤ k ∧
      (F.toRight = ∅ ∨ ∃ t, F.toRight = {t} ∧
        (F.toLeft.card < k ∨ ∃ r, F.toLeft = S r ∧ H r t = 1)) := Iff.rfl

theorem signComplex_core (k : ℕ) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ)
    (A : Finset U) (hA : A.card ≤ k) :
    (signComplex k S hS H).face (A.disjSum ∅) := by
  simp only [signComplex_face, Finset.toLeft_disjSum, Finset.toRight_disjSum]
  exact ⟨hA, Or.inl trivial⟩

theorem signComplex_selected (k : ℕ) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (hinj : Function.Injective S)
    (H : Matrix R C ℝ) (r : R) (t : C) :
    (signComplex k S hS H).face ((S r).disjSum {t}) ↔ H r t = 1 := by
  simp only [signComplex_face, Finset.toLeft_disjSum, Finset.toRight_disjSum,
    hS, le_refl, Finset.singleton_ne_empty, false_or, lt_self_iff_false,
    and_true, true_and]
  constructor
  · rintro ⟨t', ht, r', hr, hpos⟩
    have htt := Finset.singleton_injective ht
    have hrr := hinj hr
    simpa [← htt, ← hrr] using hpos
  · intro hp
    exact ⟨t, rfl, r, rfl, hp⟩

theorem signComplex_all_vertices (k : ℕ) (hk : 1 ≤ k) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ) :
    (signComplex k S hS H).vertices = Finset.univ := by
  ext v
  simp only [Complex.mem_vertices, Finset.mem_univ, iff_true]
  cases v with
  | inl u =>
    have h := signComplex_core k S hS H {u} (by simpa using hk)
    simpa [Finset.disjSum_empty, Finset.map_singleton] using h
  | inr t =>
    have h : (signComplex k S hS H).face ((∅ : Finset U).disjSum {t}) := by
      simp only [signComplex_face, Finset.toLeft_disjSum, Finset.toRight_disjSum,
        Finset.card_empty]
      exact ⟨Nat.zero_le _, Or.inr ⟨t, rfl, Or.inl (by omega)⟩⟩
    simpa [Finset.empty_disjSum, Finset.map_singleton] using h

theorem signComplex_proper (k : ℕ) (hk : k < Fintype.card U)
    (S : R → Finset U) (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ) :
    (signComplex k S hS H).Proper := by
  intro h
  have hU : (Finset.univ : Finset (U ⊕ C)).toLeft = Finset.univ := by ext; simp
  have hc := h.1
  rw [hU, Finset.card_univ] at hc
  exact (not_le_of_gt hk) hc

theorem signComplex_card_face_le (k : ℕ) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ)
    {F : Finset (U ⊕ C)} (hF : (signComplex k S hS H).face F) : F.card ≤ k + 1 := by
  have hr : F.toRight.card ≤ 1 := by
    rcases hF.2 with h | ⟨t, h, _⟩ <;> simp [h]
  rw [← Finset.card_toLeft_add_card_toRight]
  exact Nat.add_le_add hF.1 hr

theorem signComplex_dimension (k : ℕ) (S : R → Finset U)
    (hS : ∀ r, (S r).card = k) (H : Matrix R C ℝ)
    (hp : ∃ r t, H r t = 1) : (signComplex k S hS H).dimension = k := by
  obtain ⟨r, t, hrt⟩ := hp
  have hface : (signComplex k S hS H).face ((S r).disjSum {t}) := by
    simp only [signComplex_face, Finset.toLeft_disjSum, Finset.toRight_disjSum, hS]
    exact ⟨le_rfl, Or.inr ⟨t, rfl, Or.inr ⟨r, rfl, hrt⟩⟩⟩
  have hlo := (signComplex k S hS H).card_le_maxFaceCard hface
  have hhi := (signComplex k S hS H).maxFaceCard_le
    (fun _ h => signComplex_card_face_le k S hS H h)
  have heq : (signComplex k S hS H).maxFaceCard = k + 1 := by
    apply Nat.le_antisymm hhi
    simpa [hS] using hlo
  simp [Complex.dimension, heq]

end Bier
