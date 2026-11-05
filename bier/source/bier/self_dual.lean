import bier.encoding
import bier.link
import bier.sphere

/-! The exact self-dual suspension and its combinatorial antipodal symmetry. -/

noncomputable section

namespace Bier.Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem toLeft_singleton_inl {A B : Type*} [DecidableEq A] [DecidableEq B] (a : A) :
    ({Sum.inl a} : Finset (A ⊕ B)).toLeft = {a} := by ext; simp

@[simp] theorem toLeft_singleton_inr {A B : Type*} [DecidableEq A] [DecidableEq B] (b : B) :
    ({Sum.inr b} : Finset (A ⊕ B)).toLeft = ∅ := by ext; simp

@[simp] theorem toRight_singleton_inl {A B : Type*} [DecidableEq A] [DecidableEq B] (a : A) :
    ({Sum.inl a} : Finset (A ⊕ B)).toRight = ∅ := by ext; simp

@[simp] theorem toRight_singleton_inr {A B : Type*} [DecidableEq A] [DecidableEq B] (b : B) :
    ({Sum.inr b} : Finset (A ⊕ B)).toRight = {b} := by ext; simp

@[simp] theorem toLeft_compl (s : Finset (V ⊕ Bool)) : sᶜ.toLeft = s.toLeftᶜ := by
  ext v
  simp

def selfDualSuspension (K : Bier.Complex V) : Bier.Complex (V ⊕ Bool) where
  face s := ¬ (Sum.inr false ∈ s ∧ Sum.inr true ∈ s) ∧
    (Sum.inr false ∈ s → K.face s.toLeft) ∧
    (Sum.inr true ∈ s → ¬ K.face s.toLeftᶜ)
  empty := by simp
  downward := by
    intro s t hst ht
    refine ⟨fun hs => ht.1 ⟨hst hs.1, hst hs.2⟩, ?_, ?_⟩
    · intro ha
      exact K.downward (Finset.toLeft_subset_toLeft hst) (ht.2.1 (hst ha))
    · intro hb hs
      exact ht.2.2 (hst hb)
        (K.downward (Finset.compl_subset_compl.mpr (Finset.toLeft_subset_toLeft hst)) hs)

theorem selfDualSuspension_proper (K : Bier.Complex V) : K.selfDualSuspension.Proper := by
  intro h
  exact h.1 ⟨Finset.mem_univ _, Finset.mem_univ _⟩

theorem selfDualSuspension_dual (K : Bier.Complex V) (s : Finset (V ⊕ Bool)) :
    (K.selfDualSuspension.dual K.selfDualSuspension_proper).face s ↔
      K.selfDualSuspension.face s := by
  classical
  by_cases ha : Sum.inr false ∈ s <;> by_cases hb : Sum.inr true ∈ s <;>
    simp [dual, selfDualSuspension, ha, hb]

theorem selfDualSuspension_all_vertices (K : Bier.Complex V) (hK : K.Proper)
    (v : V ⊕ Bool) : K.selfDualSuspension.face {v} := by
  cases v with
  | inl v => simp [selfDualSuspension]
  | inr b =>
    cases b
    · simpa [selfDualSuspension] using K.empty
    · simpa [selfDualSuspension, Proper] using hK

theorem selfDualSuspension_bier_all_vertices (K : Bier.Complex V) (hK : K.Proper)
    (v : (V ⊕ Bool) ⊕ (V ⊕ Bool)) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).face {v} := by
  have hall := K.selfDualSuspension_all_vertices hK
  cases v with
  | inl v =>
    rw [bier_face_iff, toLeft_singleton_inl, toRight_singleton_inl, Finset.compl_empty]
    exact ⟨hall v, K.selfDualSuspension_proper, by simp⟩
  | inr v =>
    have hd : ¬ K.selfDualSuspension.face ({v} : Finset (V ⊕ Bool))ᶜ :=
      (K.selfDualSuspension_dual {v}).mpr (hall v)
    rw [bier_face_iff, toLeft_singleton_inr, toRight_singleton_inr]
    exact ⟨K.selfDualSuspension.empty, hd, by simp⟩

theorem selfDualSuspension_bier_vertices_card (K : Bier.Complex V) (hK : K.Proper) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).vertices.card =
      2 * Fintype.card V + 4 := by
  have heq : (K.selfDualSuspension.bier K.selfDualSuspension_proper).vertices = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact (mem_vertices _ _).mpr (K.selfDualSuspension_bier_all_vertices hK v)
  rw [heq]
  simp [Fintype.card_sum]
  omega

theorem selfDualSuspension_bier_isSphere (K : Bier.Complex V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).IsSphere (Fintype.card V) := by
  have h := K.selfDualSuspension.bier_isSphere K.selfDualSuspension_proper (by simp)
  simpa using h

theorem bier_swap_face (K : Bier.Complex V) (hK : K.Proper)
    (hself : ∀ s, (K.dual hK).face s ↔ K.face s) (s : Finset (V ⊕ V)) :
    (K.bier hK).face (s.image Sum.swap) ↔ (K.bier hK).face s := by
  classical
  have hl : (s.image Sum.swap).toLeft = s.toRight := by
    ext v
    simp
  have hr : (s.image Sum.swap).toRight = s.toLeft := by
    ext v
    simp
  simp only [bier_face_iff, hl, hr]
  have hdleft := hself s.toLeft
  have hdright := hself s.toRight
  change (¬ K.face s.toLeftᶜ ↔ K.face s.toLeft) at hdleft
  change (¬ K.face s.toRightᶜ ↔ K.face s.toRight) at hdright
  rw [hdleft, hdright, disjoint_comm]
  tauto

theorem bier_swap_disjoint (K : Bier.Complex V) (hK : K.Proper)
    (s : Finset (V ⊕ V)) (hs : (K.bier hK).face s) :
    Disjoint s (s.image Sum.swap) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hswap
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hswap
  subst v
  cases w with
  | inl w =>
    exact Finset.disjoint_left.mp hs.2.2
      (by simpa using hw) (by simpa using hv)
  | inr w =>
    exact Finset.disjoint_left.mp hs.2.2
      (by simpa using hv) (by simpa using hw)

end Bier.Complex
