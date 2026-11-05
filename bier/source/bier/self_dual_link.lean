import bier.self_dual

/-! The old ghost Bier sphere occurs as the exact vertex link of the self-dual one. -/

noncomputable section

namespace Bier.Complex

variable {V : Type*} [Fintype V] [DecidableEq V]

def suspensionLabel : Option V → V ⊕ Bool
  | none => .inr true
  | some v => .inl v

theorem suspensionLabel_injective : Function.Injective (suspensionLabel : Option V → V ⊕ Bool) := by
  intro x y h
  cases x <;> cases y <;> simp_all [suspensionLabel]

@[simp] theorem suspensionLabel_ne_a (x : Option V) :
    suspensionLabel x ≠ (Sum.inr false : V ⊕ Bool) := by cases x <;> simp [suspensionLabel]

@[simp] theorem suspensionLabel_eq_b (x : Option V) :
    suspensionLabel x = (Sum.inr true : V ⊕ Bool) ↔ x = none := by cases x <;> simp [suspensionLabel]

@[simp] theorem a_notMem_image_suspensionLabel (s : Finset (Option V)) :
    Sum.inr false ∉ s.image suspensionLabel := by
  intro h
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
  exact suspensionLabel_ne_a x heq

@[simp] theorem b_mem_image_suspensionLabel (s : Finset (Option V)) :
    Sum.inr true ∈ s.image suspensionLabel ↔ none ∈ s := by simp

@[simp] theorem toLeft_image_suspensionLabel (s : Finset (Option V)) :
    (s.image suspensionLabel).toLeft = s.eraseNone := by
  ext v
  simp only [Finset.mem_toLeft, Finset.mem_image, Finset.mem_eraseNone]
  constructor
  · rintro ⟨x, hx, heq⟩
    cases x with
    | none => simp [suspensionLabel] at heq
    | some w =>
      have hwv : w = v := Sum.inl.inj heq
      exact hwv ▸ hx
  · intro hv
    exact ⟨some v, hv, rfl⟩

@[simp] theorem toLeft_insert_inr {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset (A ⊕ B)) (b : B) : (insert (.inr b) s).toLeft = s.toLeft := by ext; simp

@[simp] theorem toLeft_insert_inl {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset (A ⊕ B)) (a : A) : (insert (.inl a) s).toLeft = insert a s.toLeft := by ext; simp

@[simp] theorem toRight_insert_inl {A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset (A ⊕ B)) (a : A) : (insert (.inl a) s).toRight = s.toRight := by ext; simp

@[simp] theorem eraseNone_compl (s : Finset (Option V)) :
    sᶜ.eraseNone = s.eraseNoneᶜ := by ext; simp

theorem suspension_image_face (K : Bier.Complex V) (s : Finset (Option V)) :
    K.selfDualSuspension.face (s.image suspensionLabel) ↔
      (none ∈ s → ¬ K.face s.eraseNoneᶜ) := by
  simp [selfDualSuspension]

theorem suspension_insert_a_image_face (K : Bier.Complex V) (s : Finset (Option V)) :
    K.selfDualSuspension.face (insert (.inr false) (s.image suspensionLabel)) ↔ K.ghost.face s := by
  simp only [selfDualSuspension, Finset.mem_insert, true_or, true_and, Sum.inr.injEq,
    Bool.true_eq_false, false_or, b_mem_image_suspensionLabel,
    toLeft_insert_inr, toLeft_image_suspensionLabel, ghost_face]
  tauto

theorem ghost_dual_face (K : Bier.Complex V) (s : Finset (Option V)) :
    (K.ghost.dual K.ghost_proper).face s ↔ (none ∈ s → ¬ K.face s.eraseNoneᶜ) := by
  simp [dual, ghost]

def suspensionBierLabel : (Option V ⊕ Option V) → (V ⊕ Bool) ⊕ (V ⊕ Bool) :=
  Sum.map suspensionLabel suspensionLabel

theorem suspensionBierLabel_injective : Function.Injective (suspensionBierLabel (V := V)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [suspensionBierLabel, suspensionLabel_injective.eq_iff]

@[simp] theorem toLeft_image_suspensionBierLabel (s : Finset (Option V ⊕ Option V)) :
    (s.image suspensionBierLabel).toLeft = s.toLeft.image suspensionLabel := by
  ext v
  simp only [Finset.mem_toLeft, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    cases x with
    | inl x => exact ⟨x, hx, Sum.inl.inj heq⟩
    | inr x => simp [suspensionBierLabel] at heq
  · rintro ⟨x, hx, rfl⟩
    exact ⟨.inl x, hx, rfl⟩

@[simp] theorem toRight_image_suspensionBierLabel (s : Finset (Option V ⊕ Option V)) :
    (s.image suspensionBierLabel).toRight = s.toRight.image suspensionLabel := by
  ext v
  simp only [Finset.mem_toRight, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    cases x with
    | inr x => exact ⟨x, hx, Sum.inr.inj heq⟩
    | inl x => simp [suspensionBierLabel] at heq
  · rintro ⟨x, hx, rfl⟩
    exact ⟨.inr x, hx, rfl⟩

theorem bier_selfdual_face_iff (K : Bier.Complex V) (hK : K.Proper)
    (hself : ∀ s, (K.dual hK).face s ↔ K.face s) (s : Finset (V ⊕ V)) :
    (K.bier hK).face s ↔ K.face s.toLeft ∧ K.face s.toRight ∧ Disjoint s.toLeft s.toRight := by
  rw [bier_face_iff]
  exact and_congr_right fun _ => and_congr_left fun _ => hself _

theorem selfDualSuspension_a_vertex (K : Bier.Complex V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).face {Sum.inl (Sum.inr false)} := by
  rw [bier_face_iff, toLeft_singleton_inl, toRight_singleton_inl, Finset.compl_empty]
  refine ⟨?_, K.selfDualSuspension_proper, by simp⟩
  simpa [selfDualSuspension] using K.empty

theorem suspension_link_image_face (K : Bier.Complex V) (s : Finset (Option V ⊕ Option V)) :
    ((K.selfDualSuspension.bier K.selfDualSuspension_proper).link
      (.inl (.inr false)) K.selfDualSuspension_a_vertex).face (s.image suspensionBierLabel) ↔
        (K.ghost.bier K.ghost_proper).face s := by
  classical
  have hnot : Sum.inl (Sum.inr false) ∉ s.image suspensionBierLabel := by
    intro h
    have := (Finset.mem_toLeft).mpr h
    rw [toLeft_image_suspensionBierLabel] at this
    exact a_notMem_image_suspensionLabel s.toLeft this
  rw [link_face, and_iff_right hnot,
    bier_selfdual_face_iff _ _ K.selfDualSuspension_dual]
  simp only [toLeft_insert_inl, toRight_insert_inl,
    toLeft_image_suspensionBierLabel, toRight_image_suspensionBierLabel,
    suspension_insert_a_image_face, suspension_image_face]
  rw [Finset.disjoint_insert_left]
  simp only [a_notMem_image_suspensionLabel, not_false_eq_true, true_and]
  rw [Finset.disjoint_image suspensionLabel_injective]
  rw [bier_face_iff]
  exact and_congr_right fun _ => and_congr_left fun _ => (ghost_dual_face K s.toRight).symm

def suspensionUnlabel : V ⊕ Bool → Option V
  | .inl v => some v
  | .inr _ => none

theorem suspensionLabel_unlabel {v : V ⊕ Bool} (hv : v ≠ .inr false) :
    suspensionLabel (suspensionUnlabel v) = v := by
  cases v with
  | inl v => rfl
  | inr b => cases b <;> simp_all [suspensionUnlabel, suspensionLabel]

theorem selfDualSuspension_link_eq_map (K : Bier.Complex V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).link
        (.inl (.inr false)) K.selfDualSuspension_a_vertex =
      (K.ghost.bier K.ghost_proper).map suspensionBierLabel := by
  classical
  apply Bier.Complex.ext
  funext s
  apply propext
  constructor
  · intro hs
    have ha : Sum.inl (Sum.inr false) ∉ s := hs.1
    have hap : Sum.inr (Sum.inr false) ∉ s := by
      intro h
      have hL : Sum.inr false ∈ (insert (Sum.inl (Sum.inr false)) s).toLeft := by simp
      have hR : Sum.inr false ∈ (insert (Sum.inl (Sum.inr false)) s).toRight := by simpa using h
      exact Finset.disjoint_left.mp hs.2.2.2 hL hR
    let t := s.image (Sum.map suspensionUnlabel suspensionUnlabel)
    have heq : t.image suspensionBierLabel = s := by
      rw [Finset.image_image]
      conv_rhs => rw [← Finset.image_id (s := s)]
      apply Finset.image_congr
      intro v hv
      cases v with
      | inl v =>
        change Sum.inl (suspensionLabel (suspensionUnlabel v)) = Sum.inl v
        rw [suspensionLabel_unlabel (fun h => ha (h ▸ hv))]
      | inr v =>
        change Sum.inr (suspensionLabel (suspensionUnlabel v)) = Sum.inr v
        rw [suspensionLabel_unlabel (fun h => hap (h ▸ hv))]
    exact ⟨t, (suspension_link_image_face K t).mp (heq.symm ▸ hs), heq⟩
  · rintro ⟨t, ht, rfl⟩
    exact (suspension_link_image_face K t).mpr ht

end Bier.Complex
