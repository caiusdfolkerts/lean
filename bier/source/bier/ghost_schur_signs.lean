import bier.ghost_geometry
import bier.supporting_signs

/-! # Lemma 3: the supporting facets determine the Schur signs -/

noncomputable section

namespace Bier

open Classical Finset Set Matrix

variable {E : Type*} [Fintype E] [DecidableEq E]

def ghostTransitionVertices (K : Complex E) (hK : K.Proper) (hv : ∀ i, K.face {i})
    (A : Finset E) (a : E) : Finset ↥(ghostBier K).vertices :=
  insert (ghostZ K hK) ((A.image (ghostX K hv)) ∪ ((insert a A)ᶜ.image (ghostP K)))

theorem ghostTransitionVertices_labels (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (A : Finset E) (a : E) :
    (ghostTransitionVertices K hK hv A a).image Subtype.val =
      Complex.ghostTransitionFace A a := by
  simp only [ghostTransitionVertices, Finset.image_insert, Finset.image_union,
    Finset.image_image]
  ext v
  cases v with
  | inl v => simp [Complex.ghostTransitionFace, ghostX, ghostP, ghostZ]
  | inr v =>
    cases v <;> simp [Complex.ghostTransitionFace, ghostX, ghostP, ghostZ]

@[simp] theorem ghostX_mem_transition (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (A : Finset E) (a i : E) :
    ghostX K hv i ∈ ghostTransitionVertices K hK hv A a ↔ i ∈ A := by
  simp [ghostTransitionVertices, Finset.mem_image, ghostX, ghostP, ghostZ, Subtype.ext_iff]

@[simp] theorem ghostP_mem_transition (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (A : Finset E) (a i : E) :
    ghostP K i ∈ ghostTransitionVertices K hK hv A a ↔ i ∉ insert a A := by
  simp [ghostTransitionVertices, Finset.mem_image, ghostX, ghostP, ghostZ, Subtype.ext_iff]

@[simp] theorem ghostZ_mem_transition (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (A : Finset E) (a : E) :
    ghostZ K hK ∈ ghostTransitionVertices K hK hv A a := Finset.mem_insert_self _ _

theorem ghostTransitionVertices_face (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) {A : Finset E} {a : E}
    (hA : K.face A) (hAa : ¬ K.face (insert a A)) :
    (ghostBier K).face ((ghostTransitionVertices K hK hv A a).image Subtype.val) := by
  rw [ghostTransitionVertices_labels]
  exact K.ghostTransitionFace_face hA hAa

theorem ghost_replacement_col (K : Complex E) (hv : ∀ i, K.face {i})
    (M : CoordinateModel (ghostBier K) E)
    (hp : ∀ i, M.point (ghostP K i) = Pi.single i 1) (A : Finset E) (j : E) :
    (replacementMatrix (fun i j => M.point (ghostX K hv j) i) A).col j =
      M.point (ghostChoice K hv A j) := by
  funext i
  by_cases hj : j ∈ A
  · simp [replacementMatrix, Matrix.col, ghostChoice, hj]
  · simp [replacementMatrix, Matrix.col, ghostChoice, hj, hp, Pi.single_apply,
      Matrix.one_apply, eq_comm]

theorem ghost_exchange_coordinate_neg (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (M : CoordinateModel (ghostBier K) E)
    (hz : M.point (ghostZ K hK) = 0)
    (hp : ∀ i, M.point (ghostP K i) = Pi.single i 1)
    {A : Finset E} (hA : K.face A) (a : E) (ha : a ∉ A)
    (hAa : K.face (insert a A)) (α : E → ℝ)
    (hα : replacementMatrix (fun i j => M.point (ghostX K hv j) i) A *ᵥ α =
      M.point (ghostX K hv a)) : α a < 0 := by
  letI := proper_nonempty_type K hK
  have hn (B : Finset E) : (ghostTopVertices K hv B).Nonempty := Finset.univ_nonempty.image _
  obtain ⟨f, hf_le, hf_eq⟩ := M.supporting_normalized _
    (ghostTopVertices_face K hv hA) (hn A) (ghostZ K hK) hz (ghostZ_not_mem_top K hK hv A)
  obtain ⟨g, hg_le, hg_eq⟩ := M.supporting_normalized _
    (ghostTopVertices_face K hv hAa) (hn (insert a A)) (ghostZ K hK) hz
    (ghostZ_not_mem_top K hK hv (insert a A))
  apply exchange_coordinate_neg _ _ α a hα f g
  · intro j
    rw [ghost_replacement_col K hv M hp]
    exact (hf_eq _).mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  · apply lt_of_le_of_ne (hf_le _)
    intro he
    exact ha ((ghostX_mem_top K hv A a).mp ((hf_eq _).mp he))
  · intro j hja
    rw [ghost_replacement_col K hv M hp]
    apply (hg_eq _).mpr
    by_cases hj : j ∈ A
    · simp [ghostChoice, hj]
    · simp [ghostChoice, hj, hja]
  · exact (hg_eq _).mpr (by simp)
  · rw [ghost_replacement_col K hv M hp]
    simp only [ghostChoice, if_neg ha]
    apply lt_of_le_of_ne (hg_le _)
    intro he
    have hn := (hg_eq _).mp he
    simpa using hn

theorem ghost_transition_coordinate_pos (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (M : CoordinateModel (ghostBier K) E)
    (hz : M.point (ghostZ K hK) = 0)
    (hp : ∀ i, M.point (ghostP K i) = Pi.single i 1)
    {A : Finset E} (hA : K.face A) (a : E) (ha : a ∉ A)
    (hAa : ¬ K.face (insert a A)) (α : E → ℝ)
    (hα : replacementMatrix (fun i j => M.point (ghostX K hv j) i) A *ᵥ α =
      M.point (ghostX K hv a)) : 0 < α a := by
  let t := ghostTransitionVertices K hK hv A a
  obtain ⟨f, c, hf_le, hf_eq⟩ := M.supporting t
    (ghostTransitionVertices_face K hK hv hA hAa) (Finset.insert_nonempty _ _)
  have hc : c = 0 := by
    have he := (hf_eq (ghostZ K hK)).mpr (ghostZ_mem_transition K hK hv A a)
    simpa [hz] using he.symm
  subst c
  apply transition_coordinate_pos _ _ α a hα f
  · intro j hja
    rw [ghost_replacement_col K hv M hp]
    apply (hf_eq _).mpr
    by_cases hj : j ∈ A
    · simp [t, ghostChoice, hj]
    · simp [t, ghostChoice, hj, hja]
  · apply lt_of_le_of_ne (hf_le _)
    intro he
    exact ha ((ghostX_mem_transition K hK hv A a a).mp ((hf_eq _).mp he))
  · rw [ghost_replacement_col K hv M hp]
    simp only [ghostChoice, if_neg ha]
    apply lt_of_le_of_ne (hf_le _)
    intro he
    have hn := (hf_eq _).mp he
    simpa [t] using hn

/-- The coordinate version of Lemma 3, including strict signs for every extension test. -/
theorem ghost_schur_signs (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (hP : Polytopal (ghostBier K)) :
    ∃ X : Matrix E E ℝ, ∀ (A : Finset E), K.face A →
      IsUnit (principalMatrix X A).det ∧
        ∀ a, a ∉ A →
          (K.face (insert a A) → schurValue X A a < 0) ∧
          (¬ K.face (insert a A) → 0 < schurValue X A a) := by
  obtain ⟨M, hz, hp⟩ := polytopal_ghost_normalized K hK hv hP
  let X : Matrix E E ℝ := fun i j => M.point (ghostX K hv j) i
  refine ⟨X, ?_⟩
  intro A hA
  have hC := replacementMatrix_isUnit_of_ghost_coordinates K hK hv M hz hp hA
  have hCd := (Matrix.isUnit_iff_isUnit_det _).mp hC
  have hS := replacementMatrix_principal_isUnit X A hC
  refine ⟨hS, ?_⟩
  intro a ha
  let α := (replacementMatrix X A)⁻¹ *ᵥ (fun i => X i a)
  have hα : replacementMatrix X A *ᵥ α = M.point (ghostX K hv a) := by
    dsimp [α]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hCd, Matrix.one_mulVec]
  have he := replacementMatrix_solution_coordinate X A hS a ha α hα
  constructor
  · intro hAa
    rw [← he]
    exact ghost_exchange_coordinate_neg K hK hv M hz hp hA a ha hAa α hα
  · intro hAa
    rw [← he]
    exact ghost_transition_coordinate_pos K hK hv M hz hp hA a ha hAa α hα

end Bier
