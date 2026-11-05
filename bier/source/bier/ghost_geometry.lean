import bier.facet_coordinates
import bier.facets
import bier.schur_algebra

/-! # The actual labelled vertices and facet bases in a ghost Bier realization -/

noncomputable section

namespace Bier

open Classical Finset Set Matrix
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {E : Type*} [Fintype E] [DecidableEq E]

abbrev ghostBier (K : Complex E) := K.ghost.bier K.ghost_proper

def ghostX (K : Complex E) (hv : ∀ i, K.face {i}) (i : E) : ↥(ghostBier K).vertices :=
  ⟨Sum.inl (some i), K.ghost_bier_x_vertex (hv i)⟩

def ghostP (K : Complex E) (i : E) : ↥(ghostBier K).vertices :=
  ⟨Sum.inr (some i), K.ghost_bier_p_vertex i⟩

def ghostZ (K : Complex E) (hK : K.Proper) : ↥(ghostBier K).vertices :=
  ⟨Sum.inr none, K.ghost_bier_z_vertex hK⟩

def ghostChoice (K : Complex E) (hv : ∀ i, K.face {i}) (A : Finset E) (i : E) :
    ↥(ghostBier K).vertices := if i ∈ A then ghostX K hv i else ghostP K i

theorem ghostChoice_injective (K : Complex E) (hv : ∀ i, K.face {i}) (A : Finset E) :
    Function.Injective (ghostChoice K hv A) := by
  intro i j he
  have he' := congrArg Subtype.val he
  dsimp [ghostChoice, ghostX, ghostP] at he'
  split_ifs at he' <;> simp_all

def ghostTopVertices (K : Complex E) (hv : ∀ i, K.face {i}) (A : Finset E) :
    Finset ↥(ghostBier K).vertices := Finset.univ.image (ghostChoice K hv A)

theorem ghostTopVertices_labels (K : Complex E) (hv : ∀ i, K.face {i}) (A : Finset E) :
    (ghostTopVertices K hv A).image Subtype.val = Complex.ghostTopFace A := by
  ext v
  simp only [ghostTopVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    dsimp [ghostChoice]
    split_ifs with hi <;> simp [ghostX, ghostP, Complex.ghostTopFace, hi]
  · intro hv'
    cases v with
    | inl v =>
      obtain ⟨i, hi, rfl⟩ : ∃ i ∈ A, some i = v := by
        simpa [Complex.ghostTopFace] using hv'
      exact ⟨ghostChoice K hv A i, ⟨i, rfl⟩, by simp [ghostChoice, hi, ghostX]⟩
    | inr v =>
      obtain ⟨i, hi, rfl⟩ : ∃ i ∈ Aᶜ, some i = v := by
        simpa [Complex.ghostTopFace] using hv'
      exact ⟨ghostChoice K hv A i, ⟨i, rfl⟩, by
        simp [ghostChoice, Finset.mem_compl.mp hi, ghostP]⟩

@[simp] theorem ghostX_mem_top (K : Complex E) (hv : ∀ i, K.face {i})
    (A : Finset E) (i : E) : ghostX K hv i ∈ ghostTopVertices K hv A ↔ i ∈ A := by
  simp only [ghostTopVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have he := congrArg Subtype.val hj
    dsimp [ghostChoice] at he
    split_ifs at he with h
    · have hij : j = i := by simpa [ghostX] using he
      exact hij ▸ h
    · simp [ghostP, ghostX] at he
  · intro hi
    exact ⟨i, by simp [ghostChoice, hi]⟩

@[simp] theorem ghostP_mem_top (K : Complex E) (hv : ∀ i, K.face {i})
    (A : Finset E) (i : E) : ghostP K i ∈ ghostTopVertices K hv A ↔ i ∉ A := by
  simp only [ghostTopVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have he := congrArg Subtype.val hj
    dsimp [ghostChoice] at he
    split_ifs at he with h
    · simp [ghostP, ghostX] at he
    · have hij : j = i := by simpa [ghostP] using he
      exact hij ▸ h
  · intro hi
    exact ⟨i, by simp [ghostChoice, hi]⟩

@[simp] theorem ghostZ_not_mem_top (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (A : Finset E) :
    ghostZ K hK ∉ ghostTopVertices K hv A := by
  rintro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  have he := congrArg Subtype.val hj
  dsimp [ghostChoice] at he
  split_ifs at he <;> simp [ghostP, ghostX, ghostZ] at he

theorem ghostTopVertices_face (K : Complex E) (hv : ∀ i, K.face {i})
    {A : Finset E} (hA : K.face A) :
    (ghostBier K).face ((ghostTopVertices K hv A).image Subtype.val) := by
  rw [ghostTopVertices_labels]
  exact K.ghostTopFace_face hA

theorem proper_nonempty_type (K : Complex E) (hK : K.Proper) : Nonempty E := by
  by_contra hn
  haveI : IsEmpty E := not_nonempty_iff.mp hn
  apply hK
  simpa using K.empty

theorem polytopal_ghost_normalized (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (hP : Polytopal (ghostBier K)) :
    ∃ M : CoordinateModel (ghostBier K) E,
      M.point (ghostZ K hK) = 0 ∧ ∀ i, M.point (ghostP K i) = Pi.single i 1 := by
  letI := proper_nonempty_type K hK
  obtain ⟨n, ⟨r⟩⟩ := hP
  have hp : Function.Injective (ghostP K) := by
    intro i j h
    simpa [ghostP] using congrArg Subtype.val h
  have he : ghostTopVertices K hv ∅ = Finset.univ.image (ghostP K) := by
    unfold ghostTopVertices
    congr 1
  have hf := ghostTopVertices_face K hv K.empty
  have hn : (ghostTopVertices K hv ∅).Nonempty := Finset.univ_nonempty.image _
  have hd := r.dim_eq_face_card hf hn (fun f hf => by
    have hh := K.ghost_bier_card_le hf
    simpa only [ghostTopVertices, Finset.card_image_of_injective _
      (ghostChoice_injective K hv ∅), Finset.card_univ] using hh)
  have hc : (ghostTopVertices K hv ∅).card = Fintype.card E := by
    rw [ghostTopVertices, Finset.card_image_of_injective _ (ghostChoice_injective K hv ∅),
      Finset.card_univ]
  rw [hc] at hd
  exact r.normalized_coordinates (ghostP K) hp (ghostZ K hK)
    (he ▸ ghostZ_not_mem_top K hK hv ∅) (he ▸ hf) hd

namespace CoordinateModel

theorem face_columns_isUnit {K : Complex E} {J : Type*} [Fintype J] [DecidableEq J]
    [Nonempty J] (M : CoordinateModel K J) (p : J → ↥K.vertices)
    (hp : Function.Injective p) (z : ↥K.vertices) (hz0 : M.point z = 0)
    (hz : z ∉ Finset.univ.image p)
    (hface : K.face ((Finset.univ.image p).image Subtype.val)) :
    IsUnit (Matrix.of fun i j => M.point (p j) i) := by
  let s := Finset.univ.image p
  have hs : s.Nonempty := Finset.univ_nonempty.image p
  have hAI : AffineIndependent ℝ (fun j => M.point (p j)) := by
    let e : J ↪ s := ⟨fun j => ⟨p j, Finset.mem_image_of_mem p (Finset.mem_univ j)⟩,
      fun i j h => hp (congrArg Subtype.val h)⟩
    exact (M.affineIndependent s hface hs).comp_embedding e
  obtain ⟨l, c, _, hl⟩ := M.supporting s hface hs
  have hpv (i : J) : l (M.point (p i)) = c :=
    (hl _).mpr (Finset.mem_image_of_mem p (Finset.mem_univ i))
  have hzv : l (M.point z) ≠ c := fun he => hz ((hl z).mp he)
  have hLI := linearIndependent_of_affineIndependent_supporting
    (fun i => M.point (p i)) (M.point z) hAI l c hpv hzv
  simp only [hz0, sub_zero] at hLI
  exact Matrix.linearIndependent_col_iff_isUnit.mp hLI

end CoordinateModel

theorem replacementMatrix_isUnit_of_ghost_coordinates (K : Complex E) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (M : CoordinateModel (ghostBier K) E)
    (hz : M.point (ghostZ K hK) = 0)
    (hp : ∀ i, M.point (ghostP K i) = Pi.single i 1)
    {A : Finset E} (hA : K.face A) :
    IsUnit (replacementMatrix (fun i j => M.point (ghostX K hv j) i) A) := by
  letI := proper_nonempty_type K hK
  have h := M.face_columns_isUnit (ghostChoice K hv A) (ghostChoice_injective K hv A)
    (ghostZ K hK) hz (ghostZ_not_mem_top K hK hv A) (ghostTopVertices_face K hv hA)
  convert h using 1
  ext i j
  by_cases hj : j ∈ A
  · simp [replacementMatrix, ghostChoice, hj]
  · simp [replacementMatrix, ghostChoice, hj, hp, Pi.single_apply, Matrix.one_apply, eq_comm]

end Bier
