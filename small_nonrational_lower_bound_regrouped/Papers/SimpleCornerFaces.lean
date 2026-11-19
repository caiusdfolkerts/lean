module
public import Papers.MinkowskiExposedFaces
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section
namespace Papers.SimpleCornerFaces
open Finset Set Module Papers.MinkowskiFaces
open scoped BigOperators Classical Pointwise

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module ℝ E]

def selectedSpan (b : Basis I ℝ E) (S : Finset I) : Submodule ℝ E :=
  Submodule.span ℝ (b '' (S : Set I))

theorem mem_selectedSpan_iff (b : Basis I ℝ E) (S : Finset I) (x : E) :
    x ∈ selectedSpan b S ↔ ∀ i ∉ S, b.repr x i = 0 := by
  rw [selectedSpan,b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  · intro h i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)

def coordinate (b : Basis I ℝ E) (i : I) : E →ₗ[ℝ] ℝ :=
  (Finsupp.lapply i).comp b.repr.toLinearMap

def cornerNormal (b : Basis I ℝ E) (S : Finset I) : E →ₗ[ℝ] ℝ :=
  -(∑ i ∈ Sᶜ, coordinate b i)

theorem cornerNormal_apply (b : Basis I ℝ E) (S : Finset I) (x : E) :
    cornerNormal b S x = -(∑ i ∈ Sᶜ, b.repr x i) := by
  simp [cornerNormal,coordinate]

theorem cornerNormal_le (b : Basis I ℝ E) (S : Finset I)
    {v x : E} (hx : ∀ i, 0 ≤ b.repr (x - v) i) :
    cornerNormal b S x ≤ cornerNormal b S v := by
  have h : cornerNormal b S (x - v) ≤ 0 := by
    rw [cornerNormal_apply]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => hx i)
  simpa only [map_sub,sub_nonpos] using h

theorem maxFace_eq_corner_section
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x - v) i) :
    maxFace P (cornerNormal b S) =
      {x ∈ P | x - v ∈ selectedSpan b S} := by
  ext x
  constructor
  · rintro ⟨hx,hmax⟩
    refine ⟨hx, (mem_selectedSpan_iff b S (x-v)).mpr ?_⟩
    have he : cornerNormal b S x = cornerNormal b S v :=
      (cornerNormal_le b S (hcone x hx)).antisymm (hmax v hv)
    have hz : (∑ i ∈ Sᶜ, b.repr (x-v) i) = 0 := by
      have h : cornerNormal b S (x-v) = 0 := by rw [map_sub,he,sub_self]
      rw [cornerNormal_apply,neg_eq_zero] at h
      exact h
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Sᶜ) => hcone x hx i)).mp hz
    intro i hi
    exact hz' i (Finset.mem_compl.mpr hi)
  · rintro ⟨hx,hspan⟩
    refine ⟨hx,?_⟩
    have hzero := (mem_selectedSpan_iff b S (x-v)).mp hspan
    have he : cornerNormal b S x = cornerNormal b S v := by
      apply sub_eq_zero.mp
      rw [← map_sub,cornerNormal_apply]
      apply neg_eq_zero.mpr
      exact Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_compl.mp hi)
    intro y hy
    rw [he]
    exact cornerNormal_le b S (hcone y hy)

theorem selectedSpan_finrank (b : Basis I ℝ E) (S : Finset I) :
    finrank ℝ (selectedSpan b S) = S.card := by
  have he : b '' (S : Set I) = Set.range (fun i : S => b i) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,i.2,rfl⟩
  rw [selectedSpan,he]
  have h := finrank_span_eq_card (b.linearIndependent.comp
    (fun i : S => (i : I)) Subtype.val_injective)
  simpa only [Function.comp_def, Fintype.card_coe] using h

theorem corner_section_vectorSpan
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    vectorSpan ℝ {x ∈ P | x - v ∈ selectedSpan b S} = selectedSpan b S := by
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    have h := (selectedSpan b S).sub_mem hx.2 hy.2
    change x - y ∈ selectedSpan b S
    convert h using 1 <;> abel
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    have hbi : b i ∈ selectedSpan b S := Submodule.subset_span ⟨i,hi,rfl⟩
    have hvF : v ∈ {x ∈ P | x-v ∈ selectedSpan b S} :=
      ⟨hv,by simp⟩
    have hiF : v + b i ∈ {x ∈ P | x-v ∈ selectedSpan b S} :=
      ⟨hneighbors i hi,by simpa only [add_sub_cancel_left] using hbi⟩
    change b i ∈ vectorSpan ℝ {x ∈ P | x-v ∈ selectedSpan b S}
    simpa only [vsub_eq_sub,add_sub_cancel_left] using vsub_mem_vectorSpan ℝ hiF hvF

theorem corner_section_dimension
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    finrank ℝ (vectorSpan ℝ {x ∈ P | x-v ∈ selectedSpan b S}) = S.card := by
  rw [corner_section_vectorSpan b S P v hv hneighbors,selectedSpan_finrank]

theorem exposed_corner_of_basis_cone
    (b : Basis I ℝ E) (S : Finset I) (P : Set E) (v : E)
    (hv : v ∈ P) (hcone : ∀ x ∈ P, ∀ i, 0 ≤ b.repr (x-v) i)
    (hneighbors : ∀ i ∈ S, v + b i ∈ P) :
    ∃ u : E →ₗ[ℝ] ℝ,
      maxFace P u = {x ∈ P | x-v ∈ selectedSpan b S} ∧
      vectorSpan ℝ (maxFace P u) = selectedSpan b S ∧
      finrank ℝ (vectorSpan ℝ (maxFace P u)) = S.card := by
  refine ⟨cornerNormal b S,maxFace_eq_corner_section b S P v hv hcone,?_,?_⟩
  · rw [maxFace_eq_corner_section b S P v hv hcone]
    exact corner_section_vectorSpan b S P v hv hneighbors
  · rw [maxFace_eq_corner_section b S P v hv hcone]
    exact corner_section_dimension b S P v hv hneighbors

end Papers.SimpleCornerFaces
