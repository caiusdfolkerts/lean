module

public import FacePlacementCodes
public import CellRelabelGeometry

@[expose] public section

/-!
# Compatible facets fit a common-face placement block

The common vertex set is a proper face in each complete boundary. Its
preimage in the local template and its image in the root determine the
two blocks of a compressed injection. The number of vertices outside the
root gives the exact second-block capacity.
-/

noncomputable section
namespace Papers.RationalityTen.FacePlacementGeometry

open Finset
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open FacePlacementCodes

structure Normalizes {m : Nat} (B : Block m)
    (sourceFace : Finset (Fin m)) (rootFace rootVertices : Finset (Fin 10)) : Prop where
  source_inside : ∀ i, B.source i ∈ sourceFace ↔ i.val < B.shared
  target_inside : ∀ i, B.target i ∈ rootFace ↔ i.val < B.shared
  target_outside : ∀ i, B.target i ∉ rootVertices ↔
    B.shared ≤ i.val ∧ i.val < B.shared + B.outside

theorem properFaces_mapEmbedding {m : Nat} (f : Fin m ↪ Fin 10) (C : Cell m) :
    (mapCell f C).properFaces = C.properFaces.image (fun S => S.image f) := by
  simp only [Cell.properFaces, mapCell, Finset.image_union, Finset.image_singleton,
    Finset.image_empty, Finset.image_image, Function.comp_def]

theorem fits_of_normalizes {m : Nat} (B : Block m) (f : Fin m ↪ Fin 10)
    (S : Finset (Fin m)) (R V : Finset (Fin 10))
    (H : Normalizes B S R V) (himage : S.image f = R)
    (hcommon : R = (Finset.univ.image f) ∩ V) : B.Fits f := by
  intro i
  have hin := H.target_inside (B.normalized f i)
  have hout := H.target_outside (B.normalized f i)
  simp only [Block.normalized, B.target.apply_symm_apply] at hin hout
  by_cases hi : i.val < B.shared
  · rw [if_pos hi]
    apply hin.mp
    rw [← himage]
    exact Finset.mem_image_of_mem f ((H.source_inside i).mpr hi)
  · rw [if_neg hi]
    apply hout.mp
    intro hv
    have hR : f (B.source i) ∈ R := by
      rw [hcommon]
      exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ _), hv⟩
    rw [← himage] at hR
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hR
    have heq : j = B.source i := f.injective hji
    exact hi ((H.source_inside i).mp (heq ▸ hj))

/-- Completeness is a finite obligation involving only proper faces of the
two literal cells. It does not quantify over polytopes or unknown facets. -/
def CompleteBlocks {m b : Nat} (C : Cell m) (root : Cell 10)
    (blocks : Fin b → Block m) : Prop :=
  ∀ S ∈ C.properFaces, ∀ R ∈ root.properFaces,
    S.card = R.card → m - S.card ≤ 10 - root.vertices.card →
      ∃ i, Normalizes (blocks i) S R root.vertices

/-- Every geometric embedding compatible with the root fits one checked
common-face block, and hence one pair of reduced injection codes. -/
theorem exists_block_and_codes {m b : Nat} (C : Cell m) (root : Cell 10)
    (hvertices : C.vertices = Finset.univ) (blocks : Fin b → Block m)
    (hblocks : CompleteBlocks C root blocks) (f : Fin m ↪ Fin 10)
    (hcompatible : (mapCell f C).Compatible root) :
    ∃ i, ∃ inner, inner < FiniteCycleCandidates.injectionCount (blocks i).shared
      (blocks i).shared ∧ ∃ outer,
      outer < FiniteCycleCandidates.injectionCount (blocks i).outside
        (m - (blocks i).shared) ∧ (blocks i).decoded inner outer = f := by
  let R := (mapCell f C).vertices ∩ root.vertices
  have hR : R ∈ root.properFaces := hcompatible.2.1
  have hS : R ∈ C.properFaces.image (fun S => S.image f) := by
    rw [← properFaces_mapEmbedding]
    exact hcompatible.1
  obtain ⟨S, hS, himage⟩ := Finset.mem_image.mp hS
  have hcard : S.card = R.card := by
    rw [← himage, Finset.card_image_of_injective _ f.injective]
  have hcommon : R = (Finset.univ.image f) ∩ root.vertices := by
    simp only [R, mapCell, hvertices]
  have hcapacity : m - S.card ≤ 10 - root.vertices.card := by
    have hu : ((Finset.univ.image f) ∪ root.vertices).card ≤ 10 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ ((Finset.univ.image f) ∪ root.vertices))
    have hcount := Finset.card_union_add_card_inter (Finset.univ.image f) root.vertices
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ,
      Fintype.card_fin, ← hcommon, ← hcard] at hcount
    omega
  obtain ⟨i, hi⟩ := hblocks S hS R hR hcard hcapacity
  exact ⟨i, exists_codes (blocks i) f
    (fits_of_normalizes (blocks i) f S R root.vertices hi himage hcommon)⟩

end Papers.RationalityTen.FacePlacementGeometry
