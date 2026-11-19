module

public import FiniteFacetCells

@[expose] public section

/-!
# Complete cell compatibility is invariant under vertex relabeling

Every edge and ridge is transported along the same vertex permutation.
The proof is independent of literal cell tables, so checking an orbit's
cell map never requires checking a quadratic compatibility matrix.
-/

namespace Papers.RationalityTen.CellRelabelGeometry

open Finset Set
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport

variable {n : ℕ}

theorem image_image_symm (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (S.image σ).image σ.symm = S := by
  rw [Finset.image_image, σ.symm_comp_self, Finset.image_id]

theorem image_symm_image (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (S.image σ.symm).image σ = S := by
  rw [Finset.image_image, σ.self_comp_symm, Finset.image_id]

theorem mapCell_inverse (σ : Equiv.Perm (Fin n)) (C : Cell n) :
    mapCell σ.symm.toEmbedding (mapCell σ.toEmbedding C) = C := by
  apply cell_ext
  · exact image_image_symm σ C.vertices
  · change (C.edges.image (fun S => S.image σ)).image (fun S => S.image σ.symm) = C.edges
    rw [Finset.image_image]
    simp only [Function.comp_def, image_image_symm, Finset.image_id']
  · change (C.ridges.image (fun S => S.image σ)).image (fun S => S.image σ.symm) = C.ridges
    rw [Finset.image_image]
    simp only [Function.comp_def, image_image_symm, Finset.image_id']

theorem properFaces_mapCell (σ : Equiv.Perm (Fin n)) (C : Cell n) :
    (mapCell σ.toEmbedding C).properFaces =
      C.properFaces.image (fun S => S.image σ) := by
  simp only [Cell.properFaces, mapCell, Finset.image_union, Finset.image_singleton,
    Finset.image_empty, Finset.image_image, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.coe_toEmbedding]

theorem mem_image_family_iff (σ : Equiv.Perm (Fin n))
    (family : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    S.image σ ∈ family.image (fun T => T.image σ) ↔ S ∈ family := by
  constructor
  · intro h
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp h
    exact (Finset.image_injective σ.injective hTS) ▸ hT
  · exact Finset.mem_image_of_mem _

theorem compatible_mapCell (σ : Equiv.Perm (Fin n)) (A B : Cell n)
    (h : A.Compatible B) :
    (mapCell σ.toEmbedding A).Compatible (mapCell σ.toEmbedding B) := by
  have hi : (A.vertices ∩ B.vertices).image σ =
      (mapCell σ.toEmbedding A).vertices ∩ (mapCell σ.toEmbedding B).vertices :=
    Finset.image_inter _ _ σ.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [properFaces_mapCell, ← hi]
    exact Finset.mem_image_of_mem _ h.1
  · rw [properFaces_mapCell, ← hi]
    exact Finset.mem_image_of_mem _ h.2.1
  · intro S hS
    let T := S.image σ.symm
    have hTS : T.image σ = S := image_symm_image σ S
    have hsub : T ⊆ A.vertices ∩ B.vertices := by
      apply (Finset.image_subset_image_iff σ.injective).mp
      rw [hTS, hi]
      exact hS
    rw [← hTS]
    change T.image σ ∈ A.edges.image (fun e => e.image σ) ↔
      T.image σ ∈ B.edges.image (fun e => e.image σ)
    rw [mem_image_family_iff, mem_image_family_iff]
    exact h.2.2 T hsub

theorem compatible_mapCell_iff (σ : Equiv.Perm (Fin n)) (A B : Cell n) :
    (mapCell σ.toEmbedding A).Compatible (mapCell σ.toEmbedding B) ↔ A.Compatible B := by
  constructor
  · intro h
    have h' := compatible_mapCell σ.symm _ _ h
    simpa only [mapCell_inverse] using h'
  · exact compatible_mapCell σ A B

end Papers.RationalityTen.CellRelabelGeometry
