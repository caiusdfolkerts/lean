module
public import MatroidChecked.CatalogueColoops

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Coloop steps in the exhaustive catalogue

A coloop is inserted into every old basis. The exact mask identities in
`CatalogueColoops` identify the result with the corresponding catalogue
entry, so the isomorphism witness is the identity permutation.
-/

open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
namespace Papers.RationalityTen.MatroidCatalogue

theorem coloop_1_2 (hn : 1 < 8) : ColoopCovered catalogue 1 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨1, hn⟩ : Fin 8) = (1 : Fin 8) := Fin.ext rfl
  refine ⟨family 2 2 i, family_mem 2 2 i ?_, ?_⟩
  · change i < 1
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_1_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 2 _

theorem coloop_2_2 (hn : 2 < 8) : ColoopCovered catalogue 2 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨2, hn⟩ : Fin 8) = (2 : Fin 8) := Fin.ext rfl
  refine ⟨family 3 2 i, family_mem 3 2 i ?_, ?_⟩
  · change i < 2
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_2_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 3 _

theorem coloop_2_3 (hn : 2 < 8) : ColoopCovered catalogue 2 3 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨2, hn⟩ : Fin 8) = (2 : Fin 8) := Fin.ext rfl
  refine ⟨family 3 3 i, family_mem 3 3 i ?_, ?_⟩
  · change i < 1
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_2_3 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 3 _

theorem coloop_3_2 (hn : 3 < 8) : ColoopCovered catalogue 3 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨3, hn⟩ : Fin 8) = (3 : Fin 8) := Fin.ext rfl
  refine ⟨family 4 2 i, family_mem 4 2 i ?_, ?_⟩
  · change i < 4
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_3_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 4 _

theorem coloop_3_3 (hn : 3 < 8) : ColoopCovered catalogue 3 3 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 2 := Finset.mem_range.mp hi
  have hpoint : (⟨3, hn⟩ : Fin 8) = (3 : Fin 8) := Fin.ext rfl
  refine ⟨family 4 3 i, family_mem 4 3 i ?_, ?_⟩
  · change i < 3
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_3_3 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 4 _

theorem coloop_3_4 (hn : 3 < 8) : ColoopCovered catalogue 3 4 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨3, hn⟩ : Fin 8) = (3 : Fin 8) := Fin.ext rfl
  refine ⟨family 4 4 i, family_mem 4 4 i ?_, ?_⟩
  · change i < 1
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_3_4 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 4 _

theorem coloop_4_2 (hn : 4 < 8) : ColoopCovered catalogue 4 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨4, hn⟩ : Fin 8) = (4 : Fin 8) := Fin.ext rfl
  refine ⟨family 5 2 i, family_mem 5 2 i ?_, ?_⟩
  · change i < 6
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_4_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 5 _

theorem coloop_4_3 (hn : 4 < 8) : ColoopCovered catalogue 4 3 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 4 := Finset.mem_range.mp hi
  have hpoint : (⟨4, hn⟩ : Fin 8) = (4 : Fin 8) := Fin.ext rfl
  refine ⟨family 5 3 i, family_mem 5 3 i ?_, ?_⟩
  · change i < 9
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_4_3 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 5 _

theorem coloop_4_4 (hn : 4 < 8) : ColoopCovered catalogue 4 4 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 3 := Finset.mem_range.mp hi
  have hpoint : (⟨4, hn⟩ : Fin 8) = (4 : Fin 8) := Fin.ext rfl
  refine ⟨family 5 4 i, family_mem 5 4 i ?_, ?_⟩
  · change i < 4
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_4_4 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 5 _

theorem coloop_5_2 (hn : 5 < 8) : ColoopCovered catalogue 5 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨5, hn⟩ : Fin 8) = (5 : Fin 8) := Fin.ext rfl
  refine ⟨family 6 2 i, family_mem 6 2 i ?_, ?_⟩
  · change i < 10
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_5_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 6 _

theorem coloop_5_3 (hn : 5 < 8) : ColoopCovered catalogue 5 3 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 6 := Finset.mem_range.mp hi
  have hpoint : (⟨5, hn⟩ : Fin 8) = (5 : Fin 8) := Fin.ext rfl
  refine ⟨family 6 3 i, family_mem 6 3 i ?_, ?_⟩
  · change i < 25
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_5_3 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 6 _

theorem coloop_5_4 (hn : 5 < 8) : ColoopCovered catalogue 5 4 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 9 := Finset.mem_range.mp hi
  have hpoint : (⟨5, hn⟩ : Fin 8) = (5 : Fin 8) := Fin.ext rfl
  refine ⟨family 6 4 i, family_mem 6 4 i ?_, ?_⟩
  · change i < 18
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_5_4 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 6 _

theorem coloop_6_2 (hn : 6 < 8) : ColoopCovered catalogue 6 2 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 1 := Finset.mem_range.mp hi
  have hpoint : (⟨6, hn⟩ : Fin 8) = (6 : Fin 8) := Fin.ext rfl
  refine ⟨family 7 2 i, family_mem 7 2 i ?_, ?_⟩
  · change i < 14
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_6_2 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 7 _

theorem coloop_6_3 (hn : 6 < 8) : ColoopCovered catalogue 6 3 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 10 := Finset.mem_range.mp hi
  have hpoint : (⟨6, hn⟩ : Fin 8) = (6 : Fin 8) := Fin.ext rfl
  refine ⟨family 7 3 i, family_mem 7 3 i ?_, ?_⟩
  · change i < 70
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_6_3 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 7 _

theorem coloop_6_4 (hn : 6 < 8) : ColoopCovered catalogue 6 4 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 25 := Finset.mem_range.mp hi
  have hpoint : (⟨6, hn⟩ : Fin 8) = (6 : Fin 8) := Fin.ext rfl
  refine ⟨family 7 4 i, family_mem 7 4 i ?_, ?_⟩
  · change i < 85
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_6_4 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 7 _

theorem coloop_7_4 (hn : 7 < 8) : ColoopCovered catalogue 7 4 hn := by
  intro hr B hB
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
  have hiBound : i < 70 := Finset.mem_range.mp hi
  have hpoint : (⟨7, hn⟩ : Fin 8) = (7 : Fin 8) := Fin.ext rfl
  refine ⟨family 8 4 i, family_mem 8 4 i ?_, ?_⟩
  · change i < 832
    omega
  · rw [hpoint, MatroidChecked.CatalogueColoops.family_7_4 ⟨i, hiBound⟩]
    exact isomorphicWithin_refl 8 _

end Papers.RationalityTen.MatroidCatalogue
