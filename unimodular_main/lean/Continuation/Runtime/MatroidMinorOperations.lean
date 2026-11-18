module

public import Recovery.Unimodular.ProductVectorMatroid
public import Mathlib.Combinatorics.Matroid.Dual

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Ordinary minors under injective relabelling and duality -/

open Set
open scoped Matroid

namespace Unimodular.RepresentationBridge

theorem mapEmbedding_comp {E F G : Type*} (M : Matroid E)
    (f : E ↪ F) (g : F ↪ G) :
    (M.mapEmbedding f).mapEmbedding g = M.mapEmbedding (f.trans g) := by
  apply Matroid.ext_indep (by simp [Set.image_image, Function.Embedding.trans_apply])
  intro I hI
  simp only [Matroid.mapEmbedding, Matroid.map_indep_iff]
  constructor
  · rintro ⟨J, ⟨H, hH, rfl⟩, rfl⟩
    refine ⟨H, hH, ?_⟩
    simp [Set.image_image, Function.Embedding.trans_apply]
  · rintro ⟨H, hH, heq⟩
    refine ⟨f '' H, ⟨H, hH, rfl⟩, ?_⟩
    simpa [Set.image_image, Function.Embedding.trans_apply] using heq

theorem mapEmbedding_dual {E F : Type*} (M : Matroid E) (f : E ↪ F) :
    (M.mapEmbedding f)✶ = M✶.mapEmbedding f := by
  simp [Matroid.mapEmbedding]

theorem mapEmbedding_delete {E F : Type*} (M : Matroid E)
    (f : E ↪ F) (D : Set E) :
    (M ＼ D).mapEmbedding f = M.mapEmbedding f ＼ (f '' D) := by
  apply Matroid.ext_indep (by simp [Set.image_sdiff f.injective])
  intro I hI
  simp only [Matroid.mapEmbedding_indep_iff, Matroid.delete_indep_iff,
    Set.disjoint_image_right]
  exact ⟨fun ⟨⟨hi, hd⟩, hr⟩ ↦ ⟨⟨hi, hr⟩, hd⟩,
    fun ⟨⟨hi, hr⟩, hd⟩ ↦ ⟨⟨hi, hd⟩, hr⟩⟩

theorem mapEmbedding_contract {E F : Type*} (M : Matroid E)
    (f : E ↪ F) (C : Set E) :
    (M ／ C).mapEmbedding f = M.mapEmbedding f ／ (f '' C) := by
  apply Matroid.dual_injective
  rw [mapEmbedding_dual, Matroid.dual_contract, mapEmbedding_delete,
    Matroid.dual_contract, mapEmbedding_dual]

theorem isMinor_mapEmbedding {E F : Type*} {N M : Matroid E}
    (h : N ≤m M) (f : E ↪ F) : N.mapEmbedding f ≤m M.mapEmbedding f := by
  obtain ⟨C, D, rfl⟩ := h
  refine ⟨f '' C, f '' D, ?_⟩
  rw [mapEmbedding_delete, mapEmbedding_contract]

theorem isMinor_dual {E : Type*} {N M : Matroid E} (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, _, _, hCD, rfl⟩ := h.exists_eq_contract_delete_disjoint
  refine ⟨D, C, ?_⟩
  rw [Matroid.dual_delete, Matroid.dual_contract,
    ← Matroid.contract_delete_comm _ hCD.symm]

#print axioms isMinor_mapEmbedding
#print axioms isMinor_dual
end Unimodular.RepresentationBridge
