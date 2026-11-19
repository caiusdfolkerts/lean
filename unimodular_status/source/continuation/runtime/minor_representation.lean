module

public import Recovery.Unimodular.ProductVectorMatroid

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Quotient representations of actual embedded minors

The starting hypothesis is Mathlib's ordinary minor relation. The contracted
set is extracted from that relation, and its actual vector span is the kernel
of the resulting quotient map. No representation of the minor is assumed.
-/

open Set Submodule
open scoped Matroid

namespace Unimodular.RepresentationBridge

theorem mapEmbedding_injective {E F : Type*} (f : E ↪ F) :
    Function.Injective (fun M : Matroid E ↦ M.mapEmbedding f) := by
  intro M N h
  have hh := congrArg (fun P : Matroid F ↦ P.comap f) h
  simpa only [Matroid.mapEmbedding, Matroid.comap_map f.injective] using hh

theorem exists_quotient_representation_of_minor
    {K E F V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (M : Matroid E) (hME : M.E = Set.univ) (v : F → V) (f : E ↪ F)
    (hminor : M.mapEmbedding f ≤m VectorMatroid.ofFamily (K := K) v) :
    ∃ C : Set F, Disjoint (Set.range f) C ∧
      M = VectorMatroid.ofFamily (K := K)
        ((span K (v '' C)).mkQ ∘ v ∘ f) := by
  obtain ⟨C, D, h⟩ := hminor
  have hground : Set.range f = (Set.univ \ C) \ D := by
    simpa [hME] using congrArg Matroid.E h
  have hdisjoint : Disjoint (Set.range f) C := by
    apply Set.disjoint_left.mpr
    intro x hx hC
    rw [hground] at hx
    exact hx.1.2 hC
  let q := (span K (v '' C)).mkQ
  have heq : M.mapEmbedding f =
      VectorMatroid.onSet (K := K) (q ∘ v) (Set.range f) := by
    rw [h, VectorMatroid.ofFamily,
      VectorMatroid.contract_eq_quotient v (Set.subset_univ C),
      VectorMatroid.delete_onSet, ← hground]
  have hmap := VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (K := K) (q ∘ v ∘ f) (q ∘ v) f (fun _ ↦ rfl)
  exact ⟨C, hdisjoint, mapEmbedding_injective f (heq.trans hmap.symm)⟩

#print axioms exists_quotient_representation_of_minor
end Unimodular.RepresentationBridge
