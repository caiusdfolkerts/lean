import cubical.simplicial_geometry
import cubical.complete_rigidity

/-!
# Reindexing finite simplicial circuits

Injectively indexed facet families are equivalent to their ordinary
facet sets. Repeated facets in a minimal circuit give the complete-graph
base case. These facts retain every multiplicity introduced by contraction.
-/

namespace Cubical.Simplicial

open scoped BigOperators
open Cubical.Rigidity
open Module

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- Passing from an injectively indexed family to its image preserves
minimality of the simplicial cycle. -/
theorem IsFacetCircuit.image {σ : I → Finset V} {s : Finset I}
    (hs : IsFacetCircuit σ s) (hinj : Set.InjOn σ s) :
    IsFacetCircuit id (s.image σ) := by
  classical
  refine ⟨hs.nonempty.image σ, ?_, ?_⟩
  · simpa only [Finset.sum_image hinj, id_eq] using hs.sum_eq_zero
  · intro t hts htne htz
    let r := s.filter (fun i => σ i ∈ t)
    have hrs : r ⊆ s := Finset.filter_subset _ _
    have hri : r.image σ = t := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hi).2
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts ha)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩, rfl⟩
    have hrne : r.Nonempty := by
      have h : (r.image σ).Nonempty := hri.symm ▸ htne
      exact Finset.image_nonempty.mp h
    have hrcycle : (∑ i ∈ r, boundary (Finsupp.single (σ i) 1)) = 0 := by
      rw [← Finset.sum_image (f := fun a : Finset V => boundary (Finsupp.single a 1))
        (hinj.mono hrs), hri]
      exact htz
    have hre := hs.minimal r hrs hrne hrcycle
    simpa only [hre] using hri.symm

/-- Homogeneity survives passage to the ordinary image family. -/
theorem Pure.image {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hs : Pure n σ s) : Pure n id (s.image σ) := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
  exact hs i hi

@[simp]
theorem vertices_image (σ : I → Finset V) (s : Finset I) :
    vertices id (s.image σ) = vertices σ s := by
  ext v
  simp only [mem_vertices, Finset.mem_image, id_eq]
  aesop

@[simp]
theorem oneSkeleton_image (σ : I → Finset V) (s : Finset I) :
    oneSkeleton id (s.image σ) = oneSkeleton σ s := by
  ext v w
  simp only [oneSkeleton_adj, Finset.mem_image, id_eq]
  aesop

/-- The one-skeleton depends on the facet vertex sets, not on their
injective labelling. In fact multiplicities do not affect this graph. -/
noncomputable def supportGraphImageIso (σ : I → Finset V) (s : Finset I) :
    supportGraph σ s ≃g supportGraph id (s.image σ) where
  toEquiv := Finset.equivOfEq (vertices_image σ s).symm
  map_rel_iff' := by
    intro a b
    change (oneSkeleton id (s.image σ)).Adj a.val b.val ↔
      (oneSkeleton σ s).Adj a.val b.val
    rw [oneSkeleton_image]

/-- A two-copy facet family has a complete support graph. -/
theorem supportGraph_pair_eq_top {σ : I → Finset V} {i j : I}
    (hσ : σ i = σ j) : supportGraph σ {i, j} = ⊤ := by
  ext a b
  change ((a.val ≠ b.val) ∧ ∃ k ∈ ({i, j} : Finset I),
    a.val ∈ σ k ∧ b.val ∈ σ k) ↔ a ≠ b
  have ha : a.val ∈ σ i := by
    have h := a.property
    simpa [vertices, hσ] using h
  have hb : b.val ∈ σ i := by
    have h := b.property
    simpa [vertices, hσ] using h
  constructor
  · intro h hab
    exact h.1 (congrArg Subtype.val hab)
  · intro h
    exact ⟨fun hab => h (Subtype.ext hab), i, by simp, ha, hb⟩

/-- Duplicate minimal circuits provide the dimension-sized complete
rigidity base. -/
theorem genericallyRigid_pair {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {σ : I → Finset V} {s : Finset I}
    (hpure : Pure n σ s) {i j : I} (hi : i ∈ s)
    (hσ : σ i = σ j) (hs : s = {i, j}) (hdim : finrank ℝ E = n) :
    GenericallyRigid (supportGraph σ s) E := by
  subst s
  rw [supportGraph_pair_eq_top hσ]
  apply genericallyRigid_complete_of_card_eq_dim
  have hv : vertices σ {i, j} = σ i := by simp [vertices, hσ]
  simpa only [Fintype.card_coe, hv, hdim] using hpure i hi

end Cubical.Simplicial
