import CommAlg.Simplicial.Homology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Explicit contraction and the one-dimensional boundary-simplex class -/
noncomputable section
set_option maxHeartbeats 800000
namespace Characterizations.Strands
open Classical Finset CommAlg.Simplicial CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V]

section Ring
variable [CommRing k]

lemma creation_mem_degree {K : Finset V → Prop} (e : V) (i : ℕ)
    (h : ∀ s, K s → s.card = i → e ∉ s → K (insert e s))
    {z : Ambient V k} (hz : z ∈ Chains K i) : creation e z ∈ Chains K (i+1) := by
  induction hz using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, ⟨hs, hc⟩, rfl⟩ := ha
    rw [creation_basis]
    split_ifs with he
    · exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (basis_mem (h s hs hc he) (by simp [he, hc]))
  | zero => simpa using (Submodule.zero_mem (Chains (k := k) K (i+1)))
  | add a b ha hb iha ihb => simpa [mul_add] using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

lemma exactIn_of_degree_extension {K : Finset V → Prop} (e : V) (i : ℕ)
    (h : ∀ s, K s → s.card = i → e ∉ s → K (insert e s)) :
    ExactIn (k := k) K i := by
  intro z hz hc
  exact ⟨creation e z, creation_mem_degree e i h hz, by
    simp only [boundary_creation, hc, map_zero, sub_zero]⟩

def simplexBoundary (T : Finset V) (s : Finset V) : Prop := s ⊂ T

lemma simplexBoundary_downward (T : Finset V) : Downward (simplexBoundary T) := by
  intro s t hts hs
  exact Finset.ssubset_of_subset_of_ssubset hts hs

lemma boundary_basis_mem (T : Finset V) (i : ℕ) (hcard : T.card = i+1) :
    boundary (basis (k := k) T) ∈ Chains (simplexBoundary T) i := by
  rw [boundary_eq_sum]
  apply Submodule.sum_mem
  intro e he
  rw [contraction_basis]
  split_ifs with heT
  · apply Submodule.smul_mem
    exact basis_mem (Finset.erase_ssubset heT)
      (by simpa [hcard] using Finset.card_erase_of_mem heT)
  · exact Submodule.zero_mem _

lemma boundary_basis_ne_zero [Nontrivial k] {T : Finset V} (hT : T.Nonempty) :
    boundary (basis (k := k) T) ≠ 0 := by
  obtain ⟨e, he⟩ := hT
  intro hzero
  have h := boundary_creation e (basis (k := k) T)
  rw [creation_basis, if_pos he, map_zero, hzero, map_zero, sub_zero] at h
  exact Module.Basis.ne_zero basis T h.symm

lemma simplexBoundary_nonzero [Nontrivial k] (T : Finset V) (i : ℕ)
    (hcard : T.card = i+1) : NonzeroHomology (k := k) (simplexBoundary T) i := by
  refine ⟨boundary (basis T), boundary_basis_mem T i hcard, boundary_boundary _, ?_⟩
  intro y hy he
  have hbot : Chains (k := k) (simplexBoundary T) (i+1) = ⊥ :=
    chains_eq_bot_of_no_face (fun s hs hc => by
      have hlt := Finset.card_lt_card hs
      omega)
  rw [hbot, Submodule.mem_bot] at hy
  subst y
  exact boundary_basis_ne_zero (k := k) (T := T)
    (Finset.card_pos.mp (by omega)) (by simpa using he.symm)

lemma simplex_top_chains (T : Finset V) :
    Chains (k := k) (fun s => s ⊆ T) T.card = Submodule.span k {basis T} := by
  apply le_antisymm
  · rw [Chains, Submodule.span_le]
    rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
    have he : s = T := Finset.eq_of_subset_of_card_le hs hc.ge
    subst s
    exact Submodule.subset_span (Set.mem_singleton _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact basis_mem (Finset.Subset.refl T) rfl

lemma simplexBoundary_cycle_span (T : Finset V) (i : ℕ) (hcard : T.card = i+1)
    {z : Ambient V k} (hz : z ∈ Chains (simplexBoundary T) i) (hc : boundary z = 0) :
    z ∈ Submodule.span k {boundary (basis T)} := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hz' : z ∈ Chains (fun s => s ⊆ T) i :=
    chains_mono (fun s hs => hs.subset) _ hz
  have hy := creation_mem_of_cone (k := k) e
    (K := fun s => s ⊆ T) (fun s hs => Finset.insert_subset he hs) hz'
  rw [← hcard, simplex_top_chains] at hy
  obtain ⟨c, hcy⟩ := Submodule.mem_span_singleton.mp hy
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  have hh := congrArg boundary hcy
  simpa only [map_smul, boundary_creation, hc, map_zero, sub_zero] using hh

end Ring

lemma homology_finrank_eq_one [Field k] {K : Finset V → Prop} (hK : Downward K)
    (i : ℕ) (v : Ambient V k) (hv : v ≠ 0)
    (hspan : ∀ z : Ambient V k, z ∈ Chains K i → boundary z = 0 →
      z ∈ Submodule.span k {v}) (hnonzero : NonzeroHomology (k := k) K i) :
    Module.finrank k ((chainComplex (k := k) hK).homology i) = 1 := by
  let C := chainComplex (k := k) hK
  let f₀ : C.cycles i →ₗ[k] Ambient V k :=
    (Chains (k := k) K i).subtype.comp (C.iCycles i).hom
  have hfmem (z : C.cycles i) : f₀ z ∈ Submodule.span k {v} := by
    apply hspan _ ((C.iCycles i z).property)
    cases i with
    | zero => exact boundary_zero_degree_zero (C.iCycles 0 z).property
    | succ j =>
      have h : (C.d (j+1) j).hom ((C.iCycles (j+1)).hom z) = 0 :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (C.iCycles_d (j+1) j)) z
      rw [show C.d (j+1) j = ModuleCat.ofHom (chainDifferential hK j) from
        chainComplex_d hK j] at h
      change (chainDifferential hK j) ((C.iCycles (j+1)).hom z) = 0 at h
      exact congrArg (fun q : Chains (k := k) K j => q.val) h
  let f : C.cycles i →ₗ[k] Submodule.span k {v} := f₀.codRestrict _ hfmem
  have hfi : Function.Injective f := by
    intro x y he
    apply (ModuleCat.mono_iff_injective (C.iCycles i)).mp inferInstance
    have he' : f₀ x = f₀ y := congrArg (fun z : Submodule.span k {v} => z.val) he
    exact Subtype.ext he'
  letI : FiniteDimensional k (C.cycles i) := FiniteDimensional.of_injective f hfi
  have hs : Function.Surjective (C.homologyπ i).hom :=
    (ModuleCat.epi_iff_surjective (C.homologyπ i)).mp inferInstance
  letI : FiniteDimensional k (C.homology i) :=
    FiniteDimensional.of_surjective (C.homologyπ i).hom hs
  have hle : Module.finrank k (C.homology i) ≤ 1 := by
    calc
      _ ≤ Module.finrank k (C.cycles i) := LinearMap.finrank_le_finrank_of_surjective hs
      _ ≤ Module.finrank k (Submodule.span k {v}) := LinearMap.finrank_le_finrank_of_injective hfi
      _ = 1 := finrank_span_singleton hv
  have hn : ¬ Subsingleton (C.homology i) := by
    intro hn
    have hz := (ModuleCat.isZero_iff_subsingleton (M := C.homology i)).mpr hn
    exact ((homology_nonzero_iff hK i).mpr hnonzero) hz
  have hne : Module.finrank k (C.homology i) ≠ 0 :=
    fun h => hn ((Module.finrank_zero_iff (R := k) (M := C.homology i)).mp h)
  change Module.finrank k (C.homology i) = 1
  omega

lemma simplexBoundary_homology_finrank [Field k] (T : Finset V) (i : ℕ)
    (hcard : T.card = i+1) :
    Module.finrank k ((chainComplex (k := k) (simplexBoundary_downward T)).homology i) = 1 :=
  homology_finrank_eq_one (simplexBoundary_downward T) i (boundary (basis T))
    (boundary_basis_ne_zero (k := k) (T := T) (Finset.card_pos.mp (by omega)))
    (fun _ hz hc => simplexBoundary_cycle_span T i hcard hz hc)
    (simplexBoundary_nonzero T i hcard)

end Characterizations.Strands
