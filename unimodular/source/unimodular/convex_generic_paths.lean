module

public import Unimodular.FiniteSubspacePaths

@[expose] public section

open scoped Pointwise Topology
open Filter Set

namespace Unimodular.ConvexGenericPaths

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Two generic points inside a convex open set admit a two-segment generic join
which remains in that same set. -/
theorem exists_polygonal_join {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V)
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ Module.finrank ℝ V)
    {U : Set V} (hU : IsOpen U) (hconv : Convex ℝ U)
    {x y : V} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : ∀ i, x ∉ L i) (hy : ∀ i, y ∉ L i) :
    ∃ z : V,
      segment ℝ x z ⊆ {q | q ∈ U ∧ ∀ i, q ∉ L i} ∧
      segment ℝ y z ⊆ {q | q ∈ U ∧ ∀ i, q ∉ L i} := by
  let P : ι × Bool → Submodule ℝ V :=
    fun a => L a.1 ⊔ ℝ ∙ (if a.2 then x else y)
  have hproper : ∀ a, P a ≠ ⊤ :=
    fun a => FiniteSubspacePaths.sup_line_ne_top (L a.1) (hcodim a.1) _
  obtain ⟨z, hzU, hz⟩ :=
    (FiniteSubspacePaths.dense_complement P hproper).inter_open_nonempty U hU ⟨x, hxU⟩
  refine ⟨z, ?_, ?_⟩
  · intro q hq
    refine ⟨hconv.segment_subset hxU hzU hq, ?_⟩
    intro i
    exact FiniteSubspacePaths.segment_avoids (L i) (hx i)
      (by simpa [P] using hz (i, true)) hq
  · intro q hq
    refine ⟨hconv.segment_subset hyU hzU hq, ?_⟩
    intro i
    exact FiniteSubspacePaths.segment_avoids (L i) (hy i)
      (by simpa [P] using hz (i, false)) hq

/-- Line-local constancy on a convex open set away from codimension two implies constancy
on its full regular locus. -/
theorem eq_of_eventually_line {ι α : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V)
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ Module.finrank ℝ V)
    {U : Set V} (hU : IsOpen U) (hconv : Convex ℝ U) (f : V → α)
    (hloc : ∀ x ∈ U, (∀ i, x ∉ L i) → ∀ v : V,
      ∀ᶠ t : ℝ in 𝓝 0, f (x + t • v) = f x)
    {x y : V} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : ∀ i, x ∉ L i) (hy : ∀ i, y ∉ L i) : f x = f y := by
  obtain ⟨z, hxz, hyz⟩ := exists_polygonal_join L hcodim hU hconv hxU hyU hx hy
  have hl : ∀ q ∈ {q | q ∈ U ∧ ∀ i, q ∉ L i}, ∀ v : V,
      ∀ᶠ t : ℝ in 𝓝 0, f (q + t • v) = f q := fun q hq => hloc q hq.1 hq.2
  exact (FiniteSubspacePaths.eq_of_segment_of_eventually_line f _ hl hxz).trans
    (FiniteSubspacePaths.eq_of_segment_of_eventually_line f _ hl hyz).symm

end Unimodular.ConvexGenericPaths
