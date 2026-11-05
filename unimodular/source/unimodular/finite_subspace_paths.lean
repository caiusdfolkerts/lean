module

public import Unimodular.FacetLine
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open scoped Pointwise Topology
open Filter Set

namespace Unimodular.FiniteSubspacePaths

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Adjoining one line to a subspace of codimension at least two still leaves
an actual proper real subspace. -/
theorem sup_line_ne_top (L : Submodule ℝ V)
    (hcodim : Module.finrank ℝ L + 2 ≤ Module.finrank ℝ V) (x : V) :
    L ⊔ ℝ ∙ x ≠ ⊤ := by
  have hline : Module.finrank ℝ (ℝ ∙ x) ≤ 1 := by
    by_cases hx : x = 0
    · subst x
      rw [Submodule.span_zero_singleton, finrank_bot]
      omega
    · exact (finrank_span_singleton hx).le
  have hsup := Submodule.finrank_add_le_finrank_add_finrank L (ℝ ∙ x)
  intro he
  rw [he, finrank_top] at hsup
  omega

/-- Finitely many proper real subspaces cannot cover any nonempty open set.
This follows from their actual topological interiors and closedness. -/
theorem dense_complement {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V) (hproper : ∀ i, L i ≠ ⊤) :
    Dense {x : V | ∀ i, x ∉ L i} := by
  let f : ι → Set V := fun i => (L i : Set V)ᶜ
  have hopen : ∀ i, IsOpen (f i) := fun i => (L i).closed_of_finiteDimensional.isOpen_compl
  have hdense : ∀ i, Dense (f i) := by
    intro i
    rw [← interior_eq_empty_iff_dense_compl]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hproper i ((L i).eq_top_of_nonempty_interior' ⟨x, hx⟩)
  have h := (Set.finite_range f).dense_sInter
    (by rintro t ⟨i, rfl⟩; exact hopen i)
    (by rintro t ⟨i, rfl⟩; exact hdense i)
  convert h using 1
  ext x
  simp [f]

/-- A segment from x to z avoids L when x avoids L and z avoids L plus the line
through x. No general-position or path condition is assumed without proof. -/
theorem segment_avoids (L : Submodule ℝ V)
    {x z : V} (hx : x ∉ L) (hz : z ∉ L ⊔ ℝ ∙ x) :
    segment ℝ x z ⊆ (L : Set V)ᶜ := by
  rintro q ⟨a, b, ha, hb, hab, rfl⟩ hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    apply hx
    simpa [hb0, ha1] using hq
  · let P := L ⊔ ℝ ∙ x
    have hxP : x ∈ P := (show ℝ ∙ x ≤ P from le_sup_right)
      (Submodule.subset_span (by simp))
    have habP : a • x + b • z ∈ P := (show L ≤ P from le_sup_left) hq
    have hbz : b • z ∈ P := by
      have h := P.sub_mem habP (P.smul_mem a hxP)
      simpa only [add_sub_cancel_left] using h
    apply hz
    have h := P.smul_mem b⁻¹ hbz
    simpa only [smul_smul, inv_mul_cancel₀ hb0, one_smul] using h

/-- Two points outside finitely many codimension-two subspaces can be joined
by two straight segments lying entirely outside those subspaces. -/
theorem exists_polygonal_join {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V)
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ Module.finrank ℝ V)
    {x y : V} (hx : ∀ i, x ∉ L i) (hy : ∀ i, y ∉ L i) :
    ∃ z : V,
      segment ℝ x z ⊆ {q | ∀ i, q ∉ L i} ∧
      segment ℝ y z ⊆ {q | ∀ i, q ∉ L i} := by
  let P : ι × Bool → Submodule ℝ V :=
    fun a => L a.1 ⊔ ℝ ∙ (if a.2 then x else y)
  have hproper : ∀ a, P a ≠ ⊤ := fun a => sup_line_ne_top (L a.1) (hcodim a.1) _
  obtain ⟨z, hz⟩ := (dense_complement P hproper).nonempty
  refine ⟨z, ?_, ?_⟩
  · intro q hq i
    exact segment_avoids (L i) (hx i) (by simpa [P] using hz (i, true)) hq
  · intro q hq i
    exact segment_avoids (L i) (hy i) (by simpa [P] using hz (i, false)) hq

/-- The actual real complement of finitely many subspaces of codimension at
least two is path connected, in every dimension where the hypotheses make sense. -/
theorem complement_pathConnected {ι : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V)
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ Module.finrank ℝ V) :
    IsPathConnected {x : V | ∀ i, x ∉ L i} := by
  have hproper : ∀ i, L i ≠ ⊤ := by
    intro i he
    apply sup_line_ne_top (L i) (hcodim i) 0
    simp [he]
  obtain ⟨x, hx⟩ := (dense_complement L hproper).nonempty
  refine ⟨x, hx, ?_⟩
  intro y hy
  obtain ⟨z, hxz, hyz⟩ := exists_polygonal_join L hcodim hx hy
  exact (JoinedIn.of_segment_subset hxz).trans (JoinedIn.of_segment_subset hyz).symm


/-- A function which is constant near every point along every line is constant along any
segment in its domain. Only one-dimensional connectedness is used. -/
theorem eq_of_segment_of_eventually_line {α : Type*} (f : V → α) (S : Set V)
    (hloc : ∀ x ∈ S, ∀ v : V, ∀ᶠ t : ℝ in 𝓝 0, f (x + t • v) = f x)
    {x y : V} (hseg : segment ℝ x y ⊆ S) : f x = f y := by
  let g : Set.Icc (0 : ℝ) 1 → α := fun t => f (x + (t : ℝ) • (y - x))
  have hg : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).2
    intro t
    have hpoint : x + (t : ℝ) • (y - x) ∈ S := by
      apply hseg
      refine ⟨1 - (t : ℝ), t, sub_nonneg.2 t.2.2, t.2.1, by ring, ?_⟩
      module
    have he := hloc _ hpoint (y - x)
    have hc : Continuous (fun s : Set.Icc (0 : ℝ) 1 => (s : ℝ) - t) :=
      continuous_subtype_val.sub continuous_const
    have ht : Tendsto (fun s : Set.Icc (0 : ℝ) 1 => (s : ℝ) - t) (𝓝 t) (𝓝 0) := by
      simpa using hc.tendsto t
    filter_upwards [ht.eventually he] with s hs
    convert hs using 1 <;> dsimp [g] <;> congr 1 <;> module
  letI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have he := hg.apply_eq_of_preconnectedSpace ⟨0, by simp⟩ ⟨1, by simp⟩
  simpa [g] using he

/-- The same line-local constancy gives equality on the entire complement of finitely
many subspaces of codimension at least two. -/
theorem eq_of_eventually_line {ι α : Type*} [Fintype ι]
    (L : ι → Submodule ℝ V)
    (hcodim : ∀ i, Module.finrank ℝ (L i) + 2 ≤ Module.finrank ℝ V)
    (f : V → α)
    (hloc : ∀ x, (∀ i, x ∉ L i) → ∀ v : V,
      ∀ᶠ t : ℝ in 𝓝 0, f (x + t • v) = f x)
    {x y : V} (hx : ∀ i, x ∉ L i) (hy : ∀ i, y ∉ L i) : f x = f y := by
  obtain ⟨z, hxz, hyz⟩ := exists_polygonal_join L hcodim hx hy
  have hxz' := eq_of_segment_of_eventually_line f {q | ∀ i, q ∉ L i} hloc hxz
  have hyz' := eq_of_segment_of_eventually_line f {q | ∀ i, q ∉ L i} hloc hyz
  exact hxz'.trans hyz'.symm

end Unimodular.FiniteSubspacePaths
