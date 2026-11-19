module

public import Unimodular.CycleDegree
public import Unimodular.ConvexGenericPaths
public import Mathlib.Analysis.Convex.Topology

@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set

namespace Unimodular.CycleDegree.FullCones

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (S : FullCones I V)

def ProperFace := {F : PointedCone ℝ V // S.IsFace F ∧
  Submodule.span ℝ (F : Set V) ≠ ⊤}

noncomputable instance : Fintype S.ProperFace :=
  (S.finite_faces.subset (show
    {F : PointedCone ℝ V | S.IsFace F ∧ Submodule.span ℝ (F : Set V) ≠ ⊤} ⊆
    {F | S.IsFace F} from fun _ h => h.1)).fintype

def Generic (x : V) : Prop := ∀ F : S.ProperFace, x ∉ Submodule.span ℝ (F.1 : Set V)

theorem generic_dense : Dense {x | S.Generic x} :=
  FiniteSubspacePaths.dense_complement
    (fun F : S.ProperFace => Submodule.span ℝ (F.1 : Set V)) (fun F => F.2.2)

theorem generic_regular {x : V} (hx : S.Generic x) : S.Regular x := by
  intro F
  apply hx ⟨F.1, F.2.1, ?_⟩
  intro he
  have hd := F.2.2
  rw [he, finrank_top] at hd
  omega

theorem generic_interior {x : V} (hx : S.Generic x) (i : I) (hxi : x ∈ S.cone i) :
    x ∈ interior (S.cone i : Set V) := by
  by_contra hn
  have hF := MinimalFaces.dominatedCone_isFaceOf (S.cone i) x
  have hne : MinimalFaces.dominatedCone (S.cone i) x ≠ S.cone i := by
    intro he
    exact hn ((ConeInterior.mem_interior_iff_dominatedCone_eq
      ⟨S.center i, S.center_mem_interior i⟩ hxi).2 he)
  exact hx ⟨_, ⟨⟨i, hF⟩, ConeInterior.span_ne_top_of_proper_face hF hne⟩⟩
    (Submodule.subset_span (MinimalFaces.self_mem_dominatedCone hxi))

theorem regular_dense : Dense {x | S.Regular x} :=
  S.generic_dense.mono (fun _ hx => S.generic_regular hx)

noncomputable def multiplicity (c : I → ℤ) (x : V) : ℤ :=
  ∑ i, if x ∈ interior (S.cone i : Set V) then c i else 0

theorem weightedDegree_eq_two_mul {x : V} (hx : S.Generic x) (c : I → ℤ) :
    S.weightedDegree c x = 2 * S.multiplicity c x := by
  unfold weightedDegree multiplicity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ interior (S.cone i : Set V)
  · rw [if_pos hi, FacetLine.weight_of_interior hi]; ring
  · have hn : x ∉ S.cone i := fun hm => hi (S.generic_interior hx i hm)
    rw [if_neg hi, FacetLine.weight_of_outside hn]; ring

/-- All generic-direction degree rows agree on the integer kernel of the actual
facet matrix, including arbitrary signed coefficients. -/
theorem multiplicity_eq (c : I → ℤ) (hc : S.IsCycle c)
    {x y : V} (hx : S.Generic x) (hy : S.Generic y) :
    S.multiplicity c x = S.multiplicity c y := by
  have he := S.weightedDegree_eq c hc (S.generic_regular hx) (S.generic_regular hy)
  rw [S.weightedDegree_eq_two_mul hx c, S.weightedDegree_eq_two_mul hy c] at he
  omega

theorem weight_nonneg (i : I) (x : V) : 0 ≤ FacetLine.weight (S.cone i) x := by
  unfold FacetLine.weight
  split_ifs <;> norm_num

theorem term_le_weightedDegree (c : I → ℤ) (hc : ∀ i, 0 ≤ c i) (i : I) (x : V) :
    c i * FacetLine.weight (S.cone i) x ≤ S.weightedDegree c x := by
  exact Finset.single_le_sum (fun j _ => mul_nonneg (hc j) (S.weight_nonneg j x))
    (Finset.mem_univ i)

/-- The closed union of cones with positive coefficient. -/
def Selected (c : I → ℤ) : Set V := {x | ∃ i, 0 < c i ∧ x ∈ S.cone i}

theorem selected_isClosed (c : I → ℤ) : IsClosed (S.Selected c) := by
  have he : S.Selected c = ⋃ i : {i : I // 0 < c i}, (S.cone i.1 : Set V) := by
    ext x
    simp [Selected]
  rw [he]
  exact isClosed_iUnion_of_finite (fun i => ConeInterior.isClosed_of_fg (S.fg i.1))

theorem mem_selected_of_weightedDegree_pos (c : I → ℤ) (hc : ∀ i, 0 ≤ c i)
    {x : V} (hx : 0 < S.weightedDegree c x) : x ∈ S.Selected c := by
  by_contra hn
  have hzero : S.weightedDegree c x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : 0 < c i
    · have hxi : x ∉ S.cone i := fun hm => hn ⟨i, hi, hm⟩
      rw [FacetLine.weight_of_outside hxi, mul_zero]
    · have hi0 : c i = 0 := by have := hc i; omega
      rw [hi0, zero_mul]
  omega

theorem weightedDegree_eq_on_open_convex (c : I → ℤ)
    {U : Set V} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hc : ∀ x ∈ U, ∀ F : S.Facet, Active F.1 x → ∑ i, c i * S.boundary F i = 0)
    {x y : V} (hxU : x ∈ U) (hyU : y ∈ U) (hx : S.Regular x) (hy : S.Regular y) :
    S.weightedDegree c x = S.weightedDegree c y := by
  exact ConvexGenericPaths.eq_of_eventually_line
    (fun F : S.SmallFace => Submodule.span ℝ (F.1 : Set V)) (fun F => F.2.2)
    hU hconv (S.weightedDegree c)
    (fun z hz hr v => S.eventually_weightedDegree_eq_of_active_rows c (hc z hz) hr v)
    hxU hyU hx hy

/-- Positive degree at one regular point forces an entire convex open region to be covered
when every active facet row cancels throughout that region. -/
theorem open_subset_selected_of_local_cycle (c : I → ℤ) (hc0 : ∀ i, 0 ≤ c i)
    {U : Set V} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hc : ∀ x ∈ U, ∀ F : S.Facet, Active F.1 x → ∑ i, c i * S.boundary F i = 0)
    {y : V} (hyU : y ∈ U) (hy : S.Regular y) (hypos : 0 < S.weightedDegree c y) :
    U ⊆ S.Selected c := by
  have hreg : U ∩ {x | S.Regular x} ⊆ S.Selected c := by
    rintro x ⟨hxU, hx⟩
    apply S.mem_selected_of_weightedDegree_pos c hc0
    rw [S.weightedDegree_eq_on_open_convex c hU hconv hc hxU hyU hx hy]
    exact hypos
  have hsub : U ⊆ closure (U ∩ {x | S.Regular x}) :=
    S.regular_dense.open_subset_closure_inter hU
  exact hsub.trans ((closure_mono hreg).trans (S.selected_isClosed c).closure_subset)

theorem cone_subset_closure_interior (i : I) :
    (S.cone i : Set V) ⊆ closure (interior (S.cone i : Set V)) := by
  have he := (S.cone i : ConvexCone ℝ V).convex.closure_interior_eq_closure_of_nonempty_interior
    (show (interior (S.cone i : Set V)).Nonempty from ⟨S.center i, S.center_mem_interior i⟩)
  change closure (interior (S.cone i : Set V)) = closure (S.cone i : Set V) at he
  rw [he]
  exact subset_closure

end Unimodular.CycleDegree.FullCones
