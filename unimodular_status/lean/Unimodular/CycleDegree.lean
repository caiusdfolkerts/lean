module

public import Unimodular.FiniteSubspacePaths
public import TauCeti.Geometry.Convex.Cone.Face.Finite

@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set

namespace Unimodular.CycleDegree

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A finite indexed family of actual full-dimensional polyhedral cones. Repeated cones
are permitted, which is necessary when taking quotient stars. -/
structure FullCones (I V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  cone : I → PointedCone ℝ V
  fg : ∀ i, (cone i).FG
  full : ∀ i, Submodule.span ℝ (cone i : Set V) = ⊤

namespace FullCones

variable (S : FullCones I V)

def IsFace (F : PointedCone ℝ V) : Prop := ∃ i, F.IsFaceOf (S.cone i)

theorem finite_faces : {F | S.IsFace F}.Finite := by
  letI : ∀ i, Finite (S.cone i).Face := fun i => PointedCone.FG.finite_face (S.fg i)
  have hf := Set.finite_range (fun p : Σ i, (S.cone i).Face => p.2.toPointedCone)
  apply hf.subset
  rintro F ⟨i, hF⟩
  exact ⟨⟨i, ⟨F, hF⟩⟩, rfl⟩

def Facet := {F : PointedCone ℝ V // S.IsFace F ∧
  Module.finrank ℝ (Submodule.span ℝ (F : Set V)) + 1 = Module.finrank ℝ V}

def SmallFace := {F : PointedCone ℝ V // S.IsFace F ∧
  Module.finrank ℝ (Submodule.span ℝ (F : Set V)) + 2 ≤ Module.finrank ℝ V}

noncomputable instance : Fintype S.Facet := by
  exact (S.finite_faces.subset (show
    {F : PointedCone ℝ V | S.IsFace F ∧
      Module.finrank ℝ (Submodule.span ℝ (F : Set V)) + 1 = Module.finrank ℝ V} ⊆
    {F | S.IsFace F} from fun _ h => h.1)).fintype

noncomputable instance : Fintype S.SmallFace := by
  exact (S.finite_faces.subset (show
    {F : PointedCone ℝ V | S.IsFace F ∧
      Module.finrank ℝ (Submodule.span ℝ (F : Set V)) + 2 ≤ Module.finrank ℝ V} ⊆
    {F | S.IsFace F} from fun _ h => h.1)).fintype

noncomputable def center (i : I) : V :=
  (ConeInterior.interior_nonempty_of_span_eq_top (S.full i)).choose

theorem center_mem_interior (i : I) : S.center i ∈ interior (S.cone i : Set V) :=
  (ConeInterior.interior_nonempty_of_span_eq_top (S.full i)).choose_spec

noncomputable def normal (F : S.Facet) : V →ₗ[ℝ] ℝ :=
  (ConeInterior.exists_normal (Submodule.span ℝ (F.1 : Set V)) F.2.2).choose

theorem normal_ne_zero (F : S.Facet) : S.normal F ≠ 0 :=
  (ConeInterior.exists_normal (Submodule.span ℝ (F.1 : Set V)) F.2.2).choose_spec.1

theorem normal_ker (F : S.Facet) :
    LinearMap.ker (S.normal F) = Submodule.span ℝ (F.1 : Set V) :=
  (ConeInterior.exists_normal (Submodule.span ℝ (F.1 : Set V)) F.2.2).choose_spec.2

theorem facet_ne_cone (F : S.Facet) (i : I) : F.1 ≠ S.cone i := by
  intro he
  have hd := F.2.2
  rw [he, S.full i, finrank_top] at hd
  omega

/-- The actual oriented facet boundary matrix, with its sign read from an interior point. -/
noncomputable def boundary (F : S.Facet) (i : I) : ℤ := by
  classical
  exact if F.1.IsFaceOf (S.cone i) then FacetLine.signZ (S.normal F (S.center i)) else 0

/-- Points outside every face span of codimension at least two. -/
def Regular (x : V) : Prop := ∀ F : S.SmallFace, x ∉ Submodule.span ℝ (F.1 : Set V)

/-- A facet is active at `x` when `x` lies in its relative interior, expressed by its
actual smallest face. This is not a supplied combinatorial incidence relation. -/
def Active (F : PointedCone ℝ V) (x : V) : Prop :=
  x ∈ F ∧ MinimalFaces.dominatedCone F x = F

theorem active_iff {F : PointedCone ℝ V} {i : I} (hF : F.IsFaceOf (S.cone i))
    {x : V} : Active F x ↔ x ∈ S.cone i ∧ MinimalFaces.dominatedCone (S.cone i) x = F := by
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hF.le hx, (MinimalFaces.dominatedCone_eq_of_face hF hx).symm.trans he⟩
  · rintro ⟨hx, he⟩
    have hxF : x ∈ F := he ▸ MinimalFaces.self_mem_dominatedCone hx
    exact ⟨hxF, (MinimalFaces.dominatedCone_eq_of_face hF hxF).trans he⟩

theorem minimal_is_facet {x : V} (hx : S.Regular x) {i : I}
    (hxi : x ∈ S.cone i) (hni : x ∉ interior (S.cone i : Set V)) :
    S.IsFace (MinimalFaces.dominatedCone (S.cone i) x) ∧
      Module.finrank ℝ (Submodule.span ℝ
        (MinimalFaces.dominatedCone (S.cone i) x : Set V)) + 1 = Module.finrank ℝ V := by
  have hF := MinimalFaces.dominatedCone_isFaceOf (S.cone i) x
  have hne : MinimalFaces.dominatedCone (S.cone i) x ≠ S.cone i := by
    intro he
    exact hni ((ConeInterior.mem_interior_iff_dominatedCone_eq
      ⟨S.center i, S.center_mem_interior i⟩ hxi).2 he)
  have hr := ConeInterior.finrank_lt_of_proper_face hF hne
  have hnot : ¬ Module.finrank ℝ (Submodule.span ℝ
      (MinimalFaces.dominatedCone (S.cone i) x : Set V)) + 2 ≤ Module.finrank ℝ V := by
    intro hd
    exact hx ⟨_, ⟨⟨i, hF⟩, hd⟩⟩
      (Submodule.subset_span (MinimalFaces.self_mem_dominatedCone hxi))
  exact ⟨⟨i, hF⟩, by omega⟩

theorem active_boundary_zero_of_interior {x : V} {i : I}
    (hx : x ∈ interior (S.cone i : Set V)) (F : S.Facet) (hF : Active F.1 x) :
    S.boundary F i = 0 := by
  classical
  have hn : ¬ F.1.IsFaceOf (S.cone i) := by
    intro hface
    exact S.facet_ne_cone F i (ConeInterior.face_eq_of_mem_interior hface hF.1 hx)
  simp [boundary, hn]

theorem active_boundary_zero_of_outside {x : V} {i : I}
    (hx : x ∉ S.cone i) (F : S.Facet) (hF : Active F.1 x) :
    S.boundary F i = 0 := by
  classical
  have hn : ¬ F.1.IsFaceOf (S.cone i) := fun hface => hx (hface.le hF.1)
  simp [boundary, hn]

theorem eventually_weight_eq {x : V} (hx : S.Regular x) (i : I) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, FacetLine.weight (S.cone i) (x + t • v) =
      FacetLine.weight (S.cone i) x +
      ∑ F : S.Facet, if Active F.1 x then
        FacetLine.signZ (t * S.normal F v) * S.boundary F i else 0 := by
  classical
  by_cases hi : x ∈ interior (S.cone i : Set V)
  · filter_upwards [FacetLine.eventually_weight_of_interior hi v] with t ht
    rw [ht]
    have hs : (∑ F : S.Facet, if Active F.1 x then
        FacetLine.signZ (t * S.normal F v) * S.boundary F i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro F _
      split_ifs with hF
      · rw [S.active_boundary_zero_of_interior hi F hF, mul_zero]
      · rfl
    rw [hs, add_zero]
  by_cases hxi : x ∈ S.cone i
  · let F : S.Facet := ⟨_, S.minimal_is_facet hx hxi hi⟩
    have hface : F.1.IsFaceOf (S.cone i) := MinimalFaces.dominatedCone_isFaceOf _ _
    have hactive : Active F.1 x := (S.active_iff hface).2 ⟨hxi, rfl⟩
    have he := FacetLine.eventually_weight_at_facet hxi (S.facet_ne_cone F i)
      (S.normal F) (S.normal_ker F) (S.center_mem_interior i) v
    filter_upwards [he] with t ht
    rw [ht, FacetLine.weight_of_boundary hxi hi]
    congr 1
    have hs : (∑ G : S.Facet, if Active G.1 x then
        FacetLine.signZ (t * S.normal G v) * S.boundary G i else 0) =
        FacetLine.signZ (t * S.normal F v) * S.boundary F i := by
      rw [Finset.sum_eq_single F]
      · rw [if_pos hactive]
      · intro G _ hGF
        by_cases hact : Active G.1 x
        · rw [if_pos hact]
          have hn : ¬ G.1.IsFaceOf (S.cone i) := by
            intro hG
            have hm := ((S.active_iff hG).1 hact).2
            apply hGF
            exact Subtype.ext hm.symm
          simp [boundary, hn]
        · rw [if_neg hact]
      · simp
    rw [hs, boundary, if_pos hface]
  · filter_upwards [FacetLine.eventually_weight_of_outside (S.fg i) hxi v] with t ht
    rw [ht]
    have hs : (∑ F : S.Facet, if Active F.1 x then
        FacetLine.signZ (t * S.normal F v) * S.boundary F i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro F _
      split_ifs with hF
      · rw [S.active_boundary_zero_of_outside hxi F hF, mul_zero]
      · rfl
    rw [hs, add_zero]

noncomputable def weightedDegree (c : I → ℤ) (x : V) : ℤ :=
  ∑ i, c i * FacetLine.weight (S.cone i) x

/-- The signed boundary equation, with no positivity hypothesis. -/
def IsCycle (c : I → ℤ) : Prop := ∀ F : S.Facet, ∑ i, c i * S.boundary F i = 0

theorem eventually_weightedDegree_eq_of_active_rows (c : I → ℤ)
    {x : V} (hc : ∀ F : S.Facet, Active F.1 x → ∑ i, c i * S.boundary F i = 0)
    (hx : S.Regular x) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, S.weightedDegree c (x + t • v) = S.weightedDegree c x := by
  classical
  have he : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, FacetLine.weight (S.cone i) (x + t • v) =
      FacetLine.weight (S.cone i) x +
      ∑ F : S.Facet, if Active F.1 x then
        FacetLine.signZ (t * S.normal F v) * S.boundary F i else 0 :=
    Filter.eventually_all.2 (fun i => S.eventually_weight_eq hx i v)
  filter_upwards [he] with t ht
  unfold weightedDegree
  simp_rw [ht, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  suffices (∑ i, ∑ F : S.Facet, c i * (if Active F.1 x then
      FacetLine.signZ (t * S.normal F v) * S.boundary F i else 0)) = 0 by omega
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro F _
  by_cases hact : Active F.1 x
  · simp only [if_pos hact]
    calc
      ∑ i, c i * (FacetLine.signZ (t * S.normal F v) * S.boundary F i) =
          FacetLine.signZ (t * S.normal F v) * ∑ i, c i * S.boundary F i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [hc F hact, mul_zero]
  · simp [hact]

theorem eventually_weightedDegree_eq (c : I → ℤ) (hc : S.IsCycle c)
    {x : V} (hx : S.Regular x) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, S.weightedDegree c (x + t • v) = S.weightedDegree c x :=
  S.eventually_weightedDegree_eq_of_active_rows c (fun F _ => hc F) hx v

/-- The weighted degree of every integral geometric cycle is constant outside codimension
two face spans, including the regular portions of facet boundaries. -/
theorem weightedDegree_eq (c : I → ℤ) (hc : S.IsCycle c)
    {x y : V} (hx : S.Regular x) (hy : S.Regular y) :
    S.weightedDegree c x = S.weightedDegree c y := by
  exact FiniteSubspacePaths.eq_of_eventually_line
    (fun F : S.SmallFace => Submodule.span ℝ (F.1 : Set V))
    (fun F => F.2.2) (S.weightedDegree c)
    (fun _ h v => S.eventually_weightedDegree_eq c hc h v) hx hy

end FullCones

end Unimodular.CycleDegree
