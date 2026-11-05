module

public import Unimodular.CycleTopology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Connecting full cones across a common facet

A common codimension-one face is enough to connect the two cone interiors
inside the interior of their union. The proof derives a genuine local
halfspace description from relative interior in the span of the face.
It does not assume a fan, disjoint interiors, or a prescribed adjacency.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped Topology Pointwise
open Filter Set

namespace Unimodular.PrimitiveRegions

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A cone has an interior point when viewed in its actual linear span. -/
theorem relative_cone_interior_nonempty (F : PointedCone ℝ V) :
    (interior (F.comap (Submodule.span ℝ (F : Set V)).subtype :
      Set (Submodule.span ℝ (F : Set V)))).Nonempty := by
  let L := Submodule.span ℝ (F : Set V)
  have hsub : (F : Set V) ⊆ LinearMap.range L.subtype := by
    intro x hx
    exact ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩
  have hspan : Submodule.span ℝ (F.comap L.subtype : Set L) = ⊤ := by
    rw [PointedCone.coe_comap,
      Submodule.span_preimage_eq ⟨0, F.zero_mem⟩ hsub]
    apply top_unique
    intro x _
    exact x.property
  exact ConeInterior.interior_nonempty_of_span_eq_top hspan

/-- Near a relative interior point of a face, the halfspace pointing
towards an interior point lies in the cone. Strict inequality places it
in the actual interior. -/
theorem eventually_halfspace_mem
    {C F : PointedCone ℝ V} (hFC : F ≤ C)
    (f : V →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker f = Submodule.span ℝ (F : Set V))
    {x : Submodule.span ℝ (F : Set V)}
    (hx : x ∈ interior (F.comap (Submodule.span ℝ (F : Set V)).subtype :
      Set (Submodule.span ℝ (F : Set V))))
    {y : V} (hy : y ∈ interior (C : Set V)) (hfy : f y ≠ 0) :
    ∀ᶠ z in 𝓝 (x : V),
      (0 ≤ f z / f y → z ∈ C) ∧
      (0 < f z / f y → z ∈ interior (C : Set V)) := by
  let L := Submodule.span ℝ (F : Set V)
  have hp_mem (z : V) : z - (f z / f y) • y ∈ L := by
    change z - (f z / f y) • y ∈ Submodule.span ℝ (F : Set V)
    rw [← hker]
    change f (z - (f z / f y) • y) = 0
    simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfy, sub_self]
  let p : V → L := fun z => ⟨z - (f z / f y) • y, hp_mem z⟩
  have hp : Continuous p :=
    (continuous_id.sub
      ((f.continuous_of_finiteDimensional.div_const (f y)).smul continuous_const)).subtype_mk _
  have hfx : f (x : V) = 0 := by
    change (x : V) ∈ LinearMap.ker f
    rw [hker]
    exact x.property
  have hpx : p (x : V) = x := by
    apply Subtype.ext
    simp [p, hfx]
  have he : ∀ᶠ z in 𝓝 (x : V), p z ∈ F.comap L.subtype := by
    have ht : Tendsto p (𝓝 (x : V)) (𝓝 x) := by
      simpa only [hpx] using hp.tendsto (x : V)
    exact ht.eventually (mem_interior_iff_mem_nhds.1 hx)
  filter_upwards [he] with z hz
  have hbase : (p z : V) ∈ C := hFC hz
  have hre : z = (f z / f y) • y + (p z : V) := by
    dsimp [p]
    module
  constructor
  · intro h
    rw [hre]
    exact C.add_mem (PointedCone.smul_mem C h (interior_subset hy)) hbase
  · intro h
    rw [hre]
    exact ConeInterior.add_mem_interior (ConeInterior.smul_mem_interior hy h) hbase

variable {I : Type*} [Fintype I] (S : CycleDegree.FullCones I V)

/-- Two full cones sharing an actual facet have a preconnected bridge
containing both of their interiors and lying in the interior of their
union. Cones on the same side and cones on opposite sides are both
included. -/
theorem common_facet_bridge (F : S.Facet) {i j : I}
    (hi : F.1.IsFaceOf (S.cone i)) (hj : F.1.IsFaceOf (S.cone j)) :
    ∃ K : Set V, IsPreconnected K ∧
      interior (S.cone i : Set V) ⊆ K ∧
      interior (S.cone j : Set V) ⊆ K ∧
      K ⊆ interior ((S.cone i : Set V) ∪ (S.cone j : Set V)) := by
  obtain ⟨x, hx⟩ := relative_cone_interior_nonempty F.1
  let f := S.normal F
  let yi := S.center i
  let yj := S.center j
  have hfi : f yi ≠ 0 :=
    ConeInterior.normal_ne_zero_at_interior hi (S.facet_ne_cone F i) f
      (S.normal_ker F) (S.center_mem_interior i)
  have hfj : f yj ≠ 0 :=
    ConeInterior.normal_ne_zero_at_interior hj (S.facet_ne_cone F j) f
      (S.normal_ker F) (S.center_mem_interior j)
  have hei := eventually_halfspace_mem hi.le f (S.normal_ker F) hx
    (S.center_mem_interior i) hfi
  have hej := eventually_halfspace_mem hj.le f (S.normal_ker F) hx
    (S.center_mem_interior j) hfj
  have hxF : (x : V) ∈ F.1 := by
    change x ∈ F.1.comap (Submodule.span ℝ (F.1 : Set V)).subtype
    exact interior_subset hx
  have hfx : f (x : V) = 0 := by
    change (x : V) ∈ LinearMap.ker f
    rw [S.normal_ker F]
    exact x.property
  have hratio : f yi / f yj ≠ 0 := div_ne_zero hfi hfj
  have hiconn := (S.cone i : ConvexCone ℝ V).convex.interior.isPreconnected
  have hjconn := (S.cone j : ConvexCone ℝ V).convex.interior.isPreconnected
  rcases lt_or_gt_of_ne hratio with hneg | hpos
  · have hcover : ((S.cone i : Set V) ∪ (S.cone j : Set V)) ∈ 𝓝 (x : V) := by
      filter_upwards [hei, hej] with z hzi hzj
      by_cases hzi' : 0 ≤ f z / f yi
      · exact Or.inl (hzi.1 hzi')
      · apply Or.inr
        apply hzj.1
        have he : f z / f yj = (f z / f yi) * (f yi / f yj) := by
          field_simp
        rw [he]
        exact (mul_pos_of_neg_of_neg (lt_of_not_ge hzi') hneg).le
    have hxunion : (x : V) ∈ interior
        ((S.cone i : Set V) ∪ (S.cone j : Set V)) :=
      mem_interior_iff_mem_nhds.2 hcover
    let A := interior (S.cone i : Set V) ∪ {(x : V)}
    let B := interior (S.cone j : Set V) ∪ {(x : V)}
    have hA : IsPreconnected A := by
      apply hiconn.subset_closure subset_union_left
      rintro z (hz | hz)
      · exact subset_closure hz
      · have hz' : z = (x : V) := hz
        subst z
        exact S.cone_subset_closure_interior i (hi.le hxF)
    have hB : IsPreconnected B := by
      apply hjconn.subset_closure subset_union_left
      rintro z (hz | hz)
      · exact subset_closure hz
      · have hz' : z = (x : V) := hz
        subst z
        exact S.cone_subset_closure_interior j (hj.le hxF)
    refine ⟨A ∪ B,
      hA.union (x : V) (Or.inr rfl) (Or.inr rfl) hB,
      fun _ h => Or.inl (Or.inl h), fun _ h => Or.inr (Or.inl h), ?_⟩
    rintro z ((hz | hz) | (hz | hz))
    · exact interior_mono subset_union_left hz
    · simpa only [Set.mem_singleton_iff.mp hz] using hxunion
    · exact interior_mono subset_union_right hz
    · simpa only [Set.mem_singleton_iff.mp hz] using hxunion
  · have ht : Tendsto (fun t : ℝ => (x : V) + t • yi) (𝓝 0) (𝓝 (x : V)) := by
      have hc : Continuous (fun t : ℝ => (x : V) + t • yi) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    have he : ∀ᶠ t : ℝ in 𝓝[>] 0,
        (0 < f ((x : V) + t • yi) / f yj →
          (x : V) + t • yi ∈ interior (S.cone j : Set V)) :=
      (ht.eventually hej).mono (fun _ h => h.2) |>.filter_mono nhdsWithin_le_nhds
    have htpos_event : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t, htpos, htj⟩ := (htpos_event.and he).exists
    have hti : (x : V) + t • yi ∈ interior (S.cone i : Set V) := by
      simpa only [add_comm] using
        ConeInterior.add_mem_interior
          (ConeInterior.smul_mem_interior (S.center_mem_interior i) htpos)
          (hi.le hxF)
    have htj' : (x : V) + t • yi ∈ interior (S.cone j : Set V) := by
      apply htj
      simp only [map_add, map_smul, smul_eq_mul, hfx, zero_add]
      rw [mul_div_assoc]
      exact mul_pos htpos hpos
    refine ⟨interior (S.cone i : Set V) ∪ interior (S.cone j : Set V),
      hiconn.union ((x : V) + t • yi) hti htj' hjconn,
      subset_union_left, subset_union_right, ?_⟩
    exact union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

end Unimodular.PrimitiveRegions

#print axioms Unimodular.PrimitiveRegions.common_facet_bridge

