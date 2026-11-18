module

public import Unimodular.ConeFoundations
public import Unimodular.MinimalFaces
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open scoped Pointwise Topology
open Filter Set

namespace Unimodular.ConeInterior

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem isClosed_of_fg {C : PointedCone ℝ V} (hC : C.FG) : IsClosed (C : Set V) := by
  classical
  obtain ⟨s, hs⟩ := hC
  have he : Set.range (fun v : s => (v : V)) = (s : Set V) := by ext; simp
  rw [← hs, ← he]
  exact FiniteCone.isClosed_hull (fun v : s => (v : V))

theorem interior_nonempty_of_span_eq_top {C : PointedCone ℝ V}
    (hC : Submodule.span ℝ (C : Set V) = ⊤) : (interior (C : Set V)).Nonempty := by
  apply (C : ConvexCone ℝ V).convex.interior_nonempty_iff_affineSpan_eq_top.2
  change affineSpan ℝ (C : Set V) = ⊤
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ (C : Set V) C.zero_mem), hC]
  rfl

theorem add_mem_interior {C : PointedCone ℝ V} {x y : V}
    (hx : x ∈ interior (C : Set V)) (hy : y ∈ C) : x + y ∈ interior (C : Set V) := by
  have hsub : (fun z : V => z + y) '' (C : Set V) ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.add_mem hz hy
  exact interior_mono hsub
    ((isOpenMap_add_right y).image_interior_subset _ ⟨x, hx, rfl⟩)

theorem smul_mem_interior {C : PointedCone ℝ V} {x : V}
    (hx : x ∈ interior (C : Set V)) {a : ℝ} (ha : 0 < a) :
    a • x ∈ interior (C : Set V) := by
  have hsub : (fun z : V => a • z) '' (C : Set V) ⊆ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact PointedCone.smul_mem C ha.le hz
  exact interior_mono hsub
    ((isOpenMap_smul₀ ha.ne').image_interior_subset _ ⟨x, hx, rfl⟩)

theorem face_eq_of_mem_interior {C F : PointedCone ℝ V} (hF : F.IsFaceOf C)
    {x : V} (hxF : x ∈ F) (hx : x ∈ interior (C : Set V)) : F = C := by
  apply le_antisymm hF.le
  intro y hy
  have hcont : Tendsto (fun t : ℝ => x - t • y) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x - t • y) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa using hc.tendsto (0 : ℝ)
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, x - t • y ∈ C :=
    (hcont.eventually (mem_interior_iff_mem_nhds.1 hx)).filter_mono nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hmem⟩ := (htpos.and he).exists
  apply hF.mem_of_smul_add_mem hy hmem ht
  simpa using hxF

theorem mem_interior_iff_dominatedCone_eq {C : PointedCone ℝ V}
    (hint : (interior (C : Set V)).Nonempty) {x : V} (hx : x ∈ C) :
    x ∈ interior (C : Set V) ↔ MinimalFaces.dominatedCone C x = C := by
  constructor
  · intro hxi
    exact face_eq_of_mem_interior (MinimalFaces.dominatedCone_isFaceOf C x)
      (MinimalFaces.self_mem_dominatedCone hx) hxi
  · intro heq
    obtain ⟨y, hy⟩ := hint
    have hym : y ∈ MinimalFaces.dominatedCone C x := by
      rw [heq]
      exact interior_subset hy
    obtain ⟨_, a, ha, hres⟩ := hym
    have hai : a • x ∈ interior (C : Set V) := by
      simpa using add_mem_interior hy hres
    rcases ha.eq_or_lt with rfl | hap
    · have h0 : (0 : V) ∈ interior (C : Set V) := by simpa using hai
      simpa using add_mem_interior h0 hx
    · have hm := smul_mem_interior hai (inv_pos.2 hap)
      simpa only [smul_smul, inv_mul_cancel₀ hap.ne', one_smul] using hm

theorem span_ne_top_of_proper_face {C F : PointedCone ℝ V}
    (hF : F.IsFaceOf C) (hne : F ≠ C) : Submodule.span ℝ (F : Set V) ≠ ⊤ := by
  intro ht
  have h := QuotientFaces.inf_span_eq hF
  unfold QuotientFaces.faceSpan at h
  rw [ht] at h
  have he : C ⊓ PointedCone.ofSubmodule (⊤ : Submodule ℝ V) = C := by ext; simp
  exact hne (h.symm.trans he)

theorem finrank_lt_of_proper_face {C F : PointedCone ℝ V}
    (hF : F.IsFaceOf C) (hne : F ≠ C) :
    Module.finrank ℝ (Submodule.span ℝ (F : Set V)) < Module.finrank ℝ V := by
  have h := Submodule.finrank_lt_finrank_of_lt
    (lt_top_iff_ne_top.2 (span_ne_top_of_proper_face hF hne))
  simpa only [finrank_top] using h

/-- Every codimension-one subspace is the kernel of an actual nonzero linear functional. -/
theorem exists_normal (L : Submodule ℝ V)
    (hL : Module.finrank ℝ L + 1 = Module.finrank ℝ V) :
    ∃ f : V →ₗ[ℝ] ℝ, f ≠ 0 ∧ LinearMap.ker f = L := by
  have hne : L ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hL
    omega
  obtain ⟨f, hf, hLf⟩ := L.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  refine ⟨f, hf, (Submodule.eq_of_le_of_finrank_eq hLf ?_).symm⟩
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

theorem normal_ne_zero_at_interior {C F : PointedCone ℝ V} (hF : F.IsFaceOf C)
    (hne : F ≠ C) (f : V →ₗ[ℝ] ℝ)
    (hker : LinearMap.ker f = Submodule.span ℝ (F : Set V))
    {y : V} (hy : y ∈ interior (C : Set V)) : f y ≠ 0 := by
  intro hf
  have hyF : y ∈ F := by
    rw [← QuotientFaces.inf_span_eq hF]
    refine ⟨interior_subset hy, ?_⟩
    change y ∈ Submodule.span ℝ (F : Set V)
    rw [← hker]
    exact hf
  exact hne (face_eq_of_mem_interior hF hyF hy)

/-- A codimension-one face fixes the side of its supporting hyperplane occupied by the
whole cone. The orientation is determined by any interior point. -/
theorem normal_nonneg_on_cone {C F : PointedCone ℝ V} (hF : F.IsFaceOf C)
    (f : V →ₗ[ℝ] ℝ) (hker : LinearMap.ker f = Submodule.span ℝ (F : Set V))
    {y : V} (hy : y ∈ C) (hfy : 0 < f y) : ∀ z ∈ C, 0 ≤ f z := by
  intro z hz
  by_contra hn
  have hfz : f z < 0 := lt_of_not_ge hn
  let a : ℝ := -f z / f y
  have ha : 0 < a := div_pos (neg_pos.2 hfz) hfy
  have hw : a • y + z ∈ F := by
    rw [← QuotientFaces.inf_span_eq hF]
    refine ⟨C.add_mem (PointedCone.smul_mem C ha.le hy) hz, ?_⟩
    change a • y + z ∈ Submodule.span ℝ (F : Set V)
    rw [← hker]
    change f (a • y + z) = 0
    simp only [map_add, map_smul, smul_eq_mul, a]
    rw [div_mul_cancel₀ _ hfy.ne', neg_add_cancel]
  have hyF := hF.mem_of_smul_add_mem hy hz ha hw
  have hzero : f y = 0 := by
    change y ∈ LinearMap.ker f
    rw [hker]
    exact Submodule.subset_span hyF
  linarith

end Unimodular.ConeInterior
