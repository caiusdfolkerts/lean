/-
The exposed-face span and intrinsic-interior arguments below are adapted from
openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
Original source files and hashes are retained under vendor/openai-math and
in audit/openai-polytope-provenance.json. Selected original theorem bodies are
preserved verbatim. The active-constraint proof and unit-normal comparison are
new proofs here, avoiding the upstream projection-front and surface-area theory.
-/
module

public import VolumePolynomials.PolytopeFoundation
public import VolumePolynomials.PolytopeFaces
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section
set_option autoImplicit false

noncomputable section
open Set
open scoped RealInnerProductSpace Pointwise

namespace OAI.Paper092

def exposedFace {n : ℕ} (K : Set (Euclidean n)) (u : Euclidean n) : Set (Euclidean n) :=
  (innerSL ℝ u).toExposed K

@[simp] theorem exposedFace_zero {n : ℕ} (K : Set (Euclidean n)) : exposedFace K 0 = K := by
  first
  | ext x
    simp [exposedFace, ContinuousLinearMap.toExposed]

theorem exposedFace_nonempty {n : ℕ} (K : Set (Euclidean n)) (hK : IsCompact K)
    (hne : K.Nonempty) (u : Euclidean n) : (exposedFace K u).Nonempty := by
  first
  | obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (innerSL ℝ u).continuous.continuousOn
    exact ⟨x, hx, hmax⟩

theorem exposedFace_vectorSpan_le_normalHyperplane {n : ℕ}
    (K : Set (Euclidean n)) (u : Euclidean n) :
    vectorSpan ℝ (exposedFace K u) ≤ normalHyperplane u := by
  first
  | rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪u, x - y⟫ = 0
    rw [inner_sub_right]
    exact sub_eq_zero.mpr (le_antisymm (hy.2 x hx.1) (hx.2 y hy.1))

theorem exposedFace_finrank_le {n : ℕ} (K : Set (Euclidean n))
    {u : Euclidean n} (hu : u ≠ 0) :
    Module.finrank ℝ (vectorSpan ℝ (exposedFace K u)) ≤ n - 1 := by
  first
  | have h := Submodule.finrank_mono (exposedFace_vectorSpan_le_normalHyperplane K u)
    rwa [normalHyperplane_finrank u hu] at h

theorem inner_eq_of_mem_intrinsicInterior {d : ℕ} {S : Set (Euclidean d)}
    {x : Euclidean d} (hx : x ∈ intrinsicInterior ℝ S) (v : Euclidean d)
    (hmax : ∀ z ∈ S, ⟪v, z⟫ ≤ ⟪v, x⟫) :
    ∀ z ∈ S, ⟪v, z⟫ = ⟪v, x⟫ := by
  first
  | obtain ⟨xQ, hxQ, rfl⟩ := mem_intrinsicInterior.mp hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxQ)
    intro z hz
    by_cases hzx : z = xQ.val
    · simp only [hzx]
    let t : ℝ := ε / (2 * ‖xQ.val - z‖)
    have hnorm : 0 < ‖xQ.val - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzx))
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
    let y : affineSpan ℝ S := ⟨xQ.val + t • (xQ.val - z), by
      simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using
        (affineSpan ℝ S).smul_vsub_vadd_mem t xQ.property
          (subset_affineSpan ℝ S hz) xQ.property⟩
    have hyball : y ∈ Metric.ball xQ ε := by
      change dist (xQ.val + t • (xQ.val - z)) xQ.val < ε
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖xQ.val - z‖ = ε / 2 := by
        dsimp [t]
        field_simp
      rw [heq]
      linarith
    have hy : y.val ∈ S := hball hyball
    have hle := hmax y.val hy
    change ⟪v, xQ.val + t • (xQ.val - z)⟫ ≤ ⟪v, xQ.val⟫ at hle
    rw [inner_add_right, real_inner_smul_right, inner_sub_right] at hle
    exact le_antisymm (hmax z hz) (by nlinarith)

namespace HPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι] (P : HPolytope d ι)

theorem body_convex : Convex ℝ P.body := by
  first
  | intro x hx y hy a b ha hb hab i
    simp only [inner_add_right, real_inner_smul_right]
    calc
      a * ⟪P.normal i, x⟫ + b * ⟪P.normal i, y⟫ ≤
          a * P.offset i + b * P.offset i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
          (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = P.offset i := by rw [← add_mul, hab, one_mul]

theorem body_nonempty : P.body.Nonempty := by
  first
  | obtain ⟨x, hx⟩ := P.strict_feasible
    exact ⟨x, fun i => (hx i).le⟩

theorem exists_active_of_mem_exposedFace {u x : Euclidean d} (hu : u ≠ 0)
    (hx : x ∈ exposedFace P.body u) : ∃ i, x ∈ P.face i := by
  first
  | classical
    by_contra hnone
    have hstrict : ∀ i, ⟪P.normal i, x⟫ < P.offset i := by
      intro i
      exact lt_of_le_of_ne (hx.1 i) (fun h => hnone ⟨i, hx.1, h⟩)
    let S : Set (Euclidean d) := ⋂ i, {y | ⟪P.normal i, y⟫ < P.offset i}
    have hS : IsOpen S := isOpen_iInter_of_finite fun i =>
      isOpen_lt (innerSL ℝ (P.normal i)).continuous continuous_const
    have hxS : x ∈ S := mem_iInter.mpr hstrict
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hxS
    have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let t : ℝ := ε / (2 * ‖u‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
    have hyball : x + t • u ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖u‖ = ε / 2 := by dsimp [t]; field_simp
      rw [heq]
      linarith
    have hy : x + t • u ∈ P.body :=
      fun i => (mem_iInter.mp (hball hyball) i).le
    have hmax := hx.2 (x + t • u) hy
    change ⟪u, x + t • u⟫ ≤ ⟪u, x⟫ at hmax
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hmax
    have hpos := mul_pos ht (sq_pos_of_pos hnorm)
    linarith

theorem exposedFace_eq_face {u : Euclidean d} (hu : u ≠ 0)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace P.body u)) = d - 1) :
    ∃ i, exposedFace P.body u = P.face i := by
  first
  | have hconv : Convex ℝ (exposedFace P.body u) :=
      (show IsExposed ℝ P.body (exposedFace P.body u) from
        ContinuousLinearMap.toExposed.isExposed).convex P.body_convex
    have hne := exposedFace_nonempty P.body P.compact P.body_nonempty u
    obtain ⟨x, hx⟩ := (intrinsicInterior_nonempty hconv).mpr hne
    have hxF : x ∈ exposedFace P.body u := intrinsicInterior_subset hx
    obtain ⟨i, hxi⟩ := P.exists_active_of_mem_exposedFace hu hxF
    have hinner : ∀ z ∈ exposedFace P.body u, ⟪P.normal i, z⟫ = P.offset i := by
      intro z hz
      apply Eq.trans (inner_eq_of_mem_intrinsicInterior hx (P.normal i) ?_ z hz) hxi.2
      intro y hy
      rw [hxi.2]
      exact hy.1 i
    have hle : vectorSpan ℝ (exposedFace P.body u) ≤ normalHyperplane (P.normal i) := by
      rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, b, hb, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, a - b⟫ = 0
      rw [inner_sub_right, hinner a ha, hinner b hb, sub_self]
    have hn : P.normal i ≠ 0 := by
      intro h
      have hnorm := P.normal_unit i
      rw [h, norm_zero] at hnorm
      norm_num at hnorm
    have hspan_i : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane (P.normal i) :=
      Submodule.eq_of_le_of_finrank_eq hle (hdim.trans (normalHyperplane_finrank _ hn).symm)
    have hspan_u : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane u :=
      Submodule.eq_of_le_of_finrank_eq (exposedFace_vectorSpan_le_normalHyperplane P.body u)
        (hdim.trans (normalHyperplane_finrank u hu).symm)
    refine ⟨i, Subset.antisymm (fun z hz => ⟨hz.1, hinner z hz⟩) ?_⟩
    intro y hy
    have hyi : y - x ∈ normalHyperplane (P.normal i) := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, hy.2, hxi.2, sub_self]
    have hyu : y - x ∈ normalHyperplane u := by
      rwa [← hspan_u, hspan_i]
    have heq : ⟪u, y⟫ = ⟪u, x⟫ := by
      have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hyu
      simpa only [inner_sub_right, sub_eq_zero] using h
    refine ⟨hy.1, ?_⟩
    intro z hz
    change ⟪u, z⟫ ≤ ⟪u, y⟫
    rw [heq]
    exact hxF.2 z hz

theorem exists_strict_face_point_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    ∃ x ∈ P.face i, ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
  first
  | classical
    push Not at hessential
    obtain ⟨y, hy, hyi⟩ := hessential
    obtain ⟨z, hz⟩ := P.strict_feasible
    have hden : 0 < ⟪P.normal i, y⟫ - ⟪P.normal i, z⟫ := by linarith [hz i]
    let t : ℝ := (P.offset i - ⟪P.normal i, z⟫) /
      (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫)
    have ht0 : 0 < t := div_pos (sub_pos.mpr (hz i)) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    have htmul : t * (⟪P.normal i, y⟫ - ⟪P.normal i, z⟫) =
        P.offset i - ⟪P.normal i, z⟫ := div_mul_cancel₀ _ hden.ne'
    let x := (1 - t) • z + t • y
    have hxi : ⟪P.normal i, x⟫ = P.offset i := by
      dsimp [x]
      simp only [inner_add_right, real_inner_smul_right]
      nlinarith
    have hxj : ∀ j, j ≠ i → ⟪P.normal j, x⟫ < P.offset j := by
      intro j hji
      have hleft := mul_lt_mul_of_pos_left (hz j) (sub_pos.mpr ht1)
      have hright := mul_le_mul_of_nonneg_left (hy j hji) ht0.le
      dsimp [x]
      simp only [inner_add_right, real_inner_smul_right]
      nlinarith
    refine ⟨x, ⟨?_, hxi⟩, hxj⟩
    intro j
    by_cases hji : j = i
    · simpa only [hji, hxi] using le_refl (P.offset i)
    · exact (hxj j hji).le

theorem affineSpan_face_of_essential (i : ι)
    (hessential : ¬ ∀ x : Euclidean d,
      (∀ j, j ≠ i → ⟪P.normal j, x⟫ ≤ P.offset j) → ⟪P.normal i, x⟫ ≤ P.offset i) :
    (affineSpan ℝ (P.face i) : Set (Euclidean d)) =
      {y | ⟪P.normal i, y⟫ = P.offset i} := by
  first
  | classical
    let Q : AffineSubspace ℝ (Euclidean d) :=
      (affineSpan ℝ ({P.offset i} : Set ℝ)).comap (innerₛₗ ℝ (P.normal i)).toAffineMap
    have hQ (y : Euclidean d) : y ∈ Q ↔ ⟪P.normal i, y⟫ = P.offset i := by
      simp [Q]
    have hle : affineSpan ℝ (P.face i) ≤ Q := by
      apply affineSpan_le.mpr
      intro y hy
      exact (hQ y).mpr hy.2
    ext y
    constructor
    · exact fun hy => (hQ y).mp (hle hy)
    · intro hy
      change ⟪P.normal i, y⟫ = P.offset i at hy
      change y ∈ affineSpan ℝ (P.face i)
      obtain ⟨x, hx, hxstrict⟩ := P.exists_strict_face_point_of_essential i hessential
      have hxspan : x ∈ affineSpan ℝ (P.face i) := subset_affineSpan ℝ _ hx
      by_cases hxy : y = x
      · simpa only [hxy] using hxspan
      let S : Set (Euclidean d) := ⋂ j : {j : ι // j ≠ i},
        {z | ⟪P.normal j.val, z⟫ < P.offset j.val}
      have hopen : IsOpen S := isOpen_iInter_of_finite fun j =>
        isOpen_lt (innerSL ℝ (P.normal j.val)).continuous continuous_const
      have hxS : x ∈ S := mem_iInter.mpr (fun j => hxstrict j.val j.property)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxS
      have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      let t : ℝ := ε / (2 * ‖y - x‖)
      have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hnorm)
      let z := x + t • (y - x)
      have hzball : z ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        change ‖x + t • (y - x) - x‖ < ε
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        dsimp [t]
        have heq : ε / (2 * ‖y - x‖) * ‖y - x‖ = ε / 2 := by field_simp
        rw [heq]
        linarith
      have hzS := hball hzball
      have hzi : ⟪P.normal i, z⟫ = P.offset i := by
        dsimp [z]
        simp only [inner_add_right, real_inner_smul_right, inner_sub_right, hy, hx.2,
          sub_self, mul_zero, add_zero]
      have hzface : z ∈ P.face i := by
        refine ⟨?_, hzi⟩
        intro j
        by_cases hji : j = i
        · simpa only [hji, hzi] using le_refl (P.offset i)
        · exact (mem_iInter.mp hzS ⟨j, hji⟩).le
      have hzspan := subset_affineSpan ℝ (P.face i) hzface
      have hmem := (affineSpan ℝ (P.face i)).smul_vsub_vadd_mem t⁻¹ hzspan hxspan hxspan
      have heq : t⁻¹ • (z - x) + x = y := by
        dsimp [z]
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, sub_add_cancel]
      simpa only [vsub_eq_sub, vadd_eq_add, heq] using hmem

/-- The outward unit normal of a genuine exposed facet is one of the finite
halfspace normals. Strict feasibility fixes its orientation. -/
theorem unit_normal_mem_of_exposed_finrank {u : Euclidean d}
    (hu : ‖u‖ = 1)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace P.body u)) = d - 1) :
    ∃ i, u = P.normal i := by
  first
  | have hu0 : u ≠ 0 := by intro h; simpa [h] using hu
    obtain ⟨i, hi⟩ := P.exposedFace_eq_face hu0 hdim
    have hn0 : P.normal i ≠ 0 := by
      intro h
      simpa [h] using P.normal_unit i
    have hFi : vectorSpan ℝ (exposedFace P.body u) ≤ normalHyperplane (P.normal i) := by
      rw [vectorSpan_def]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, b, hb, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      change ⟪P.normal i, a - b⟫ = 0
      have ha' : a ∈ P.face i := hi ▸ ha
      have hb' : b ∈ P.face i := hi ▸ hb
      rw [inner_sub_right, ha'.2, hb'.2, sub_self]
    have hspan_i : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane (P.normal i) :=
      Submodule.eq_of_le_of_finrank_eq hFi
        (hdim.trans (normalHyperplane_finrank _ hn0).symm)
    have hspan_u : vectorSpan ℝ (exposedFace P.body u) = normalHyperplane u :=
      Submodule.eq_of_le_of_finrank_eq (exposedFace_vectorSpan_le_normalHyperplane _ u)
        (hdim.trans (normalHyperplane_finrank u hu0).symm)
    have hH : normalHyperplane (P.normal i) = normalHyperplane u :=
      hspan_i.symm.trans hspan_u
    have hspan : Submodule.span ℝ {P.normal i} = Submodule.span ℝ {u} := by
      have h := congrArg Submodule.orthogonal hH
      simpa only [normalHyperplane, Submodule.orthogonal_orthogonal] using h
    have humem : u ∈ Submodule.span ℝ {P.normal i} := by
      rw [hspan]
      exact Submodule.subset_span (mem_singleton u)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp humem
    have habs : |c| = 1 := by
      have h := congrArg norm hc
      simpa only [norm_smul, Real.norm_eq_abs, P.normal_unit, hu, mul_one] using h
    obtain ⟨x, hx⟩ := exposedFace_nonempty P.body P.compact P.body_nonempty u
    have hxi : x ∈ P.face i := hi ▸ hx
    obtain ⟨p, hp⟩ := P.strict_feasible
    have hpbody : p ∈ P.body := fun j => (hp j).le
    have hm := hx.2 p hpbody
    change ⟪u, p⟫ ≤ ⟪u, x⟫ at hm
    rw [← hc, real_inner_smul_left, real_inner_smul_left, hxi.2] at hm
    have hdiff : 0 < P.offset i - ⟪P.normal i, p⟫ := sub_pos.mpr (hp i)
    have hc0 : 0 ≤ c := by nlinarith
    have hc1 : c = 1 := by simpa only [abs_of_nonneg hc0] using habs
    refine ⟨i, ?_⟩
    simpa only [hc1, one_smul] using hc.symm

end HPolytope
end OAI.Paper092

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

/-- Every positive weighted sum uses only the finite facet-normal directions of
its unweighted total. The constituent sets may be lower dimensional. -/
theorem positive_sum_facet_normals {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set (Euclidean d)) (hA : ∀ i, IsCompact (A i))
    (hne : ∀ i, (A i).Nonempty) (P : HPolytope d κ)
    (hP : P.body = ∑ i, A i) (t : ι → ℝ) (ht : ∀ i, 0 < t i)
    {u : Euclidean d} (hu : ‖u‖ = 1)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (exposedFace (∑ i, t i • A i) u)) = d - 1) :
    ∃ i, u = P.normal i := by
  first
  | apply P.unit_normal_mem_of_exposed_finrank hu
    rw [hP]
    change Module.finrank ℝ (vectorSpan ℝ ((innerSL ℝ u).toExposed (∑ i, A i))) = _
    have heq := PolytopeFaces.vectorSpan_exposed_weighted_sum (innerSL ℝ u)
      Finset.univ A t (fun i _ => hA i) (fun i _ => hne i) (fun i _ => ht i)
    rw [← heq]
    exact hdim

end VolumePolynomials.PolytopeGeometry
