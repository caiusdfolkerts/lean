module

public import triangle_sides
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.AffineSpace.Basis

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-! # Generic geometry of finite planar triangles

This module contains the exact generic sections extracted from the harmonic
embedding development. It assumes affine independence only in the generic
lemmas where it is mathematically required, and proves no harmonic conclusion.
-/

@[expose] public section
noncomputable section

/-! ## TriangleCombinatorics -/

namespace NormalProjective.Planar

open Finset

variable {V : Type*} [DecidableEq V]

theorem triangle_eq_insert_pair {s : Finset V} (hs : s.card = 3)
    {a b : V} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ s = {a,b,x} := by
  classical
  have hsub : ({a,b} : Finset V) ⊆ s := by
    exact Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hcard : (s \ {a,b}).card = 1 := by
    rw [card_sdiff_of_subset hsub,hs]
    simp [hab]
  obtain ⟨x,hx⟩ := card_eq_one.mp hcard
  have hxmem : x ∈ s \ {a,b} := by rw [hx]; simp
  have hxnot : x ≠ a ∧ x ≠ b := by
    simpa only [mem_insert,mem_singleton,not_or] using (mem_sdiff.mp hxmem).2
  have hxa : x ≠ a := hxnot.1
  have hxb : x ≠ b := hxnot.2
  refine ⟨x,hxa,hxb,?_⟩
  have heq := sdiff_union_of_subset hsub
  rw [hx] at heq
  simpa [Finset.union_assoc,Finset.union_comm,Finset.union_left_comm] using heq.symm

theorem adjacent_triangles_decompose {s t : Finset V}
    (hs : s.card = 3) (ht : t.card = 3) (hst : s ≠ t)
    (hc : 2 ≤ (s ∩ t).card) :
    ∃ a b x y, a ≠ b ∧ x ≠ y ∧ x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧
      s = {a,b,x} ∧ t = {a,b,y} := by
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < (s ∩ t).card)
  obtain ⟨x,hxa,hxb,hsx⟩ := triangle_eq_insert_pair hs hab (mem_inter.mp ha).1 (mem_inter.mp hb).1
  obtain ⟨y,hya,hyb,hty⟩ := triangle_eq_insert_pair ht hab (mem_inter.mp ha).2 (mem_inter.mp hb).2
  have hxy : x ≠ y := by intro h; apply hst; simpa [hsx,hty,h]
  exact ⟨a,b,x,y,hab,hxy,hxa,hxb,hya,hyb,hsx,hty⟩

end NormalProjective.Planar

/-! ## TriangleCoordinates -/

/-!
# Barycentric coordinates and local half-planes of genuine triangles
-/

namespace NormalProjective.Planar

open Set Finset Filter
open scoped Topology

structure Triangle where
  point : Fin 3 → ℂ
  independent : AffineIndependent ℝ point

namespace Triangle

variable (T : Triangle)

def basis : AffineBasis (Fin 3) ℝ ℂ where
  toFun := T.point
  ind' := T.independent
  tot' := by
    exact T.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

def carrier : Set ℂ := convexHull ℝ (range T.point)

def coord (i : Fin 3) : ℂ →ᵃ[ℝ] ℝ := T.basis.coord i

theorem coord_continuous (i : Fin 3) : Continuous (T.coord i) :=
  continuous_barycentric_coord T.basis i

@[simp] theorem coord_point (i j : Fin 3) : T.coord i (T.point j) = if i = j then 1 else 0 :=
  T.basis.coord_apply i j

theorem sum_coord (z : ℂ) : ∑ i, T.coord i z = 1 := T.basis.sum_coord_apply_eq_one z

theorem reconstruct (z : ℂ) : ∑ i, T.coord i z • T.point i = z :=
  T.basis.linear_combination_coord_eq_self z

theorem mem_carrier_iff (z : ℂ) : z ∈ T.carrier ↔ ∀ i, 0 ≤ T.coord i z := by
  exact congrArg (fun S : Set ℂ => z ∈ S) T.basis.convexHull_eq_nonneg_coord |>.to_iff

theorem mem_interior_iff (z : ℂ) : z ∈ interior T.carrier ↔ ∀ i, 0 < T.coord i z := by
  exact congrArg (fun S : Set ℂ => z ∈ S) T.basis.interior_convexHull |>.to_iff

theorem compact_carrier : IsCompact T.carrier := (Set.finite_range T.point).isCompact_convexHull ℝ

theorem sum_three (f : Fin 3 → ℝ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_succ] <;> ring

theorem reconstruct_three (z : ℂ) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    T.coord i z • T.point i + T.coord j z • T.point j + T.coord k z • T.point k = z := by
  have h := T.reconstruct z
  apply Complex.ext
  · have hre := congrArg Complex.re h
    rw [Complex.re_sum,
      sum_three (fun l => (T.coord l z • T.point l).re) i j k hij hik hjk] at hre
    simpa only [Complex.add_re] using hre
  · have him := congrArg Complex.im h
    rw [Complex.im_sum,
      sum_three (fun l => (T.coord l z • T.point l).im) i j k hij hik hjk] at him
    simpa only [Complex.add_im] using him

theorem coord_zero_on_edge (i j k : Fin 3) (hik : i ≠ k) (hjk : j ≠ k)
    {z : ℂ} (hz : z ∈ segment ℝ (T.point i) (T.point j)) : T.coord k z = 0 := by
  have hconv : Convex ℝ {z | T.coord k z = 0} :=
    (convex_singleton (0 : ℝ)).affine_preimage (T.coord k)
  exact hconv.segment_subset (by simp [hik.symm]) (by simp [hjk.symm]) hz

theorem mem_edge_iff_coord_zero (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {z : ℂ} (hz : z ∈ T.carrier) :
    z ∈ segment ℝ (T.point i) (T.point j) ↔ T.coord k z = 0 := by
  constructor
  · exact T.coord_zero_on_edge i j k hik hjk
  · intro hk
    have hnonneg := (T.mem_carrier_iff z).mp hz
    have hsum := T.sum_coord z
    rw [sum_three (fun l => T.coord l z) i j k hij hik hjk,hk,add_zero] at hsum
    have hrecon := T.reconstruct_three z i j k hij hik hjk
    rw [hk,zero_smul,add_zero] at hrecon
    exact ⟨T.coord i z,T.coord j z,hnonneg i,hnonneg j,hsum,hrecon⟩

theorem coord_mul_height (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (z : ℂ) :
    T.coord k z * edgeHeight (T.point i) (T.point j) (T.point k) =
      edgeHeight (T.point i) (T.point j) z := by
  let L : ℂ →ᵃ[ℝ] ℝ :=
    Complex.imCLM.toLinearMap.toAffineMap.comp (edgeNormalize (T.point i) (T.point j))
  have heq : L = edgeHeight (T.point i) (T.point j) (T.point k) • T.coord k := by
    apply AffineMap.ext_on T.basis.tot
    rintro x ⟨l,rfl⟩
    change edgeHeight (T.point i) (T.point j) (T.point l) =
      edgeHeight (T.point i) (T.point j) (T.point k) * T.coord k (T.point l)
    have hcover : l = i ∨ l = j ∨ l = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
    rcases hcover with rfl | rfl | rfl
    · simp [coord_point,hik.symm,edgeHeight,edgeNormalize]
    · simp [coord_point,hjk.symm,edgeHeight,edgeNormalize_right (T.independent.injective.ne hij)]
    · simp [coord_point]
  have h := congrArg (fun A : ℂ →ᵃ[ℝ] ℝ => A z) heq
  change edgeHeight (T.point i) (T.point j) z =
    edgeHeight (T.point i) (T.point j) (T.point k) * T.coord k z at h
  simpa only [mul_comm] using h.symm

theorem mem_edge_iff_height_zero (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : edgeHeight (T.point i) (T.point j) (T.point k) ≠ 0)
    {z : ℂ} (hz : z ∈ T.carrier) :
    z ∈ segment ℝ (T.point i) (T.point j) ↔
      edgeHeight (T.point i) (T.point j) z = 0 := by
  rw [T.mem_edge_iff_coord_zero i j k hij hik hjk hz]
  rw [← T.coord_mul_height i j k hij hik hjk z,mul_eq_zero]
  simp [hk]

theorem edge_coords_positive (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {z : ℂ} (hz : z ∈ openSegment ℝ (T.point i) (T.point j)) :
    0 < T.coord i z ∧ 0 < T.coord j z ∧ T.coord k z = 0 := by
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  have hmap (l : Fin 3) : T.coord l (r • T.point i+s • T.point j) =
      r * T.coord l (T.point i)+s * T.coord l (T.point j) := by
    have heq : r • T.point i+s • T.point j =
        s • (T.point j-T.point i)+T.point i := by
      have hr' : r = 1-s := by linarith
      rw [hr']; module
    have hlinear : (T.coord l).linear (T.point j - T.point i) =
        T.coord l (T.point j) - T.coord l (T.point i) := by
      simpa only [vsub_eq_sub] using
        (T.coord l).linear_apply_vsub (T.point j) (T.point i)
    rw [heq,← vadd_eq_add,AffineMap.map_vadd]
    simp only [map_smul,vadd_eq_add,smul_eq_mul]
    rw [hlinear,show r = 1-s by linarith]
    ring
  simp only [hmap,T.coord_point,ite_true,ite_false,hij,hij.symm,hik.symm,hjk.symm,
    mul_one,mul_zero,add_zero,zero_add]
  exact ⟨hr,hs,True.intro⟩

theorem locally_carrier_is_halfplane_at_openEdge (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {z : ℂ} (hz : z ∈ openSegment ℝ (T.point i) (T.point j)) :
    ∀ᶠ y in 𝓝 z, y ∈ T.carrier ↔ 0 ≤ T.coord k y := by
  have hc := T.edge_coords_positive i j k hij hik hjk hz
  have hi : ∀ᶠ y in 𝓝 z, 0 < T.coord i y :=
    (isOpen_lt continuous_const (T.coord_continuous i)).mem_nhds hc.1
  have hj : ∀ᶠ y in 𝓝 z, 0 < T.coord j y :=
    (isOpen_lt continuous_const (T.coord_continuous j)).mem_nhds hc.2.1
  filter_upwards [hi,hj] with y hiy hjy
  rw [T.mem_carrier_iff]
  constructor
  · exact fun h => h k
  · intro hky l
    have hcover : l = i ∨ l = j ∨ l = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
    rcases hcover with rfl | rfl | rfl
    · exact hiy.le
    · exact hjy.le
    · exact hky

theorem frontier_point_on_open_edge {z : ℂ} (hz : z ∈ frontier T.carrier)
    (hv : ∀ i, z ≠ T.point i) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z ∈ openSegment ℝ (T.point i) (T.point j) ∧ T.coord k z = 0 := by
  have hzin : z ∈ T.carrier := (T.compact_carrier.isClosed.frontier_subset) hz
  have hznot : z ∉ interior T.carrier := hz.2
  have hcoords := (T.mem_carrier_iff z).mp hzin
  have hznot' : ¬ ∀ i, 0 < T.coord i z := by simpa only [← T.mem_interior_iff] using hznot
  push_neg at hznot'
  obtain ⟨k,hk⟩ := hznot'
  have hk0 : T.coord k z = 0 := le_antisymm hk (hcoords k)
  have hex : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases k
    · exact ⟨1,2,by decide,by decide,by decide⟩
    · exact ⟨0,2,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  obtain ⟨i,j,hij,hik,hjk⟩ := hex
  have hseg := (T.mem_edge_iff_coord_zero i j k hij hik hjk hzin).mpr hk0
  obtain ⟨r,s,hr,hs,hrs,hzrs⟩ := hseg
  have hrp : 0 < r := by
    by_contra hr'
    have hr0 : r = 0 := le_antisymm (le_of_not_gt hr') hr
    have hs1 : s = 1 := by linarith
    exact hv j (by simpa [hr0,hs1] using hzrs.symm)
  have hsp : 0 < s := by
    by_contra hs'
    have hs0 : s = 0 := le_antisymm (le_of_not_gt hs') hs
    have hr1 : r = 1 := by linarith
    exact hv i (by simpa [hs0,hr1] using hzrs.symm)
  exact ⟨i,j,k,hij,hik,hjk,⟨r,s,hrp,hsp,hrs,hzrs⟩,hk0⟩

end Triangle

end NormalProjective.Planar

/-! ## HorizontalSlice -/

/-!
# Compact horizontal sections of convex planar sets

These are literal intersections with a horizontal line, parametrized by the
real coordinate. Their endpoints are genuine boundary points of the planar
set. This is the geometric input to the finite interval-chain argument.
-/

namespace NormalProjective.Planar

open Set Filter
open scoped Topology

def horizontalPoint (c x : ℝ) : ℂ := (x : ℂ) + (c : ℂ) * Complex.I

@[simp] theorem horizontalPoint_re (c x : ℝ) : (horizontalPoint c x).re = x := by
  simp [horizontalPoint]

@[simp] theorem horizontalPoint_im (c x : ℝ) : (horizontalPoint c x).im = c := by
  simp [horizontalPoint]

theorem horizontalPoint_eq {z : ℂ} {c : ℝ} (hz : z.im = c) :
    horizontalPoint c z.re = z := by
  apply Complex.ext <;> simp [hz]

theorem continuous_horizontalPoint (c : ℝ) : Continuous (horizontalPoint c) := by
  unfold horizontalPoint
  fun_prop

def horizontalAffine (c : ℝ) : ℝ →ᵃ[ℝ] ℂ where
  toFun := horizontalPoint c
  linear := Complex.ofRealCLM.toLinearMap
  map_vadd' x y := by simp [horizontalPoint]; ring

def horizontalSlice (S : Set ℂ) (c : ℝ) : Set ℝ := horizontalPoint c ⁻¹' S

theorem horizontalSlice_eq_image (S : Set ℂ) (c : ℝ) :
    horizontalSlice S c = Complex.re '' (S ∩ {z | z.im = c}) := by
  ext x
  constructor
  · intro hx
    exact ⟨horizontalPoint c x,⟨hx,by simp⟩,by simp⟩
  · rintro ⟨z,⟨hz,hzc⟩,rfl⟩
    change horizontalPoint c z.re ∈ S
    simpa only [horizontalPoint_eq hzc] using hz

theorem compact_horizontalSlice {S : Set ℂ} (hS : IsCompact S) (c : ℝ) :
    IsCompact (horizontalSlice S c) := by
  rw [horizontalSlice_eq_image]
  exact (hS.inter_right (isClosed_eq Complex.continuous_im continuous_const)).image
    Complex.continuous_re

theorem convex_horizontalSlice {S : Set ℂ} (hS : Convex ℝ S) (c : ℝ) :
    Convex ℝ (horizontalSlice S c) := hS.affine_preimage (horizontalAffine c)

theorem interior_horizontalSlice_of_interior {S : Set ℂ} {c x : ℝ}
    (hx : horizontalPoint c x ∈ interior S) : x ∈ interior (horizontalSlice S c) := by
  apply interior_maximal (preimage_mono interior_subset)
    (isOpen_interior.preimage (continuous_horizontalPoint c))
  exact hx

theorem horizontalSlice_eq_Icc {S : Set ℂ} (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (c : ℝ) (hne : (horizontalSlice S c).Nonempty) :
    horizontalSlice S c = Icc (sInf (horizontalSlice S c)) (sSup (horizontalSlice S c)) :=
  eq_Icc_of_connected_compact ⟨hne,(convex_horizontalSlice hconvex c).isPreconnected⟩
    (compact_horizontalSlice hcompact c)

theorem horizontalSlice_inf_lt_sup {S : Set ℂ} (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (c : ℝ)
    (hne : (horizontalPoint c ⁻¹' interior S).Nonempty) :
    sInf (horizontalSlice S c) < sSup (horizontalSlice S c) := by
  obtain ⟨x,hx⟩ := hne
  have hxS : x ∈ horizontalSlice S c := by
    change horizontalPoint c x ∈ S
    exact interior_subset (show horizontalPoint c x ∈ interior S from hx)
  have hI := horizontalSlice_eq_Icc hcompact hconvex c ⟨x,hxS⟩
  have hxint := interior_horizontalSlice_of_interior hx
  rw [hI,interior_Icc] at hxint
  exact hxint.1.trans hxint.2

theorem horizontalSlice_inf_frontier {S : Set ℂ} (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (c : ℝ) (hne : (horizontalSlice S c).Nonempty) :
    horizontalPoint c (sInf (horizontalSlice S c)) ∈ frontier S := by
  have hlo : sInf (horizontalSlice S c) ∈ horizontalSlice S c :=
    (compact_horizontalSlice hcompact c).sInf_mem hne
  refine ⟨subset_closure hlo,?_⟩
  intro hint
  have h := interior_horizontalSlice_of_interior hint
  have hI := congrArg (interior : Set ℝ → Set ℝ)
    (horizontalSlice_eq_Icc hcompact hconvex c hne)
  rw [interior_Icc] at hI
  have h' : sInf (horizontalSlice S c) ∈
      Ioo (sInf (horizontalSlice S c)) (sSup (horizontalSlice S c)) := hI ▸ h
  exact lt_irrefl _ h'.1

theorem horizontalSlice_sup_frontier {S : Set ℂ} (hcompact : IsCompact S)
    (hconvex : Convex ℝ S) (c : ℝ) (hne : (horizontalSlice S c).Nonempty) :
    horizontalPoint c (sSup (horizontalSlice S c)) ∈ frontier S := by
  have hhi : sSup (horizontalSlice S c) ∈ horizontalSlice S c :=
    (compact_horizontalSlice hcompact c).sSup_mem hne
  refine ⟨subset_closure hhi,?_⟩
  intro hint
  have h := interior_horizontalSlice_of_interior hint
  have hI := congrArg (interior : Set ℝ → Set ℝ)
    (horizontalSlice_eq_Icc hcompact hconvex c hne)
  rw [interior_Icc] at hI
  have h' : sSup (horizontalSlice S c) ∈
      Ioo (sInf (horizontalSlice S c)) (sSup (horizontalSlice S c)) := hI ▸ h
  exact lt_irrefl _ h'.2

namespace Triangle

variable (T : Triangle)

theorem slice_endpoint_on_open_edge (c : ℝ) (hgeneric : ∀ i, (T.point i).im ≠ c)
    (hne : (horizontalSlice T.carrier c).Nonempty) :
    (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      horizontalPoint c (sInf (horizontalSlice T.carrier c)) ∈
        openSegment ℝ (T.point i) (T.point j) ∧
      T.coord k (horizontalPoint c (sInf (horizontalSlice T.carrier c))) = 0) ∧
    (∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      horizontalPoint c (sSup (horizontalSlice T.carrier c)) ∈
        openSegment ℝ (T.point i) (T.point j) ∧
      T.coord k (horizontalPoint c (sSup (horizontalSlice T.carrier c))) = 0) := by
  constructor
  · apply T.frontier_point_on_open_edge
      (horizontalSlice_inf_frontier T.compact_carrier (convex_convexHull ℝ _) c hne)
    intro i hi
    exact hgeneric i (by simpa only [horizontalPoint_im] using congrArg Complex.im hi.symm)
  · apply T.frontier_point_on_open_edge
      (horizontalSlice_sup_frontier T.compact_carrier (convex_convexHull ℝ _) c hne)
    intro i hi
    exact hgeneric i (by simpa only [horizontalPoint_im] using congrArg Complex.im hi.symm)

end Triangle

end NormalProjective.Planar

/-! ## TriangleSections -/

/-! Generic horizontal sections meet genuine triangle interiors. -/

namespace NormalProjective.Planar

open Set Filter
open scoped Topology

theorem convex_interior_horizontalSlice_nonempty {S : Set ℂ}
    (hconvex : Convex ℝ S) (hint : (interior S).Nonempty)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) {c : ℝ} (hac : a.im < c) (hcb : c < b.im) :
    (horizontalPoint c ⁻¹' interior S).Nonempty := by
  have hclosure := hconvex.closure_interior_eq_closure_of_nonempty_interior hint
  have ha' : a ∈ closure (interior S) := hclosure.symm ▸ subset_closure ha
  have hb' : b ∈ closure (interior S) := hclosure.symm ▸ subset_closure hb
  obtain ⟨a',ha'im,ha'int⟩ := mem_closure_iff_nhds.mp ha' {z | z.im < c}
    ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hac)
  obtain ⟨b',hb'im,hb'int⟩ := mem_closure_iff_nhds.mp hb' {z | c < z.im}
    ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hcb)
  let f : ℝ → ℂ := fun t => (1-t) • a' + t • b'
  have hf : Continuous (fun t => (f t).im) := by dsimp [f]; fun_prop
  have hbetween : c ∈ Icc ((f 0).im) ((f 1).im) := by
    simpa [f] using And.intro ha'im.le hb'im.le
  obtain ⟨t,ht,htc⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hf.continuousOn hbetween
  have hft : f t ∈ interior S := hconvex.interior.segment_subset ha'int hb'int
    ⟨1-t,t,by linarith [ht.2],ht.1,by ring,rfl⟩
  refine ⟨(f t).re, ?_⟩
  change horizontalPoint c (f t).re ∈ interior S
  rw [horizontalPoint_eq htc]
  exact hft

theorem im_constant_on_line {z w : ℂ} {c : ℝ} (hz : z.im = c) (hw : w.im = c) :
    ∀ x ∈ affineSpan ℝ ({z,w} : Set ℂ), x.im = c := by
  apply AffineMap.eqOn_affineSpan (f := Complex.imCLM.toLinearMap.toAffineMap)
    (g := AffineMap.const ℝ ℂ c)
  intro x hx
  rcases hx with rfl | hx
  · exact hz
  · exact (Set.mem_singleton_iff.mp hx).symm ▸ hw

theorem segment_endpoints_im_eq_of_two_points {a b z w : ℂ} {c : ℝ}
    (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzw : z ≠ w) (hzc : z.im = c) (hwc : w.im = c) : a.im = c ∧ b.im = c := by
  have hspan (u : ℂ) (hu : u ∈ segment ℝ a b) : u ∈ affineSpan ℝ ({a,b} : Set ℂ) := by
    apply convexHull_subset_affineSpan _
    simpa only [convexHull_pair] using hu
  have heq := affineSpan_pair_eq_of_mem_of_mem_of_ne (hspan z hz) (hspan w hw) hzw
  have ha : a ∈ affineSpan ℝ ({z,w} : Set ℂ) := by
    rw [heq]
    exact left_mem_affineSpan_pair ℝ a b
  have hb : b ∈ affineSpan ℝ ({z,w} : Set ℂ) := by
    rw [heq]
    exact right_mem_affineSpan_pair ℝ a b
  exact ⟨im_constant_on_line hzc hwc a ha,im_constant_on_line hzc hwc b hb⟩

theorem affine_zero_inside_interval {L : ℝ →ᵃ[ℝ] ℝ} {a b x : ℝ}
    (hax : a < x) (hxb : x < b) (ha : 0 ≤ L a) (hb : 0 ≤ L b) (hx : L x = 0) :
    L a = 0 ∧ L b = 0 := by
  let t := (x-a)/(b-a)
  have hab : 0 < b-a := sub_pos.mpr (hax.trans hxb)
  have ht : 0 < t := div_pos (sub_pos.mpr hax) hab
  have ht1 : t < 1 := (div_lt_one hab).mpr (by linarith)
  have hline : AffineMap.lineMap a b t = x := by
    rw [AffineMap.lineMap_apply_ring']
    dsimp [t]
    field_simp [ne_of_gt hab]
    ring
  have heq := L.apply_lineMap a b t
  rw [hline,hx,AffineMap.lineMap_apply_ring] at heq
  constructor
  · have hn : 0 ≤ t * L b := mul_nonneg ht.le hb
    have he : (1-t)*L a = 0 := by
      have hn' := mul_nonneg (sub_pos.mpr ht1).le ha
      linarith
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (sub_pos.mpr ht1))
  · have hn : 0 ≤ (1-t) * L a := mul_nonneg (sub_pos.mpr ht1).le ha
    have he : t*L b = 0 := by
      have hn' := mul_nonneg ht.le hb
      linarith
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt ht)

namespace Triangle

variable (T : Triangle)

theorem interior_nonempty : (interior T.carrier).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  exact T.basis.tot

theorem generic_slice_interior_nonempty (c : ℝ) (hgeneric : ∀ i, (T.point i).im ≠ c)
    (hne : (horizontalSlice T.carrier c).Nonempty) :
    (horizontalPoint c ⁻¹' interior T.carrier).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  have hlower : ∃ i, (T.point i).im < c := by
    by_contra! h
    have hstrict : ∀ i, c < (T.point i).im := fun i => lt_of_le_of_ne (h i) (hgeneric i).symm
    have hsub : T.carrier ⊆ {z | c < z.im} := by
      apply convexHull_min
      · rintro z ⟨i,rfl⟩
        exact hstrict i
      · exact convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear c
    have hbad := hsub hx
    simpa only [Set.mem_setOf_eq,horizontalPoint_im,lt_self_iff_false] using hbad
  have hupper : ∃ i, c < (T.point i).im := by
    by_contra! h
    have hstrict : ∀ i, (T.point i).im < c := fun i => lt_of_le_of_ne (h i) (hgeneric i)
    have hsub : T.carrier ⊆ {z | z.im < c} := by
      apply convexHull_min
      · rintro z ⟨i,rfl⟩
        exact hstrict i
      · exact convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear c
    have hbad := hsub hx
    simpa only [Set.mem_setOf_eq,horizontalPoint_im,lt_self_iff_false] using hbad
  obtain ⟨i,hi⟩ := hlower
  obtain ⟨j,hj⟩ := hupper
  exact convex_interior_horizontalSlice_nonempty (convex_convexHull ℝ _) T.interior_nonempty
    (subset_convexHull ℝ _ (Set.mem_range_self i))
    (subset_convexHull ℝ _ (Set.mem_range_self j)) hi hj

theorem generic_slice_inf_lt_sup (c : ℝ) (hgeneric : ∀ i, (T.point i).im ≠ c)
    (hne : (horizontalSlice T.carrier c).Nonempty) :
    sInf (horizontalSlice T.carrier c) < sSup (horizontalSlice T.carrier c) :=
  horizontalSlice_inf_lt_sup T.compact_carrier (convex_convexHull ℝ _) c
    (T.generic_slice_interior_nonempty c hgeneric hne)

theorem slice_between_mem_interior (c : ℝ) (hgeneric : ∀ i, (T.point i).im ≠ c)
    {a b x : ℝ} (ha : horizontalPoint c a ∈ T.carrier)
    (hb : horizontalPoint c b ∈ T.carrier) (hax : a < x) (hxb : x < b) :
    horizontalPoint c x ∈ interior T.carrier := by
  have hsection := convex_horizontalSlice (convex_convexHull ℝ (Set.range T.point)) c
  have hx : horizontalPoint c x ∈ T.carrier :=
    (hsection.ordConnected.out ha hb) ⟨hax.le,hxb.le⟩
  rw [T.mem_interior_iff]
  intro k
  have hnonneg := (T.mem_carrier_iff _).mp hx k
  apply lt_of_le_of_ne hnonneg
  intro hk
  have hzero : T.coord k (horizontalPoint c x) = 0 := hk.symm
  let L : ℝ →ᵃ[ℝ] ℝ := (T.coord k).comp (horizontalAffine c)
  have hab0 := affine_zero_inside_interval (L := L) hax hxb
    ((T.mem_carrier_iff _).mp ha k) ((T.mem_carrier_iff _).mp hb k) hzero
  have hex : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases k
    · exact ⟨1,2,by decide,by decide,by decide⟩
    · exact ⟨0,2,by decide,by decide,by decide⟩
    · exact ⟨0,1,by decide,by decide,by decide⟩
  obtain ⟨i,j,hij,hik,hjk⟩ := hex
  have haedge := (T.mem_edge_iff_coord_zero i j k hij hik hjk ha).mpr hab0.1
  have hbedge := (T.mem_edge_iff_coord_zero i j k hij hik hjk hb).mpr hab0.2
  have habne : horizontalPoint c a ≠ horizontalPoint c b := by
    intro h
    have := congrArg Complex.re h
    simp only [horizontalPoint_re] at this
    exact (hax.trans hxb).ne this
  have him := segment_endpoints_im_eq_of_two_points haedge hbedge habne
    (horizontalPoint_im c a) (horizontalPoint_im c b)
  exact hgeneric i him.1

theorem slice_interval_interior_eq (c : ℝ) (hgeneric : ∀ i, (T.point i).im ≠ c)
    (hne : (horizontalSlice T.carrier c).Nonempty) :
    horizontalPoint c ⁻¹' interior T.carrier =
      Ioo (sInf (horizontalSlice T.carrier c)) (sSup (horizontalSlice T.carrier c)) := by
  ext x
  constructor
  · intro hx
    have hx' := interior_horizontalSlice_of_interior hx
    rwa [horizontalSlice_eq_Icc T.compact_carrier (convex_convexHull ℝ _) c hne,
      interior_Icc] at hx'
  · rintro ⟨hlo,hhi⟩
    exact T.slice_between_mem_interior c hgeneric
      ((compact_horizontalSlice T.compact_carrier c).sInf_mem hne)
      ((compact_horizontalSlice T.compact_carrier c).sSup_mem hne) hlo hhi

end Triangle

end NormalProjective.Planar

/-! ## DrawingTriangles -/

/-! The actual image triangles of a vertex drawing. -/

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

def faceEnumeration (s : T.Face) : Fin 3 ≃ s.val :=
  (Fintype.equivFinOfCardEq (by simpa using T.face_card s.val s.property)).symm

def drawingTriangle (q : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (s : T.Face) : Triangle where
  point i := q (T.faceEnumeration s i).val
  independent := (hind s).comp_embedding (T.faceEnumeration s).toEmbedding

theorem drawingTriangle_carrier (q : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (s : T.Face) : (T.drawingTriangle q hind s).carrier = simplex q s.val := by
  unfold Triangle.carrier simplex
  congr 1
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(T.faceEnumeration s i).val,(T.faceEnumeration s i).property,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨i,hi⟩ := (T.faceEnumeration s).surjective ⟨v,hv⟩
    refine ⟨i,?_⟩
    change q (T.faceEnumeration s i).val = q v
    rw [hi]

theorem drawingTriangle_generic (q : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (c : ℝ) (hgeneric : ∀ v, (q v).im ≠ c) (s : T.Face) :
    ∀ i, ((T.drawingTriangle q hind s).point i).im ≠ c :=
  fun i => hgeneric _

theorem drawing_cell_subset (q : V → ℂ) {S : Set ℂ} (hS : Convex ℝ S)
    (hvertices : ∀ v, q v ∈ S) (s : T.Face) : simplex q s.val ⊆ S := by
  apply convexHull_min
  · rintro z ⟨v,hv,rfl⟩
    exact hvertices v
  · exact hS

end Triangulation

end NormalProjective.Planar

/-! ## DrawingSubfaces -/

/-! Local subface intersections before global injectivity is known. -/

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem independent_subface_intersection (q : V → ℂ) {s a b : Finset V}
    (hs : AffineIndependent ℝ (fun v : s => q v.val)) (ha : a ⊆ s) (hb : b ⊆ s) :
    simplex q a ∩ simplex q b = simplex q (a ∩ b) := by
  classical
  have hind : AffineIndependent ℝ ((↑) : (s.image q) → ℂ) := by
    have hr := hs.range
    have hrange : Set.range (fun v : s => q v.val) = (s.image q : Set ℂ) := by
      ext z
      simp
    change AffineIndependent ℝ (fun x : ↥(s.image q : Set ℂ) => (x : ℂ))
    rw [← hrange]
    exact hr
  have hinj : Set.InjOn q (s : Set V) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hs.injective (show q (⟨x,hx⟩ : s).val = q (⟨y,hy⟩ : s).val from hxy))
  have h := hind.convexHull_inter (Finset.image_subset_image ha) (Finset.image_subset_image hb)
  have hu : Set.InjOn q ((a : Set V) ∪ (b : Set V)) := hinj.mono (by
    intro v hv
    exact hv.elim (fun h => ha h) (fun h => hb h))
  rw [← Finset.coe_inter,← Finset.image_inter_of_injOn a b hu] at h
  simpa only [simplex,Finset.coe_image] using h.symm

theorem two_edges_eq_of_intersection_away_vertices (q : V → ℂ) {s a b : Finset V}
    (hs : AffineIndependent ℝ (fun v : s => q v.val))
    (ha : a ⊆ s) (hb : b ⊆ s) (hca : a.card = 2) (hcb : b.card = 2)
    {z : ℂ} (hza : z ∈ simplex q a) (hzb : z ∈ simplex q b)
    (hzv : ∀ v, z ≠ q v) : a = b := by
  have hz : z ∈ simplex q (a ∩ b) := by
    rw [← independent_subface_intersection q hs ha hb]
    exact ⟨hza,hzb⟩
  have hcard : 2 ≤ (a ∩ b).card := by
    by_contra hn
    have hle : (a ∩ b).card ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (a ∩ b).card with hzcard | hpos
    · have he : a ∩ b = ∅ := Finset.card_eq_zero.mp hzcard
      simpa [he,simplex] using hz
    · have hone : (a ∩ b).card = 1 := by omega
      obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hone
      exact hzv v (by simpa [hv,simplex] using hz)
  have hia : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hib : a ∩ b = b := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hia.symm.trans hib

end NormalProjective.Planar


/-! Read-only actual-body audit; generated from Verify.lean. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`planar_geometry]
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool := localModules.contains (moduleOf n)
  let names := env.checked.get.constants.foldStage2
    (fun ns n _ => ns.push n) (#[] : Array Name)
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing imported declaration {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let ctorDeps := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ ctorDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved library-boundary axiom {ax} in {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("lean_version", toJson "4.35.0"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("local_modules", toJson (localModules.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/PlanarGeometry_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
