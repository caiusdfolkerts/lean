module

public import subfaces
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Order.LeftRight

/-!
# Opposite sides of a shared geometric edge

The proof is elementary: after sending the edge to `[0,1]` in `ℂ`, two third
vertices in the upper half-plane have a common point `1/2 + ε I` in their
triangles for sufficiently small positive `ε`. Thus triangles meeting exactly
in their common edge have third vertices on opposite sides of its line.
-/

@[expose] public section

noncomputable section

namespace NormalProjective.Planar

open Set Finset Filter
open scoped Topology

def edgeNormalize (a b : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := (b-a)⁻¹ * (z-a)
  linear := LinearMap.mul ℝ ℂ (b-a)⁻¹
  map_vadd' z v := by simp only [vadd_eq_add,LinearMap.mul_apply']; ring

def edgeHeight (a b z : ℂ) : ℝ := (edgeNormalize a b z).im

def edgeHeightLinear (a b : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ (b-a)⁻¹)

theorem edgeHeight_eq_linear (a b z : ℂ) :
    edgeHeight a b z = edgeHeightLinear a b z - edgeHeightLinear a b a := by
  simp [edgeHeight,edgeNormalize,edgeHeightLinear,mul_sub]

@[simp] theorem edgeNormalize_left (a b : ℂ) : edgeNormalize a b a = 0 := by
  simp [edgeNormalize]

@[simp] theorem edgeNormalize_right {a b : ℂ} (hab : a ≠ b) : edgeNormalize a b b = 1 := by
  simp [edgeNormalize,sub_ne_zero.mpr hab.symm]

theorem edgeNormalize_injective {a b : ℂ} (hab : a ≠ b) :
    Function.Injective (edgeNormalize a b) := by
  intro x y h
  exact sub_left_injective ((mul_left_cancel₀ (inv_ne_zero (sub_ne_zero.mpr hab.symm))) h)

theorem edgeHeight_swap {a b : ℂ} (hab : a ≠ b) (z : ℂ) :
    edgeHeight b a z = -edgeHeight a b z := by
  have heq : edgeNormalize b a z = 1-edgeNormalize a b z := by
    change (a-b)⁻¹*(z-b) = 1-(b-a)⁻¹*(z-a)
    field_simp [sub_ne_zero.mpr hab,sub_ne_zero.mpr hab.symm]
    ring
  simp [edgeHeight,heq]

theorem mem_line_of_edgeHeight_zero {a b z : ℂ} (hab : a ≠ b)
    (hz : edgeHeight a b z = 0) : z ∈ affineSpan ℝ ({a,b} : Set ℂ) := by
  let r : ℝ := (edgeNormalize a b z).re
  have hnorm : (r : ℂ) = edgeNormalize a b z := by
    apply Complex.ext
    · rfl
    · simpa [edgeHeight] using hz.symm
  have heq : z = r • (b-a) + a := by
    rw [Complex.real_smul,hnorm]
    change z = ((b-a)⁻¹*(z-a))*(b-a)+a
    field_simp [sub_ne_zero.mpr hab.symm]
    ring
  rw [heq]
  exact smul_vsub_vadd_mem_affineSpan_pair r a b

theorem edgeHeight_zero_on_segment {a b z : ℂ}
    (hz : z ∈ segment ℝ a b) : edgeHeight a b z = 0 := by
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  have heq : edgeNormalize a b (r • a + s • b) = s • edgeNormalize a b b := by
    have hr' : r = 1-s := by linarith
    rw [hr']
    simp only [edgeNormalize,AffineMap.coe_mk,Complex.real_smul]
    push_cast
    ring
  by_cases hab : a = b
  · subst b
    simp [edgeHeight,edgeNormalize]
  · change (edgeNormalize a b (r • a+s • b)).im = 0
    rw [heq,edgeNormalize_right hab]
    simp

theorem normalized_triangle_mem (x : ℂ) (ε : ℝ)
    (hx : 0 < x.im) (hε : 0 < ε)
    (ha : 0 < (1/2:ℝ) + ε / x.im * (x.re-1))
    (hb : 0 < (1/2:ℝ) - ε / x.im * x.re) :
    (1/2:ℂ) + (ε : ℂ)*Complex.I ∈ convexHull ℝ ({0,1,x} : Set ℂ) := by
  let weights : Fin 3 → ℝ :=
    ![(1/2:ℝ)+ε/x.im*(x.re-1),(1/2:ℝ)-ε/x.im*x.re,ε/x.im]
  let points : Fin 3 → ℂ := ![0,1,x]
  have hnonneg : ∀ i ∈ (univ : Finset (Fin 3)), 0 ≤ weights i := by
    intro i _
    fin_cases i
    · exact ha.le
    · exact hb.le
    · exact (div_pos hε hx).le
  have hsum : ∑ i : Fin 3, weights i = 1 := by
    simp [weights,Fin.sum_univ_succ]
    ring
  have hp : ∀ i ∈ (univ : Finset (Fin 3)), points i ∈ convexHull ℝ ({0,1,x} : Set ℂ) := by
    intro i _
    apply subset_convexHull ℝ _
    fin_cases i <;> simp [points]
  have hmem := (convex_convexHull ℝ ({0,1,x} : Set ℂ)).sum_mem hnonneg hsum hp
  have heq : ∑ i : Fin 3, weights i • points i = (1/2:ℂ)+(ε:ℂ)*Complex.I := by
    apply Complex.ext <;> simp [weights,points,Fin.sum_univ_succ]
    field_simp [ne_of_gt hx]
  rwa [heq] at hmem

theorem normalized_triangles_same_side_intersect {x y : ℂ}
    (hx : 0 < x.im) (hy : 0 < y.im) :
    ∃ z, z ∈ convexHull ℝ ({0,1,x} : Set ℂ) ∩
      convexHull ℝ ({0,1,y} : Set ℂ) ∧ 0 < z.im := by
  have haux : ∀ z : ℂ, ∀ᶠ ε : ℝ in 𝓝 0,
      0 < (1/2:ℝ)+ε/z.im*(z.re-1) ∧ 0 < (1/2:ℝ)-ε/z.im*z.re := by
    intro z
    have hca : Continuous (fun ε : ℝ => (1/2:ℝ)+ε/z.im*(z.re-1)) := by fun_prop
    have hcb : Continuous (fun ε : ℝ => (1/2:ℝ)-ε/z.im*z.re) := by fun_prop
    have ha : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (1/2:ℝ)+ε/z.im*(z.re-1) :=
      (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (0:ℝ))) hca).mem_nhds (by norm_num)
    have hb : ∀ᶠ ε : ℝ in 𝓝 0, 0 < (1/2:ℝ)-ε/z.im*z.re :=
      (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (0:ℝ))) hcb).mem_nhds (by norm_num)
    exact ha.and hb
  obtain ⟨ε,hε,hxε,hyε⟩ := ((haux x).and (haux y)).exists_gt
  refine ⟨(1/2:ℂ)+(ε:ℂ)*Complex.I,
    ⟨normalized_triangle_mem x ε hx hε hxε.1 hxε.2,
      normalized_triangle_mem y ε hy hε hyε.1 hyε.2⟩,?_⟩
  simpa using hε

theorem third_vertex_negative_of_triangle_intersection {a b x y : ℂ}
    (hab : a ≠ b) (hx : 0 < edgeHeight a b x)
    (hy : edgeHeight a b y ≠ 0)
    (hinter : convexHull ℝ ({a,b,x} : Set ℂ) ∩
      convexHull ℝ ({a,b,y} : Set ℂ) ⊆ segment ℝ a b) :
    edgeHeight a b y < 0 := by
  by_contra h
  have hyp : 0 < edgeHeight a b y := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hy)
  obtain ⟨z,hz,hzim⟩ := normalized_triangles_same_side_intersect hx hyp
  have hzx := hz.1
  have hzy := hz.2
  have hximage : convexHull ℝ ({0,1,edgeNormalize a b x} : Set ℂ) =
      edgeNormalize a b '' convexHull ℝ ({a,b,x} : Set ℂ) := by
    rw [(edgeNormalize a b).image_convexHull]
    simp [edgeNormalize_right hab]
  have hyimage : convexHull ℝ ({0,1,edgeNormalize a b y} : Set ℂ) =
      edgeNormalize a b '' convexHull ℝ ({a,b,y} : Set ℂ) := by
    rw [(edgeNormalize a b).image_convexHull]
    simp [edgeNormalize_right hab]
  rw [hximage] at hzx
  rw [hyimage] at hzy
  obtain ⟨zx,hzx,rfl⟩ := hzx
  obtain ⟨zy,hzy,heq⟩ := hzy
  have heq' : zy = zx := edgeNormalize_injective hab heq
  subst zy
  have hz0 := edgeHeight_zero_on_segment (hinter ⟨hzx,hzy⟩)
  exact hzim.ne' hz0

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem face_third_height_ne_zero {s : Finset V} (hs : s ∈ T.faces)
    {a b v : V} (ha : a ∈ s) (hb : b ∈ s) (hv : v ∈ s)
    (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b) :
    edgeHeight (T.point a) (T.point b) (T.point v) ≠ 0 := by
  intro hzero
  have hline := mem_line_of_edgeHeight_zero (T.point_injective.ne hab) hzero
  let a' : s := ⟨a,ha⟩
  let b' : s := ⟨b,hb⟩
  let v' : s := ⟨v,hv⟩
  have hmem : T.point v ∈ affineSpan ℝ
      ((fun i : s => T.point i) '' ({a',b'} : Set s)) := by
    simpa [a',b'] using hline
  have hm := (T.face_independent s hs).mem_affineSpan_iff v' ({a',b'} : Set s) |>.mp hmem
  simp only [mem_insert_iff,mem_singleton_iff] at hm
  rcases hm with h | h
  · exact hva (congrArg Subtype.val h)
  · exact hvb (congrArg Subtype.val h)

end Triangulation

end NormalProjective.Planar
