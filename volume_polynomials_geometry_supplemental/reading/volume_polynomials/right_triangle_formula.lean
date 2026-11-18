module

public import VolumePolynomials.PlanarEdgeMeasure
public import VolumePolynomials.PlanarFacetFormula
public import VolumePolynomials.PlanarCornerOptimizer
public import Mathlib.Analysis.Convex.Combination

@[expose] public section
set_option autoImplicit false

/-! # The exact three-term mixed-area formula for a right triangle

The three facet weights are determined from actual first variation, translation
balance and coordinate extrusion. No unproved triangle-area or surface-area
formula is used.
-/

noncomputable section
open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PolytopeGeometry OAI.Paper092
open PolytopeFirstVariation

def unitTriangle : ConvexBody Plane where
  carrier := {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1}
  convex' := by
    first
    | intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
        add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), ?_⟩
      nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]
  isCompact' := by
    first
    | have hc : IsClosed {x : Plane | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1} :=
        (isClosed_le continuous_const continuous_fst).inter
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
      refine (isCompact_Icc : IsCompact (Icc ((0, 0) : Plane) (1, 1))).of_isClosed_subset hc ?_
      intro x hx
      exact ⟨⟨hx.1, hx.2.1⟩, ⟨by linarith [hx.2.2, hx.2.1], by linarith [hx.2.2, hx.1]⟩⟩
  nonempty' := ⟨(0, 0), by norm_num⟩

@[simp] theorem mem_unitTriangle (x : Plane) :
    x ∈ unitTriangle ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 1 := Iff.rfl

theorem unitTriangle_projections :
    Prod.fst '' (unitTriangle : Set Plane) = Icc (0 : ℝ) 1 ∧
      Prod.snd '' (unitTriangle : Set Plane) = Icc (0 : ℝ) 1 := by
  first
  | constructor
    · ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.1, by linarith [hx.2.1, hx.2.2]⟩
      · intro ht
        exact ⟨(t, 0), ⟨ht.1, le_rfl, by simpa using ht.2⟩, rfl⟩
    · ext t
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx.2.1, by linarith [hx.1, hx.2.2]⟩
      · intro ht
        exact ⟨(0, t), ⟨le_rfl, ht.1, by simpa using ht.2⟩, rfl⟩

@[simp] theorem width_unitTriangle : width unitTriangle = 1 := by
  first
  | rw [width, unitTriangle_projections.1]
    norm_num

@[simp] theorem height_unitTriangle : height unitTriangle = 1 := by
  first
  | rw [height, unitTriangle_projections.2]
    norm_num

def triangleVertices : Fin 3 → Plane := ![(0, 0), (1, 0), (0, 1)]

theorem unitTriangle_eq_convexHull :
    (unitTriangle : Set Plane) = convexHull ℝ (Set.range triangleVertices) := by
  first
  | apply subset_antisymm
    · intro x hx
      apply mem_convexHull_of_exists_fintype
        (![1 - x.1 - x.2, x.1, x.2] : Fin 3 → ℝ) triangleVertices
      · intro i
        fin_cases i
        · change 0 ≤ 1 - x.1 - x.2
          linarith [hx.2.2]
        · change 0 ≤ x.1
          exact hx.1
        · change 0 ≤ x.2
          exact hx.2.1
      · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Fin.sum_univ_zero, add_zero]
        ring
      · exact fun i => Set.mem_range_self i
      · ext <;> simp [triangleVertices, Fin.sum_univ_succ]
    · apply convexHull_min
      · rintro x ⟨i, rfl⟩
        fin_cases i <;> norm_num [triangleVertices, mem_unitTriangle]
      · exact unitTriangle.convex

theorem unitTriangle_finiteHull : IsFiniteHull (unitTriangle : Set Plane) :=
  ⟨Set.range triangleVertices, Set.finite_range _, unitTriangle_eq_convexHull⟩

def centeredTriangle : ConvexBody Plane := translateBody (-(1 / 3), -(1 / 3)) unitTriangle

def triangleNormals : Fin 3 → Plane →L[ℝ] ℝ :=
  ![normal (0, -3), normal (3, 0), normal (-3, 3)]

def triangleRightInverse : Fin 3 → Plane :=
  ![(-(1 / 3), 0), (0, -(1 / 3)), (1 / 3, 0)]

theorem triangle_normal_unit (i : Fin 3) : triangleNormals i (triangleRightInverse i) = 1 := by
  first
  | fin_cases i <;> norm_num [triangleNormals, triangleRightInverse, normal_apply]

theorem triangleNormals_injective : Function.Injective triangleNormals := by
  first
  | intro i j hij
    have hx := congrArg (fun l : Plane →L[ℝ] ℝ => l (1, 0)) hij
    fin_cases i
    all_goals fin_cases j
    all_goals first | rfl | norm_num [triangleNormals, normal_apply] at hx

theorem triangle_halfspace_body :
    HalfspacePyramids.body triangleNormals = (centeredTriangle : Set Plane) := by
  first
  | ext x
    change (∀ i, triangleNormals i x ≤ 1) ↔ x ∈ centeredTriangle
    rw [centeredTriangle, mem_translateBody]
    change (∀ i, triangleNormals i x ≤ 1) ↔
      0 ≤ x.1 - (-(1 / 3)) ∧ 0 ≤ x.2 - (-(1 / 3)) ∧
        (x.1 - (-(1 / 3))) + (x.2 - (-(1 / 3))) ≤ 1
    constructor
    · intro hx
      have h0 := hx 0
      have h1 := hx 1
      have h2 := hx 2
      norm_num [triangleNormals, normal_apply] at h0 h1 h2
      exact ⟨by linarith, by linarith, by linarith⟩
    · intro hx i
      fin_cases i <;> norm_num [triangleNormals, normal_apply] <;>
        linarith [hx.1, hx.2.1, hx.2.2]

def triangleWeight (i : Fin 3) : ℝ :=
  canonicalFacetWeight triangleNormals i (triangleRightInverse i) (triangle_normal_unit i)

theorem triangle_facet_formula (A : ConvexBody Plane) :
    2 * mixedArea volume A centeredTriangle =
      ∑ i, triangleWeight i * SupportGeometry.support (A : Set Plane) (triangleNormals i) :=
  mixedArea_facet_formula centeredTriangle triangleNormals triangleNormals_injective
    triangle_halfspace_body triangleRightInverse triangle_normal_unit A

theorem triangleWeight_value (i : Fin 3) : triangleWeight i = 1 / 3 := by
  first
  | have hx := triangle_facet_formula (pointBody (1, 0))
    have hy := triangle_facet_formula (pointBody (0, 1))
    simp only [mixedArea_point_left, mul_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
      support_pointBody, triangleNormals, Matrix.cons_val_zero, Matrix.cons_val_succ,
      normal_apply, mul_one, mul_zero, zero_sub, sub_zero, add_zero] at hx hy
    have hs := triangle_facet_formula unitX
    rw [mixedArea_symm, twice_mixedArea_unitX, centeredTriangle,
      height_translate, height_unitTriangle] at hs
    norm_num [Fin.sum_univ_succ, triangleNormals, support_unitX] at hs
    norm_num at hx hy
    fin_cases i <;> norm_num <;> linarith

theorem support_third_normal (A : ConvexBody Plane) (e : Plane) :
    (1 / 3 : ℝ) * SupportGeometry.support (A : Set Plane) (normal ((3 : ℝ) • e)) =
      SupportGeometry.support (A : Set Plane) (normal e) := by
  first
  | rw [← support_smul_functional _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.smul_apply, normal_apply, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring

/-- Exact mixed-area functional of the actual unit right triangle. -/
theorem unitTriangle_mixedArea (A : ConvexBody Plane) :
    2 * mixedArea volume A unitTriangle =
      SupportGeometry.support (A : Set Plane) (normal (0, -1)) +
      SupportGeometry.support (A : Set Plane) (normal (1, 0)) +
      SupportGeometry.support (A : Set Plane) (normal (-1, 1)) := by
  first
  | have h := triangle_facet_formula A
    rw [centeredTriangle, mixedArea_translate_right] at h
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, triangleWeight_value,
      triangleNormals, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero] at h
    have h0 := support_third_normal A (0, -1)
    have h1 := support_third_normal A (1, 0)
    have h2 := support_third_normal A (-1, 1)
    have he0 : (3 : ℝ) • ((0, -1) : Plane) = (0, -3) := by ext <;> norm_num
    have he1 : (3 : ℝ) • ((1, 0) : Plane) = (3, 0) := by ext <;> norm_num
    have he2 : (3 : ℝ) • ((-1, 1) : Plane) = (-3, 3) := by ext <;> norm_num
    rw [he0] at h0
    rw [he1] at h1
    rw [he2] at h2
    linarith

end VolumePolynomials.PlanarEdges
