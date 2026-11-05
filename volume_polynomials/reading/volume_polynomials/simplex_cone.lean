module

public import VolumePolynomials.SimplexMoments
public import VolumePolynomials.ConvexFibersBasic
public import VolumePolynomials.BodyOperations

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# The actual cone realizing the lifted slice

The cone is the image of a compact planar body times a coordinate simplex
under the explicit map `(a,y) ↦ (ρ(y) • a,y)`. Its convexity, exact fibers,
and finite convex-hull description are proved, including the zero-height
faces. These are geometric assertions about subsets, not assumed data in
a realization structure.
-/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.SimplexCone

open SimplexCoordinates ConvexFibers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def coneSet (A : ConvexBody E) (k : ℕ) : Set (E × Space k) :=
  (fun p : E × Space k => (coneHeight p.2 • p.1, p.2)) ''
    ((A : Set E) ×ˢ simplex k)

theorem coneSet_compact (A : ConvexBody E) (k : ℕ) : IsCompact (coneSet A k) :=
  (A.isCompact.prod (simplex_compact k)).image
    (((continuous_coneHeight k).comp continuous_snd).smul continuous_fst |>.prodMk continuous_snd)

theorem coneSet_nonempty (A : ConvexBody E) (k : ℕ) : (coneSet A k).Nonempty :=
  (A.nonempty.prod ⟨0, zero_mem_simplex k⟩).image _

theorem coneSet_convex (A : ConvexBody E) (k : ℕ) : Convex ℝ (coneSet A k) := by
  first
  | rintro _ ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩ _ ⟨⟨y, v⟩, ⟨hy, hv⟩, rfl⟩ a b ha hb hab
    let z : Space k := a • u + b • v
    let r : ℝ := coneHeight z
    have hz : z ∈ simplex k := simplex_convex k hu hv ha hb hab
    have hru : 0 ≤ coneHeight u := coneHeight_nonnegative hu
    have hrv : 0 ≤ coneHeight v := coneHeight_nonnegative hv
    have hr : 0 ≤ r := coneHeight_nonnegative hz
    have hre : r = a * coneHeight u + b * coneHeight v := coneHeight_affine u v hab
    by_cases hr0 : r = 0
    · have hu0 : a * coneHeight u = 0 := by nlinarith
      have hv0 : b * coneHeight v = 0 := by nlinarith
      obtain ⟨q, hq⟩ := A.nonempty
      refine ⟨(q, z), ⟨hq, hz⟩, Prod.ext ?_ rfl⟩
      change r • q = a • (coneHeight u • x) + b • (coneHeight v • y)
      simp only [hr0, zero_smul, smul_smul, hu0, hv0, add_zero]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      let c : ℝ := a * coneHeight u / r
      let d : ℝ := b * coneHeight v / r
      have hc : 0 ≤ c := div_nonneg (mul_nonneg ha hru) hr
      have hd : 0 ≤ d := div_nonneg (mul_nonneg hb hrv) hr
      have hcd : c + d = 1 := by
        first
        | dsimp only [c, d]
          rw [← add_div, ← hre, div_self hr0]
      have hrc : r * c = a * coneHeight u := by dsimp [c]; field_simp
      have hrd : r * d = b * coneHeight v := by dsimp [d]; field_simp
      refine ⟨(c • x + d • y, z), ⟨A.convex hx hy hc hd hcd, hz⟩, Prod.ext ?_ rfl⟩
      change r • (c • x + d • y) = a • (coneHeight u • x) + b • (coneHeight v • y)
      simp only [smul_add, smul_smul, hrc, hrd]

def coneBody (A : ConvexBody E) (k : ℕ) : ConvexBody (E × Space k) :=
  ⟨coneSet A k, coneSet_convex A k, coneSet_compact A k, coneSet_nonempty A k⟩

theorem cone_projection (A : ConvexBody E) (k : ℕ) :
    projection (coneBody A k) = simplex k := by
  first
  | ext y
    constructor
    · rintro ⟨_, ⟨⟨a, z⟩, ⟨ha, hz⟩, rfl⟩, rfl⟩
      exact hz
    · intro hy
      obtain ⟨a, ha⟩ := A.nonempty
      exact ⟨(coneHeight y • a, y), ⟨(a, y), ⟨ha, hy⟩, rfl⟩, rfl⟩

theorem cone_fiber (A : ConvexBody E) (k : ℕ) {y : Space k} (hy : y ∈ simplex k) :
    fiberSet (coneBody A k) y = coneHeight y • (A : Set E) := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, z⟩, ⟨ha, hz⟩, heq⟩
      have hzy : z = y := congrArg Prod.snd heq
      subst z
      exact ⟨a, ha, congrArg Prod.fst heq⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a, y), ⟨ha, hy⟩, rfl⟩

theorem cone_fiberBody (A : ConvexBody E) (k : ℕ) {y : Space k}
    (hy : y ∈ simplex k) :
    fiberBody (coneBody A k) y = coneHeight y • A := by
  first
  | apply ConvexBody.ext
    rw [coe_fiberBody _ (by rwa [cone_projection]), cone_fiber A k hy]
    rfl

def baseMap (k : ℕ) : E →L[ℝ] E × Space k :=
  (k + 1 : ℝ) • ContinuousLinearMap.inl ℝ E (Space k)

def apex (k : ℕ) (i : Fin k) : E × Space k := (0, Pi.single i 1)

theorem base_mem_cone (A : ConvexBody E) (k : ℕ) {a : E} (ha : a ∈ A) :
    baseMap k a ∈ coneSet A k := by
  first
  | refine ⟨(a, 0), ⟨ha, zero_mem_simplex k⟩, ?_⟩
    simp [baseMap, coneHeight, height]

theorem apex_mem_cone (A : ConvexBody E) (k : ℕ) (i : Fin k) :
    apex (E := E) k i ∈ coneSet A k := by
  first
  | obtain ⟨a, ha⟩ := A.nonempty
    refine ⟨(a, Pi.single i 1), ⟨ha, coordinate_mem_simplex i⟩, ?_⟩
    simp [apex, coneHeight, height]

/-- The convex-hull description in (6.5), with every base point retained. -/
theorem cone_eq_convexHull (A : ConvexBody E) (k : ℕ) :
    coneSet A k = convexHull ℝ
      ((baseMap k '' (A : Set E)) ∪ range (apex (E := E) k)) := by
  first
  | apply le_antisymm
    · rintro _ ⟨⟨a, y⟩, ⟨ha, hy⟩, rfl⟩
      let w : Fin (k + 1) → ℝ := Fin.cons (height y) y
      let v : Fin (k + 1) → E × Space k := Fin.cons (baseMap k a) (apex k)
      apply mem_convexHull_of_exists_fintype w v
      · intro i
        cases i using Fin.cases with
        | zero => exact height_nonnegative hy
        | succ i => exact hy.1 i
      · simp [w, Fin.sum_univ_succ, height]
      · intro i
        cases i using Fin.cases with
        | zero => exact Or.inl ⟨a, ha, rfl⟩
        | succ i => exact Or.inr (mem_range_self i)
      · apply Prod.ext
        · simp [w, v, baseMap, apex, Fin.sum_univ_succ, coneHeight, smul_smul, mul_comm,
            Prod.fst_sum]
        · ext j
          simp [w, v, baseMap, apex, Fin.sum_univ_succ, Finset.sum_apply, Pi.single_apply,
            Prod.snd_sum]
    · apply convexHull_min _ (coneSet_convex A k)
      rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact base_mem_cone A k ha
      · exact apex_mem_cone A k i

/-- A finite generating set for the planar body gives a finite generating
set for the lifted cone. This proves the polytope assertion in the converse. -/
theorem cone_finiteHull (A : ConvexBody E) (k : ℕ)
    (hA : PolytopeGeometry.IsFiniteHull (A : Set E)) :
    PolytopeGeometry.IsFiniteHull (coneSet A k) := by
  first
  | obtain ⟨S, hS, hA⟩ := hA
    refine ⟨baseMap k '' S ∪ range (apex (E := E) k),
      (hS.image _).union (Set.finite_range _), ?_⟩
    rw [cone_eq_convexHull, hA]
    have himage : baseMap k '' convexHull ℝ S = convexHull ℝ (baseMap k '' S) := by
      simpa only [ContinuousLinearMap.coe_coe] using
        (baseMap (E := E) k).toLinearMap.image_convexHull S
    rw [himage, convexHull_convexHull_union_left]

end VolumePolynomials.SimplexCone
