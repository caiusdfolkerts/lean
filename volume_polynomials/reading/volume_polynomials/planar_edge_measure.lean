module

public import VolumePolynomials.PlanarCornerInequality
public import VolumePolynomials.MixedFacetIdentity
public import VolumePolynomials.BodyCentering

@[expose] public section
set_option autoImplicit false

/-! # The finite edge measure of an actual planar polytope

The edge vectors are extracted from the genuine facet first-variation formula.
Their defining identity concerns mixed areas of all actual test bodies. The
construction theorem proves that identity for every positive-area finite hull;
it is not an additional hypothesis on the paper's bodies.
-/

noncomputable section
open Set MeasureTheory Module
open scoped BigOperators Pointwise

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner PolytopeGeometry OAI.Paper092

def normal (e : Plane) : Plane →L[ℝ] ℝ :=
  e.2 • ContinuousLinearMap.fst ℝ ℝ ℝ - e.1 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem normal_apply (e x : Plane) : normal e x = e.2 * x.1 - e.1 * x.2 := rfl

def edgeOfFunctional (l : Plane →L[ℝ] ℝ) : Plane := (-l (0, 1), l (1, 0))

theorem functional_coordinates (l : Plane →L[ℝ] ℝ) (x : Plane) :
    l x = x.1 * l (1, 0) + x.2 * l (0, 1) := by
  first
  | have hx : x = x.1 • ((1, 0) : Plane) + x.2 • ((0, 1) : Plane) := by
      first
      | ext <;> simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, smul_eq_mul]

@[simp] theorem normal_edgeOfFunctional (l : Plane →L[ℝ] ℝ) :
    normal (edgeOfFunctional l) = l := by
  first
  | apply ContinuousLinearMap.ext
    intro x
    rw [normal_apply]
    dsimp only [edgeOfFunctional]
    rw [functional_coordinates l x]
    ring

theorem support_smul_functional (A : Set Plane) (l : Plane →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    SupportGeometry.support A (r • l) = r * SupportGeometry.support A l := by
  first
  | unfold SupportGeometry.support
    have he : (r • l) '' A = r • (l '' A) := by
      first
      | ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨l x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
    rw [he, Real.sSup_smul_of_nonneg hr]
    rfl

/-- Literal first-variation representation of mixed area by finitely many
oriented vectors. Zero vectors and repeated directions are allowed. -/
def Represents {ι : Type*} [Fintype ι] (P : ConvexBody Plane) (e : ι → Plane) : Prop :=
  ∀ A : ConvexBody Plane,
    2 * mixedArea volume A P = ∑ i, SupportGeometry.support (A : Set Plane) (normal (e i))

theorem exists_representation_centered (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (hint : (0 : Plane) ∈ interior (P : Set Plane)) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | classical
    let K : Fin 1 → ConvexBody Plane := fun _ => P
    have h0 : ∀ j, (0 : Plane) ∈ K j := fun _ => interior_subset hint
    have hsum : (∑ j, (K j : Set Plane)) = (P : Set Plane) := by simp [K]
    have hfull : (interior (∑ j, (K j : Set Plane))).Nonempty := by
      first
      | rw [hsum]
        exact ⟨0, hint⟩
    obtain ⟨D⟩ := exists_fixedFacets (fun j => (K j : Set Plane)) (fun _ => hP)
      (fun _ => P.nonempty) hfull
    choose v hv using fun i => LinearFrame.exists_unit_value (D.normal i) (D.normal_ne_zero i)
    let w : Fin D.count → ℝ := fun i => facetFrameFactor (D.normal i) (v i) (hv i) *
      mixedVolume (kernelMeasure (D.normal i))
        (fun j => kernelBody (K j) (D.normal i) (v i) (hv i))
    have hw (i) : 0 ≤ w i := mul_nonneg (facetFrameFactor_nonneg _ _ _)
      (mixedVolume_nonnegative _ _)
    refine ⟨D.count, fun i => edgeOfFunctional (w i • D.normal i), ?_⟩
    intro A
    have he : Fin.cons A K = ![A, P] := by
      first
      | funext i
        fin_cases i <;> rfl
    have h := mixedVolume_facet_identity K D h0 (by rwa [hsum]) v hv A
    norm_num only [Nat.cast_add, Nat.cast_one, he] at h
    change 2 * mixedArea volume A P = _ at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [normal_edgeOfFunctional, support_smul_functional _ _ (hw i)]
    dsimp only [w]
    ring

theorem Represents.translate {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) (v : Plane) : Represents (translateBody v P) e := by
  first
  | intro A
    rw [mixedArea_translate_right]
    exact h A

theorem exists_representation_of_interior (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (hint : (interior (P : Set Plane)).Nonempty) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | classical
    obtain ⟨p, hp⟩ := hint
    let Q := translateBody (-p) P
    have hQ : IsFiniteHull (Q : Set Plane) := isFiniteHull_translateBody hP (-p)
    have hQint : (0 : Plane) ∈ interior (Q : Set Plane) := by
      first
      | dsimp only [Q]
        rw [coe_translateBody, interior_vadd]
        exact ⟨p, hp, neg_add_cancel p⟩
    obtain ⟨n, e, he⟩ := exists_representation_centered Q hQ hQint
    refine ⟨n, e, ?_⟩
    have h := he.translate p
    simpa only [Q, translateBody_translate, add_neg_cancel, translateBody_zero] using h

/-- Every polygon needed in the positive-area coefficient slice has a proved
finite edge representation. -/
theorem exists_representation (P : ConvexBody Plane)
    (hP : IsFiniteHull (P : Set Plane)) (harea : 0 < volume.real (P : Set Plane)) :
    ∃ n : ℕ, ∃ e : Fin n → Plane, Represents P e := by
  first
  | have hpos : 0 < volume (P : Set Plane) := (ENNReal.toReal_pos_iff.mp harea).1
    have hint : (interior (P : Set Plane)).Nonempty := by
      first
      | have hne : volume (interior (P : Set Plane)) ≠ 0 := by
          rw [measure_interior_of_null_frontier (P.convex.addHaar_frontier volume)]
          exact hpos.ne'
        apply Set.nonempty_iff_ne_empty.mpr
        intro hempty
        apply hne
        rw [hempty, measure_empty]
    exact exists_representation_of_interior P hP hint

theorem support_pointBody (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (pointBody v : Set Plane) l = l v := by
  first
  | simp only [SupportGeometry.support, coe_pointBody, Set.image_singleton, csSup_singleton]

theorem Represents.balance {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, (e i).1) = 0 ∧ (∑ i, (e i).2) = 0 := by
  first
  | have hx := h (pointBody (0, 1))
    have hy := h (pointBody (1, 0))
    simp only [mixedArea_point_left, mul_zero, support_pointBody, normal_apply,
      mul_zero, mul_one, zero_sub, sub_zero, Finset.sum_neg_distrib] at hx hy
    constructor <;> linarith

theorem support_segmentBody (v : Plane) (l : Plane →L[ℝ] ℝ) :
    SupportGeometry.support (PlanarCorner.segmentBody v : Set Plane) l = |l v| / 2 := by
  first
  | apply le_antisymm
    · apply SupportGeometry.support_le (PlanarCorner.segmentBody v).nonempty l
      rintro x ⟨t, ht, rfl⟩
      have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
      have hmul := mul_le_mul_of_nonneg_right ht' (abs_nonneg (l v))
      have hle : t * l v ≤ |t| * |l v| := by simpa only [abs_mul] using le_abs_self (t * l v)
      simp only [map_smul, smul_eq_mul]
      nlinarith
    · by_cases hv : 0 ≤ l v
      · have hp : (1 / 2 : ℝ) • v ∈ PlanarCorner.segmentBody v :=
          ⟨1 / 2, ⟨by norm_num, le_rfl⟩, rfl⟩
        have h := SupportGeometry.le_support (PlanarCorner.segmentBody v).isCompact l hp
        simpa only [map_smul, smul_eq_mul, abs_of_nonneg hv, div_eq_mul_inv,
          one_mul, mul_comm] using h
      · have hp : (-(1 / 2) : ℝ) • v ∈ PlanarCorner.segmentBody v :=
          ⟨-(1 / 2), ⟨le_rfl, by norm_num⟩, rfl⟩
        have h := SupportGeometry.le_support (PlanarCorner.segmentBody v).isCompact l hp
        simp only [map_smul, smul_eq_mul] at h
        rw [abs_of_neg (lt_of_not_ge hv)]
        nlinarith

theorem support_unitX (e : Plane) :
    SupportGeometry.support (unitX : Set Plane) (normal e) = |e.2| / 2 := by
  first
  | simpa only [unitX, normal_apply, mul_one, mul_zero, sub_zero] using
      support_segmentBody (1, 0) (normal e)

theorem support_unitY (e : Plane) :
    SupportGeometry.support (unitY : Set Plane) (normal e) = |e.1| / 2 := by
  first
  | simpa only [unitY, normal_apply, mul_one, mul_zero, zero_sub, abs_neg] using
      support_segmentBody (0, 1) (normal e)

theorem Represents.total_variation {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, |(e i).1|) = 2 * width P ∧ (∑ i, |(e i).2|) = 2 * height P := by
  first
  | have hx := h unitY
    have hy := h unitX
    rw [mixedArea_symm, twice_mixedArea_unitY] at hx
    rw [mixedArea_symm, twice_mixedArea_unitX] at hy
    simp only [support_unitY, support_unitX, ← Finset.sum_div] at hx hy
    constructor <;> linarith

theorem twice_positive_part (x : ℝ) : 2 * max x 0 = |x| + x := by
  first
  | rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]
      ring
    · rw [max_eq_right hx, abs_of_nonpos hx]
      ring

theorem Represents.signed_variation {ι : Type*} [Fintype ι] {P : ConvexBody Plane}
    {e : ι → Plane} (h : Represents P e) :
    (∑ i, max (e i).1 0) = width P ∧ (∑ i, max (e i).2 0) = height P ∧
    (∑ i, max (-(e i).1) 0) = width P ∧ (∑ i, max (-(e i).2) 0) = height P := by
  first
  | have hbal := h.balance
    have hvar := h.total_variation
    have hp (f : ι → ℝ) : 2 * (∑ i, max (f i) 0) = (∑ i, |f i|) + ∑ i, f i := by
      first
      | rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => twice_positive_part (f i))
    have hxp := hp (fun i => (e i).1)
    have hyp := hp (fun i => (e i).2)
    have hxn := hp (fun i => -(e i).1)
    have hyn := hp (fun i => -(e i).2)
    simp only [abs_neg, Finset.sum_neg_distrib] at hxn hyn
    constructor
    · linarith [hbal.1, hvar.1]
    constructor
    · linarith [hbal.2, hvar.2]
    constructor
    · linarith [hbal.1, hvar.1]
    · linarith [hbal.2, hvar.2]

end VolumePolynomials.PlanarEdges
