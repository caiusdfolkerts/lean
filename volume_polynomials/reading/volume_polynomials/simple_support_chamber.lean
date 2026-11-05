module

public import VolumePolynomials.PolyhedralBasis
public import VolumePolynomials.BodyContinuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false

/-!
# Open cones of simple support vectors

A chamber fixes the strict sign of every inactive constraint at every
coordinate vertex. Consequently its feasible vertices have the same active
bases. The resulting bodies add exactly by adding their height vectors, and
every vector of real heights is a positive multiple of a difference of two
support vectors in the chamber.
-/

noncomputable section
open Set Filter Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def slack (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ((LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) -
    (l i).toLinearMap.comp (vertexMap l b).toLinearMap).toContinuousLinearMap

@[simp] theorem slack_apply (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (i : ι) (h : ι → ℝ) : slack l b i h = h i - l i (vertexMap l b h) := rfl

theorem slack_eq_zero_of_mem (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    {i : ι} (hi : i ∈ b.val) (h : ι → ℝ) : slack l b i h = 0 := by
  first
  | rw [slack_apply, vertexMap_active l b h ⟨i, hi⟩, sub_self]

theorem slack_ne_zero_of_generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (b : BasisIndex l) {i : ι} (hi : i ∉ b.val) :
    slack l b i h ≠ 0 := by
  first
  | intro hz
    rw [slack_apply] at hz
    have hvi : l i (vertexMap l b h) = h i := (sub_eq_zero.mp hz).symm
    have hs : Function.Surjective (evaluation l (insert i b.val)) := by
      first
      | apply hg
        apply Iff.mpr (mem_compatibleHeights l _ h)
        refine ⟨vertexMap l b h, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hvi
        · exact vertexMap_active l b h ⟨j, hj⟩
    obtain ⟨x, hx⟩ := hs (fun j => if j.val = i then 1 else 0)
    have hbx : coordinates l b x = 0 := by
      first
      | funext j
        have hj : j.val ≠ i := by rintro rfl; exact hi j.property
        have he := congrFun hx ⟨j, Finset.mem_insert_of_mem j.property⟩
        simpa only [evaluation_apply, coordinates_apply, if_neg hj, Pi.zero_apply] using he
    have hx0 : x = 0 := (coordinates l b).injective (by simpa using hbx)
    have he := congrFun hx ⟨i, Finset.mem_insert_self _ _⟩
    simp only [evaluation_apply, hx0, map_zero, if_pos rfl, ite_true, zero_ne_one] at he

def chamber (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) : Set (ι → ℝ) :=
  {h | (∀ i, 0 < h i) ∧
    ∀ b : BasisIndex l, ∀ i ∉ b.val, 0 < slack l b i h₀ * slack l b i h}

theorem isOpen_chamber (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ) :
    IsOpen (chamber l h₀) := by
  first
  | change IsOpen ({h | ∀ i, 0 < h i} ∩
      {h | ∀ b : BasisIndex l, ∀ i, i ∉ b.val →
        0 < slack l b i h₀ * slack l b i h})
    apply IsOpen.inter
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    · simp only [Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro b
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro hi
      have hc : Continuous (fun h : ι → ℝ => slack l b i h₀ * slack l b i h) := by
        first
        | fun_prop
      exact isOpen_lt continuous_const hc

theorem mem_chamber_self (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) (hpos : ∀ i, 0 < h i) : h ∈ chamber l h := by
  first
  | refine ⟨hpos, fun b i hi => ?_⟩
    exact mul_self_pos.mpr (slack_ne_zero_of_generic l h hg b hi)

theorem chamber_add (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h k : ι → ℝ} (hh : h ∈ chamber l h₀) (hk : k ∈ chamber l h₀) :
    h + k ∈ chamber l h₀ := by
  first
  | refine ⟨fun i => add_pos (hh.1 i) (hk.1 i), fun b i hi => ?_⟩
    rw [map_add, mul_add]
    exact add_pos (hh.2 b i hi) (hk.2 b i hi)

theorem chamber_smul (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h : ι → ℝ} (hh : h ∈ chamber l h₀) {r : ℝ} (hr : 0 < r) :
    r • h ∈ chamber l h₀ := by
  first
  | refine ⟨fun i => mul_pos hr (hh.1 i), fun b i hi => ?_⟩
    rw [map_smul, smul_eq_mul, mul_left_comm]
    exact mul_pos hr (hh.2 b i hi)

theorem feasibleBases_eq_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hg : Generic l h₀) {h : ι → ℝ} (hh : h ∈ chamber l h₀) :
    feasibleBases l h = feasibleBases l h₀ := by
  first
  | ext b
    constructor
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b h₀ ⟨i, hi⟩).le
      · have hp := hh.2 b i hi
        have hb' : 0 ≤ slack l b i h := by
          first
          | simpa only [slack_apply] using sub_nonneg.mpr (hb i)
        have hs : 0 ≤ slack l b i h₀ := (pos_of_mul_pos_left hp hb').le
        exact sub_nonneg.mp (by simpa only [slack_apply] using hs)
    · intro hb i
      by_cases hi : i ∈ b.val
      · exact (vertexMap_active l b h ⟨i, hi⟩).le
      · have hp := hh.2 b i hi
        have hb' : 0 ≤ slack l b i h₀ := by
          first
          | simpa only [slack_apply] using sub_nonneg.mpr (hb i)
        have hs : 0 ≤ slack l b i h := (pos_of_mul_pos_right hp hb').le
        exact sub_nonneg.mp (by simpa only [slack_apply] using hs)

theorem active_eq_basis_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) {h : ι → ℝ} (hh : h ∈ chamber l h₀)
    (b : BasisIndex l) : active l h (vertexMap l b h) = b.val := by
  first
  | ext i
    rw [mem_active]
    constructor
    · intro he
      by_contra hi
      have hp := hh.2 b i hi
      simp only [slack_apply, he, sub_self, mul_zero, lt_self_iff_false] at hp
    · intro hi
      exact vertexMap_active l b h ⟨i, hi⟩

theorem simple_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) {h : ι → ℝ} (hh : h ∈ chamber l h₀)
    {x : E} (hx : x ∈ (body l h).extremePoints ℝ) :
    Function.Bijective (evaluation l (active l h x)) := by
  first
  | obtain ⟨b, rfl⟩ := extreme_eq_vertexMap_without_generic l h hx
    rw [active_eq_basis_of_mem_chamber l h₀ hh b]
    exact b.property

theorem isCompact_body_of_positive_reference (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hpos : ∀ i, 0 < h₀ i) (hc : IsCompact (body l h₀))
    (h : ι → ℝ) : IsCompact (body l h) := by
  first
  | let r : ℝ := 1 + ∑ i, |h i / h₀ i|
    have hr : 0 < r := by
      first
      | have hs : 0 ≤ ∑ i, |h i / h₀ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp [r]
        linarith
    have hbound : ∀ i, h i ≤ r * h₀ i := by
      first
      | intro i
        have hi : |h i / h₀ i| ≤ ∑ j, |h j / h₀ j| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => |h j / h₀ j|)
            (fun j _ => abs_nonneg (h j / h₀ j)) (Finset.mem_univ i)
        have hd : h i / h₀ i ≤ r := by
          have ha := le_abs_self (h i / h₀ i)
          dsimp [r]
          linarith
        exact (div_le_iff₀ (hpos i)).mp hd
    have hsub : body l h ⊆ (fun x : E => r • x) '' body l h₀ := by
      first
      | intro x hx
        refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
        intro i
        rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
        exact (div_le_iff₀ hr).mpr ((hx i).trans (hbound i) |>.trans_eq (mul_comm r (h₀ i)))
    exact (hc.image (continuous_const.smul continuous_id)).of_isClosed_subset
      (body_isClosed l h) hsub

theorem zero_mem_interior_body (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hpos : ∀ i, 0 < h i) : (0 : E) ∈ interior (body l h) := by
  first
  | let U : Set E := {x | ∀ i, l i x < h i}
    have hU : IsOpen U := by
      first
      | simp only [U, Set.ofPred_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt (l i).continuous continuous_const
    have h0 : (0 : E) ∈ U := by intro i; simpa only [map_zero] using hpos i
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hU.mem_nhds h0) (fun x hx i => (hx i).le))

theorem body_add_of_mem_chamber (l : ι → E →L[ℝ] ℝ)
    (h₀ : ι → ℝ) (hg : Generic l h₀) (hpos : ∀ i, 0 < h₀ i)
    (hc : IsCompact (body l h₀)) {h k : ι → ℝ}
    (hh : h ∈ chamber l h₀) (hk : k ∈ chamber l h₀) :
    body l (h + k) = body l h + body l k := by
  first
  | apply Subset.antisymm
    · rw [body_eq_convexHull_vertices l (h + k)
        (isCompact_body_of_positive_reference l h₀ hpos hc _)]
      apply convexHull_min _ ((body_convex l h).add (body_convex l k))
      rintro x ⟨b, hb, rfl⟩
      have hb₀ : b ∈ feasibleBases l h₀ := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg (chamber_add l h₀ hh hk)] at hb
      have hbh : b ∈ feasibleBases l h := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg hh]
      have hbk : b ∈ feasibleBases l k := by
        first
        | rwa [feasibleBases_eq_of_mem_chamber l h₀ hg hk]
      change vertexMap l b (h + k) ∈ body l h + body l k
      rw [map_add]
      exact Set.add_mem_add hbh hbk
    · rintro x ⟨y, hy, z, hz, rfl⟩ i
      simpa only [map_add, Pi.add_apply] using add_le_add (hy i) (hz i)

theorem body_smul (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    body l (r • h) = r • body l h := by
  first
  | ext x
    constructor
    · intro hx
      refine ⟨r⁻¹ • x, ?_, by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      intro i
      rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
      exact (div_le_iff₀ hr).mpr (by simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hx i)
    · rintro ⟨y, hy, rfl⟩ i
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using
        mul_le_mul_of_nonneg_left (hy i) hr.le

/-- Every real support direction is represented by two actual bodies in one
simple chamber. This is the precise unrestricted extension used in the
finite-dimensional Alexandrov--Fenchel operator. -/
theorem exists_chamber_difference (l : ι → E →L[ℝ] ℝ) (h₀ : ι → ℝ)
    {h : ι → ℝ} (hh : h ∈ chamber l h₀) (x : ι → ℝ) :
    ∃ (a : ℝ) (k : ι → ℝ), 0 < a ∧ k ∈ chamber l h₀ ∧ x = a • (k - h) := by
  first
  | have ht : Tendsto (fun t : ℝ => h + t • x) (𝓝 0) (𝓝 h) := by
      first
      | have hc : Continuous (fun t : ℝ => h + t • x) := by fun_prop
        simpa only [zero_smul, add_zero] using
          hc.tendsto (0 : ℝ)
    have he := ht.eventually ((isOpen_chamber l h₀).mem_nhds hh)
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp he
    have heps : dist (ε / 2) 0 < ε := by
      first
      | rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
        linarith
    refine ⟨(ε / 2)⁻¹, h + (ε / 2) • x, inv_pos.mpr (half_pos hε), hsmall heps, ?_⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (half_pos hε).ne', one_smul]

end VolumePolynomials.PolyhedralSupport
