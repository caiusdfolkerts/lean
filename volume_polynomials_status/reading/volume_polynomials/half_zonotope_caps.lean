module

public import VolumePolynomials.PlanarZonotope
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section
set_option autoImplicit false

/-!
# Literal convex caps obtained by halving planar zonotopes

These are actual compact convex sets with Lebesgue area, not formal edge lists.
The cut through the center divides the area equally because negation exchanges
the two halves and their common line has measure zero. Nonnegative horizontal
and nonpositive vertical generators with sum `(1,-1)` give exact unit widths.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def diagonalMap : Plane →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ

@[simp] theorem diagonalMap_apply (p : Plane) : diagonalMap p = p.1 + p.2 := rfl

theorem volume_diagonal_zero : volume {p : Plane | p.1 + p.2 = 0} = 0 := by
  first
  | change volume (LinearMap.ker diagonalMap : Set Plane) = 0
    apply Measure.addHaar_submodule volume
    intro h
    have hmem : ((1, 0) : Plane) ∈ LinearMap.ker diagonalMap := by
      first
      | rw [h]
        trivial
    norm_num [LinearMap.mem_ker, diagonalMap] at hmem

theorem neg_mem_zonotope {vs : List Plane} {x : Plane} (hx : x ∈ zonotope vs) :
    -x ∈ zonotope vs := by
  first
  | induction vs generalizing x with
    | nil => simpa [zonotope] using hx
    | cons v vs ih =>
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hz
        refine ⟨-y, ih hy, (-t) • v, ?_, ?_⟩
        · exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
        · simp [add_comm]

theorem neg_mem_zonotope_iff (vs : List Plane) (x : Plane) :
    -x ∈ zonotope vs ↔ x ∈ zonotope vs := by
  first
  | constructor
    · intro h
      simpa using neg_mem_zonotope h
    · exact neg_mem_zonotope

def lowerHalf (vs : List Plane) : Set Plane :=
  zonotope vs ∩ {p | p.1 + p.2 ≤ 0}

def upperHalf (vs : List Plane) : Set Plane :=
  zonotope vs ∩ {p | 0 ≤ p.1 + p.2}

theorem lowerHalf_compact (vs : List Plane) : IsCompact (lowerHalf vs) :=
  (zonotope_compact vs).inter_right
    (isClosed_le (continuous_fst.add continuous_snd) continuous_const)

theorem upperHalf_compact (vs : List Plane) : IsCompact (upperHalf vs) :=
  (zonotope_compact vs).inter_right
    (isClosed_le continuous_const (continuous_fst.add continuous_snd))

theorem lowerHalf_convex (vs : List Plane) : Convex ℝ (lowerHalf vs) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨zonotope_convex vs hx.1 hy.1 ha hb hab, ?_⟩
    change (a • x + b • y).1 + (a • x + b • y).2 ≤ 0
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hax := mul_nonpos_of_nonneg_of_nonpos ha hx.2
    have hby := mul_nonpos_of_nonneg_of_nonpos hb hy.2
    nlinarith

theorem upperHalf_eq_neg_preimage (vs : List Plane) :
    upperHalf vs = Neg.neg ⁻¹' lowerHalf vs := by
  first
  | ext x
    simp only [upperHalf, lowerHalf, mem_inter_iff, mem_setOf_eq, mem_preimage,
      neg_mem_zonotope_iff, Prod.fst_neg, Prod.snd_neg]
    constructor <;> rintro ⟨hx, h⟩ <;> exact ⟨hx, by linarith⟩

theorem lowerHalf_union_upperHalf (vs : List Plane) :
    lowerHalf vs ∪ upperHalf vs = zonotope vs := by
  first
  | ext x
    simp only [lowerHalf, upperHalf, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases le_total (x.1 + x.2) 0 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩

theorem volume_lowerHalf_inter_upperHalf (vs : List Plane) :
    volume (lowerHalf vs ∩ upperHalf vs) = 0 := by
  first
  | apply measure_mono_null _ volume_diagonal_zero
    intro x hx
    exact le_antisymm hx.1.2 hx.2.2

/-- Halving is a literal Lebesgue-area identity, including degenerate zonotopes. -/
theorem area_lowerHalf (vs : List Plane) :
    volume.real (lowerHalf vs) = pairArea vs / 2 := by
  first
  | have hneg : volume.real (upperHalf vs) = volume.real (lowerHalf vs) := by
      first
      | rw [upperHalf_eq_neg_preimage]
        exact congrArg ENNReal.toReal (Measure.measure_preimage_neg volume (lowerHalf vs))
    have hsplit := measureReal_union_add_inter
      (μ := (volume : Measure Plane)) (s := lowerHalf vs) (t := upperHalf vs)
      (upperHalf_compact vs).measurableSet
      (lowerHalf_compact vs).measure_lt_top.ne (upperHalf_compact vs).measure_lt_top.ne
    rw [lowerHalf_union_upperHalf, area_zonotope, hneg] at hsplit
    have hzero : volume.real (lowerHalf vs ∩ upperHalf vs) = 0 := by
      first
      | simp only [measureReal_def, volume_lowerHalf_inter_upperHalf, ENNReal.toReal_zero]
    rw [hzero] at hsplit
    linarith

/-- Translation places the diagonal endpoints at `(0,1)` and `(1,0)` when the
generators sum to `(1,-1)`. -/
def cap (vs : List Plane) : Set Plane :=
  {((1 / 2, 1 / 2) : Plane)} + lowerHalf vs

theorem cap_compact (vs : List Plane) : IsCompact (cap vs) :=
  isCompact_singleton.add (lowerHalf_compact vs)

theorem cap_convex (vs : List Plane) : Convex ℝ (cap vs) :=
  (convex_singleton _).add (lowerHalf_convex vs)

theorem area_cap (vs : List Plane) : volume.real (cap vs) = pairArea vs / 2 := by
  first
  | unfold cap
    rw [Set.singleton_add]
    simp only [measureReal_def, Set.image_add_left, measure_preimage_add]
    exact area_lowerHalf vs

theorem constant_parameter_mem_zonotope (vs : List Plane) (t : ℝ)
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : t • vs.sum ∈ zonotope vs := by
  first
  | induction vs with
    | nil => simp [zonotope]
    | cons v vs ih =>
        refine ⟨t • vs.sum, ih, t • v, ⟨t, ht, rfl⟩, ?_⟩
        simp only [List.sum_cons, smul_add]
        exact add_comm _ _

theorem diagonal_endpoints_mem_cap {vs : List Plane} (hsum : vs.sum = (1, -1)) :
    ((0, 1) : Plane) ∈ cap vs ∧ ((1, 0) : Plane) ∈ cap vs := by
  first
  | constructor
    · refine ⟨(1 / 2, 1 / 2), rfl, (-1 / 2 : ℝ) • vs.sum, ?_, ?_⟩
      · refine ⟨constant_parameter_mem_zonotope vs _ ⟨by norm_num, by norm_num⟩, ?_⟩
        norm_num [hsum]
      · norm_num [hsum]
    · refine ⟨(1 / 2, 1 / 2), rfl, (1 / 2 : ℝ) • vs.sum, ?_, ?_⟩
      · refine ⟨constant_parameter_mem_zonotope vs _ ⟨by norm_num, by norm_num⟩, ?_⟩
        norm_num [hsum]
      · norm_num [hsum]

theorem zonotope_coordinate_bounds {vs : List Plane} {x : Plane} (hx : x ∈ zonotope vs) :
    |x.1| ≤ (vs.map (fun v => |v.1|)).sum / 2 ∧
      |x.2| ≤ (vs.map (fun v => |v.2|)).sum / 2 := by
  first
  | induction vs generalizing x with
    | nil =>
        have hx0 : x = 0 := hx
        subst x
        simp
    | cons v vs ih =>
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        obtain ⟨t, ht, rfl⟩ := hz
        have hi := ih hy
        have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
        have hfst := mul_le_mul_of_nonneg_right ht' (abs_nonneg v.1)
        have hsnd := mul_le_mul_of_nonneg_right ht' (abs_nonneg v.2)
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        constructor
        · have htri := abs_add_le y.1 (t * v.1)
          rw [abs_mul] at htri
          linarith [hi.1]
        · have htri := abs_add_le y.2 (t * v.2)
          rw [abs_mul] at htri
          linarith [hi.2]

theorem sum_abs_coordinates {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (vs.map (fun v => |v.1|)).sum = vs.sum.1 ∧
      (vs.map (fun v => |v.2|)).sum = -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp
    | cons v vs ih =>
        have hv := hvs v (List.mem_cons_self)
        have hi := ih (fun w hw => hvs w (List.mem_cons_of_mem v hw))
        simp only [List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add,
          abs_of_nonneg hv.1, abs_of_nonpos hv.2, hi.1, hi.2]
        constructor
        · trivial
        · ring

theorem cap_subset_unitSquare {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    cap vs ⊆ Icc ((0, 0) : Plane) (1, 1) := by
  first
  | intro x hx
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    change c = (1 / 2, 1 / 2) at hc
    subst c
    have hb := zonotope_coordinate_bounds hy.1
    have ha := sum_abs_coordinates hvs
    rw [ha.1, ha.2, hsum] at hb
    have hx := abs_le.mp hb.1
    have hy' := abs_le.mp hb.2
    constructor <;> constructor <;> simp only [Prod.fst_add, Prod.snd_add] <;>
      norm_num at * <;> linarith

/-- Both coordinate projections are the entire unit interval, not merely subsets. -/
theorem cap_coordinate_projections {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    Prod.fst '' cap vs = Icc (0 : ℝ) 1 ∧ Prod.snd '' cap vs = Icc (0 : ℝ) 1 := by
  first
  | have hb := cap_subset_unitSquare hvs hsum
    obtain ⟨h01, h10⟩ := diagonal_endpoints_mem_cap hsum
    have hdiag (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, 1 - t) ∈ cap vs := by
      first
      | have h := cap_convex vs h01 h10 (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
        convert h using 1 <;> ext <;> simp <;> ring
    constructor
    · apply Subset.antisymm
      · rintro t ⟨x, hx, rfl⟩
        exact ⟨(hb hx).1.1, (hb hx).2.1⟩
      · intro t ht
        exact ⟨(t, 1 - t), hdiag t ht, rfl⟩
    · apply Subset.antisymm
      · rintro t ⟨x, hx, rfl⟩
        exact ⟨(hb hx).1.2, (hb hx).2.2⟩
      · intro t ht
        refine ⟨(1 - t, t), ?_, rfl⟩
        convert hdiag (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ using 1 <;>
          ext <;> simp <;> ring

end VolumePolynomials.HalfZonotope
