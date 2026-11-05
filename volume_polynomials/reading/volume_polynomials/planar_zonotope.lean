module

public import VolumePolynomials.PlanarLinearExtrusion
public import Mathlib.Data.List.Range

@[expose] public section

/-!
# Area and directional widths of arbitrary finite planar zonotopes

These are identities for Lebesgue measure of actual Minkowski sums of actual
segments. Repeated, collinear, and zero generating vectors are all allowed.
The only geometric input is the extrusion theorem proved from Fubini.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials.PlanarExtrusion

/-- Length is additive under Minkowski addition of nonempty compact intervals. -/
theorem length_add_compact_convex {S T : Set ℝ}
    (hS : IsCompact S) (hSc : Convex ℝ S) (hSn : S.Nonempty)
    (hT : IsCompact T) (hTc : Convex ℝ T) (hTn : T.Nonempty) :
    volume.real (S + T) = volume.real S + volume.real T := by
  have hs : S = Icc (sInf S) (sSup S) :=
    eq_Icc_of_connected_compact ⟨hSn, Real.convex_iff_isPreconnected.mp hSc⟩ hS
  have ht : T = Icc (sInf T) (sSup T) :=
    eq_Icc_of_connected_compact ⟨hTn, Real.convex_iff_isPreconnected.mp hTc⟩ hT
  have hab : sInf S ≤ sSup S := csInf_le_csSup hSn hS.bddBelow hS.bddAbove
  have hcd : sInf T ≤ sSup T := csInf_le_csSup hTn hT.bddBelow hT.bddAbove
  rw [hs, ht, Icc_add_Icc hab hcd, Real.volume_real_Icc_of_le (add_le_add hab hcd),
    Real.volume_real_Icc_of_le hab, Real.volume_real_Icc_of_le hcd]
  ring

/-- Determinant in the second entry, bundled as a linear map. -/
def determinantMap (v : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := determinant v
  map_add' := by
    intro x y
    simp only [determinant, Prod.fst_add, Prod.snd_add]
    ring
  map_smul' := by
    intro a x
    simp only [determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem determinantMap_apply (v x : Plane) : determinantMap v x = determinant v x := rfl

theorem continuous_determinant (v : Plane) : Continuous (determinant v) :=
  (continuous_const.mul continuous_snd).sub (continuous_const.mul continuous_fst)

theorem centeredSegment_compact (v : Plane) : IsCompact (centeredSegment v) :=
  isCompact_Icc.image (continuous_id.smul continuous_const)

theorem centeredSegment_convex (v : Plane) : Convex ℝ (centeredSegment v) :=
  (convex_Icc _ _).linear_image (LinearMap.toSpanSingleton ℝ Plane v)

theorem zero_mem_centeredSegment (v : Plane) : (0 : Plane) ∈ centeredSegment v := by
  refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
  simp

theorem length_image_mul (k : ℝ) (S : Set ℝ) :
    volume.real ((fun s : ℝ => k * s) '' S) = |k| * volume.real S := by
  have h := congrArg ENNReal.toReal
    (Measure.addHaar_image_linearMap (volume : Measure ℝ)
      (k • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) S)
  simpa [measureReal_def, LinearMap.det_ring, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg k)] using h

theorem length_determinant_centeredSegment (v w : Plane) :
    volume.real (determinant v '' centeredSegment w) = |determinant v w| := by
  have himage : determinant v '' centeredSegment w =
      (fun s : ℝ => determinant v w * s) '' Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    rw [centeredSegment, Set.image_image]
    congr 1
    funext s
    simp only [Function.comp_apply, determinant, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [himage, length_image_mul]
  norm_num

/-- The finite Minkowski sum of centered generating segments. -/
def zonotope : List Plane → Set Plane
  | [] => {0}
  | v :: vs => zonotope vs + centeredSegment v

@[simp] theorem zonotope_singleton (v : Plane) : zonotope [v] = centeredSegment v := by
  simp [zonotope, Set.singleton_zero]

theorem zonotope_append (xs ys : List Plane) :
    zonotope (xs ++ ys) = zonotope xs + zonotope ys := by
  induction xs with
  | nil => simp [zonotope, Set.singleton_zero]
  | cons v xs ih => simp [zonotope, ih, add_assoc, add_comm, add_left_comm]

theorem zonotope_range_succ (u : ℕ → Plane) (N : ℕ) :
    zonotope ((List.range (N + 1)).map u) =
      zonotope ((List.range N).map u) + centeredSegment (u N) := by
  simp [List.range_succ, List.map_append, zonotope_append]

theorem zonotope_compact (vs : List Plane) : IsCompact (zonotope vs) := by
  induction vs with
  | nil => exact isCompact_singleton
  | cons v vs ih => exact ih.add (centeredSegment_compact v)

theorem zonotope_convex (vs : List Plane) : Convex ℝ (zonotope vs) := by
  induction vs with
  | nil => exact convex_singleton 0
  | cons v vs ih => exact ih.add (centeredSegment_convex v)

theorem zero_mem_zonotope (vs : List Plane) : (0 : Plane) ∈ zonotope vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      exact ⟨0, ih, 0, zero_mem_centeredSegment v, zero_add 0⟩

theorem determinant_width_zonotope (v : Plane) (vs : List Plane) :
    volume.real (determinant v '' zonotope vs) =
      (vs.map (fun w => |determinant v w|)).sum := by
  induction vs with
  | nil => simp [zonotope, determinant, measureReal_def]
  | cons w vs ih =>
      change volume.real (determinantMap v '' (zonotope vs + centeredSegment w)) = _
      rw [Set.image_add (determinantMap v)]
      have hlen := length_add_compact_convex
        ((zonotope_compact vs).image (continuous_determinant v))
        ((zonotope_convex vs).linear_image (determinantMap v))
        ((show (zonotope vs).Nonempty from ⟨0, zero_mem_zonotope vs⟩).image _)
        ((centeredSegment_compact w).image (continuous_determinant v))
        ((centeredSegment_convex w).linear_image (determinantMap v))
        ((show (centeredSegment w).Nonempty from ⟨0, zero_mem_centeredSegment w⟩).image _)
      change volume.real (determinant v '' zonotope vs + determinant v '' centeredSegment w) = _
      rw [hlen]
      change volume.real (determinant v '' zonotope vs) +
        volume.real (determinant v '' centeredSegment w) = _
      rw [ih, length_determinant_centeredSegment]
      simp [add_comm]

/-- Sum of absolute determinants over every unordered pair of occurrences. -/
def pairArea : List Plane → ℝ
  | [] => 0
  | v :: vs => pairArea vs + (vs.map (fun w => |determinant v w|)).sum

theorem pairArea_append_singleton (vs : List Plane) (w : Plane) :
    pairArea (vs ++ [w]) = pairArea vs + (vs.map (fun v => |determinant v w|)).sum := by
  induction vs with
  | nil => simp [pairArea]
  | cons v vs ih =>
      simp only [List.cons_append, pairArea, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih]
      ring

theorem list_sum_map_range (f : ℕ → ℝ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ, ih]

theorem pairArea_range_succ (u : ℕ → Plane) (N : ℕ) :
    pairArea ((List.range (N + 1)).map u) = pairArea ((List.range N).map u) +
      ∑ i ∈ Finset.range N, |determinant (u i) (u N)| := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
    pairArea_append_singleton, List.map_map, Function.comp_def, list_sum_map_range]

theorem pairArea_range (u : ℕ → Plane) (N : ℕ) :
    pairArea ((List.range N).map u) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |determinant (u i) (u j)| := by
  induction N with
  | zero => simp [pairArea]
  | succ N ih => rw [pairArea_range_succ, Finset.sum_range_succ, ih]

/-- The exact planar zonotope area identity, with no general-position assumption. -/
theorem area_zonotope (vs : List Plane) : volume.real (zonotope vs) = pairArea vs := by
  induction vs with
  | nil => simp [zonotope, pairArea, measureReal_def]
  | cons v vs ih =>
      rw [zonotope, area_add_centeredSegment (zonotope_compact vs) (zonotope_convex vs),
        ih, determinant_width_zonotope, pairArea]

theorem area_zonotope_range (u : ℕ → Plane) (N : ℕ) :
    volume.real (zonotope ((List.range N).map u)) =
      ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, |determinant (u i) (u j)| := by
  rw [area_zonotope, pairArea_range]

theorem determinant_width_zonotope_range (v : Plane) (u : ℕ → Plane) (N : ℕ) :
    volume.real (determinant v '' zonotope ((List.range N).map u)) =
      ∑ i ∈ Finset.range N, |determinant v (u i)| := by
  rw [determinant_width_zonotope, List.map_map, list_sum_map_range]
  rfl

end VolumePolynomials.PlanarExtrusion
