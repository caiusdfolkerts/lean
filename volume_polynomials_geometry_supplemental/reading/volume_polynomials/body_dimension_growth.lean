module

public import VolumePolynomials.BodySubspaceCoordinates
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Dimension is the exponent of volume growth

Every full-dimensional sum `K + L` has two-sided growth of exact order
`t^(dim K)` when only `K` is dilated. The proof constructs subspace
coordinates and uses the literal fiber bounds. This supplies the geometric
foundation of Lemma 2.1 in every dimension.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

def affineDimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) : ℕ := finrank ℝ (vectorSpan ℝ (K : Set E))

theorem affineDimension_eq_direction_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) : affineDimension K = finrank ℝ (affineSpan ℝ (K : Set E)).direction := by
  first
  | rw [direction_affineSpan]
    rfl

theorem linearHull_translate_eq_vectorSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) {p : E} (hp : p ∈ K) :
    linearHull (translateBody (-p) K) = vectorSpan ℝ (K : Set E) := by
  first
  | rw [linearHull, vectorSpan_eq_span_vsub_set_right ℝ hp]
    congr 1
    rw [coe_translateBody]
    change (fun x : E => -p + x) '' (K : Set E) = (fun x : E => x - p) '' (K : Set E)
    congr 1
    funext x
    abel

theorem bodyVolume_pos_iff_affineSpan_eq_top {d : ℕ} (K : Body d) :
    0 < bodyVolume K ↔ affineSpan ℝ (K : Set (Space d)) = ⊤ := by
  first
  | have hreal : 0 < bodyVolume K ↔ 0 < volume (K : Set (Space d)) := by
      first
      | constructor
        · intro h
          exact (ENNReal.toReal_pos_iff.mp h).1
        · intro h
          exact ENNReal.toReal_pos h.ne' (bodyVolume_finite K)
    have hpos : 0 < volume (K : Set (Space d)) ↔
        (interior (K : Set (Space d))).Nonempty := by
      first
      | rw [pos_iff_ne_zero, ← measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
        simpa only [Set.nonempty_iff_ne_empty] using
          not_congr (isOpen_interior.measure_eq_zero_iff volume)
    rw [hreal, hpos, K.convex.interior_nonempty_iff_affineSpan_eq_top]

theorem centered_volume_growth {d : ℕ} (K L : Body d)
    (hK : (0 : Space d) ∈ K) (hL : (0 : Space d) ∈ L)
    (hfull : 0 < bodyVolume (K + L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ finrank ℝ (linearHull K) ≤ bodyVolume (t • K + L) ∧
        bodyVolume (t • K + L) ≤ C * t ^ finrank ℝ (linearHull K) := by
  first
  | let H := linearHull K
    obtain ⟨U, hHU⟩ := Submodule.exists_isCompl H
    let T := SubspaceCoordinates.frame H U hHU
    let A := SubspaceCoordinates.coordinateBody H U hHU K
    let B := mapBody T.toContinuousLinearMap L
    let J : ℝ := LinearFrame.volumeFactor T
    have hJ : 0 < J := by exact_mod_cast LinearFrame.volumeFactor_pos T
    have hKH : (K : Set (Space d)) ⊆ H := fun _ hx => mem_linearHull hx
    have htotal : linearHull (K + L) = ⊤ :=
      (bodyVolume_pos_iff_linearHull_eq_top (zero_mem_body_add hK hL)).mp hfull
    have hA : 0 < bodyVolume A := SubspaceCoordinates.coordinateBody_volume_pos H U hHU K hK rfl
    have hB : 0 < bodyVolume (FiberGrowth.projectionBody B) :=
      SubspaceCoordinates.projection_volume_pos H U hHU K L hKH hL htotal
    have hmap (t : ℝ) : mapBody T.toContinuousLinearMap (t • K + L) =
        FiberVolume.embedBody (t • A) + B := by
      first
      | rw [mapBody_add, mapBody_smul]
        have hKA := SubspaceCoordinates.frame_body_eq_embed H U hHU K hKH
        change t • mapBody (SubspaceCoordinates.frame H U hHU).toContinuousLinearMap K + B = _
        rw [hKA]
        congr 1
        exact (mapBody_smul
          (ContinuousLinearMap.inl ℝ (Space (finrank ℝ H)) (Space (finrank ℝ U))) t A).symm
    have hvolume (t : ℝ) : bodyVolume (t • K + L) =
        J * volume.real ((FiberVolume.embedBody (t • A) + B :
          ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
          Set (Space (finrank ℝ H) × Space (finrank ℝ U))) := by
      first
      | have h := LinearFrame.realVolume_eq_factor_mul_image T (t • K + L : Set (Space d))
        change bodyVolume (t • K + L) = J * volume.real
          (mapBody T.toContinuousLinearMap (t • K + L) : Set (Space (finrank ℝ H) × Space (finrank ℝ U))) at h
        rwa [hmap] at h
    have hbase : bodyVolume (K + L) =
        J * volume.real ((FiberVolume.embedBody A + B :
          ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
          Set (Space (finrank ℝ H) × Space (finrank ℝ U))) := by
      first
      | simpa only [one_smul] using hvolume 1
    refine ⟨J * bodyVolume A * bodyVolume (FiberGrowth.projectionBody B), bodyVolume (K + L),
      mul_pos (mul_pos hJ hA) hB, hfull, ?_⟩
    intro t ht
    constructor
    · rw [hvolume]
      have h := mul_le_mul_of_nonneg_left (FiberGrowth.lower_bound A B (zero_le_one.trans ht)) hJ.le
      change (J * bodyVolume A * bodyVolume (FiberGrowth.projectionBody B)) * t ^ finrank ℝ H ≤ _
      nlinarith only [h]
    · rw [hvolume, hbase]
      have h := mul_le_mul_of_nonneg_left (FiberGrowth.upper_bound A B ht) hJ.le
      change _ ≤ (J * volume.real ((FiberVolume.embedBody A + B :
        ConvexBody (Space (finrank ℝ H) × Space (finrank ℝ U))) :
        Set (Space (finrank ℝ H) × Space (finrank ℝ U)))) * t ^ finrank ℝ H
      nlinarith only [h]

/-- Exact growth order for arbitrary translations and lower-dimensional
summands, under the paper's full-dimensional total-sum hypothesis. -/
theorem volume_growth {d : ℕ} (K L : Body d) (hfull : 0 < bodyVolume (K + L)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ affineDimension K ≤ bodyVolume (t • K + L) ∧
        bodyVolume (t • K + L) ≤ C * t ^ affineDimension K := by
  first
  | obtain ⟨p, hp⟩ := K.nonempty
    obtain ⟨q, hq⟩ := L.nonempty
    let K' := translateBody (-p) K
    let L' := translateBody (-q) L
    have hvol (t : ℝ) : bodyVolume (t • K' + L') = bodyVolume (t • K + L) := by
      first
      | have h := volumeFunction_translate (![K, L] : Fin 2 → Body d) ![-p, -q] ![t, 1]
        simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] using h
    have hfull' : 0 < bodyVolume (K' + L') := by
      first
      | have heq : bodyVolume (K' + L') = bodyVolume (K + L) := by
          simpa only [one_smul] using hvol 1
        rwa [heq]
    obtain ⟨c, C, hc, hC, hbound⟩ := centered_volume_growth K' L'
      (zero_mem_translateBody_neg hp) (zero_mem_translateBody_neg hq) hfull'
    refine ⟨c, C, hc, hC, ?_⟩
    intro t ht
    have h := hbound t ht
    rw [hvol] at h
    have hdim : finrank ℝ (linearHull K') = affineDimension K := by
      first
      | dsimp only [K']
        rw [linearHull_translate_eq_vectorSpan K hp]
        rfl
    simpa only [hdim] using h

theorem exponent_le_of_growth_bound {a b : ℕ} {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ t : ℝ, 1 ≤ t → c * t ^ a ≤ C * t ^ b) : a ≤ b := by
  first
  | by_contra hab
    have hba : b + 1 ≤ a := by omega
    let t := max 1 (C / c + 1)
    have ht : 1 ≤ t := le_max_left _ _
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hp := pow_le_pow_right₀ ht hba
    have h := (mul_le_mul_of_nonneg_left hp hc.le).trans (hbound t ht)
    rw [pow_succ] at h
    have hct : c * t ≤ C := by
      first
      | apply Iff.mp (mul_le_mul_iff_left₀ (pow_pos htpos b))
        nlinarith only [h]
    have hlarge : C / c + 1 ≤ t := le_max_right _ _
    have hlarge' := mul_le_mul_of_nonneg_left hlarge hc.le
    have hcancel : c * (C / c) = C := mul_div_cancel₀ C hc.ne'
    nlinarith

theorem affineDimension_eq_of_growth {d m : ℕ} (K L : Body d)
    (hfull : 0 < bodyVolume (K + L)) {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ t : ℝ, 1 ≤ t → c * t ^ m ≤ bodyVolume (t • K + L) ∧
      bodyVolume (t • K + L) ≤ C * t ^ m) : affineDimension K = m := by
  first
  | obtain ⟨a, A, ha, hA, hgrowth⟩ := volume_growth K L hfull
    apply le_antisymm
    · exact exponent_le_of_growth_bound ha (fun t ht =>
        (hgrowth t ht).1.trans (hbound t ht).2)
    · exact exponent_le_of_growth_bound hc (fun t ht =>
        (hbound t ht).1.trans (hgrowth t ht).2)

end VolumePolynomials
