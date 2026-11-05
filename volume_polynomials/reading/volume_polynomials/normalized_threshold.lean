module

public import VolumePolynomials.GeometricThreshold
public import VolumePolynomials.ThresholdFrontier

@[expose] public section
set_option autoImplicit false

/-! # Attained minima of the actual normalized cubic geometry

The fiber is defined by literal bodies and the equalities in (3.2), with
`α = 2*s`. Compactness and a positive lower bound on `T` prove attainment;
the threshold is not supplied as an assumed minimum function. Proposition
3.1 is the separate equivalence with the original coefficient slice.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092

structure NormalizedData (s z : ℝ) where
  A : ConvexBody Plane
  B : ConvexBody Plane
  C : ConvexBody Plane
  T : ℝ
  T_pos : 0 < T
  A_width : width A = 1
  A_height : height A = s
  A_area : volume.real (A : Set Plane) = 2 * s * T
  B_width : width B = 1
  B_height : height B = 1
  C_width : width C = 1
  C_height : height C = 1
  B_area : volume.real (B : Set Plane) = T
  C_area : volume.real (C : Set Plane) = T
  triple_value : 6 * triple A B C = 2 * T * z

def NormalizedRealizable (s z : ℝ) : Prop := Nonempty (NormalizedData s z)
def normalizedThreshold (s : ℝ) : ℝ := sInf {z : ℝ | NormalizedRealizable s z}
def normalizedSlice : Set (Fin 2 → ℝ) := {p | NormalizedRealizable (p 0) (p 1)}

theorem triple_translate (A B C : ConvexBody Plane) (a b c : Plane) :
    triple (translateBody a A) (translateBody b B) (translateBody c C) = triple A B C := by
  first
  | have h := mixed3_translate (mapBody embedXY A) (mapBody embedYZ B) (mapBody embedXZ C)
      (embedXY a) (embedYZ b) (embedXZ c)
    simpa only [triple, mapBody_translate] using h

def NormalizedData.translate {s z : ℝ} (D : NormalizedData s z) (a b c : Plane) :
    NormalizedData s z where
  A := translateBody a D.A
  B := translateBody b D.B
  C := translateBody c D.C
  T := D.T
  T_pos := D.T_pos
  A_width := (width_translate _ _).trans D.A_width
  A_height := (height_translate _ _).trans D.A_height
  A_area := (area_translate _ _).trans D.A_area
  B_width := (width_translate _ _).trans D.B_width
  B_height := (height_translate _ _).trans D.B_height
  C_width := (width_translate _ _).trans D.C_width
  C_height := (height_translate _ _).trans D.C_height
  B_area := (area_translate _ _).trans D.B_area
  C_area := (area_translate _ _).trans D.C_area
  triple_value := by rw [triple_translate]; exact D.triple_value

theorem normalized_nonempty {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    ∃ z : ℝ, NormalizedRealizable s z ∧ z ≤ 2 := by
  first
  | obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
      hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsSmall
    have hlog : 0 ≤ Real.log (1 / s) :=
      Real.log_nonneg ((one_le_div hs).mpr (by linarith))
    have hterm : 0 ≤ (3 / 51200 : ℝ) * s ^ 3 * Real.log (1 / s) := by positivity
    have hr := comparisonRoot_le_one_add hs.le
    exact ⟨z, ⟨⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh, hBa, hCa, hz⟩⟩,
      by linarith⟩

def separationConstant (s : ℝ) : ℝ := 1 + s - 2 * Real.sqrt s

theorem separationConstant_pos {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    0 < separationConstant s := by
  first
  | have hr := Real.sqrt_nonneg s
    have hsq := Real.sq_sqrt hs
    have hr1 : Real.sqrt s < 1 := by nlinarith
    have hdiff : 0 < (1 - Real.sqrt s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr1)
    dsimp [separationConstant]
    nlinarith

theorem NormalizedData.separation {s z : ℝ} (D : NormalizedData s z) (hs : 0 < s) :
    separationConstant s ≤ 2 * D.T * z := by
  first
  | obtain ⟨Q, hQ, _⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
    have hcorner := mixedArea_corner_inequality D.A Q
    rw [D.A_width, D.A_height, hQ.1, hQ.2.1, one_mul, mul_one] at hcorner
    simp only [one_mul, mul_one] at hcorner
    have hAu := area_le_width_mul_height D.A
    rw [D.A_width, D.A_height, one_mul] at hAu
    have hQu := area_le_width_mul_height Q
    rw [hQ.1, hQ.2.1, one_mul] at hQu
    have hA0 : 0 ≤ volume.real (D.A : Set Plane) := measureReal_nonneg
    have hQ0 : 0 ≤ volume.real (Q : Set Plane) := measureReal_nonneg
    have hprod : (s - volume.real (D.A : Set Plane)) * (1 - volume.real (Q : Set Plane)) ≤ s := by
      first
      | have h := mul_le_mul_of_nonneg_left (show 1 - volume.real (Q : Set Plane) ≤ 1 by linarith)
          (show 0 ≤ s - volume.real (D.A : Set Plane) by linarith)
        nlinarith
    have hroot := Real.sqrt_le_sqrt hprod
    have heq := hQ.2.2 D.A
    rw [D.triple_value] at heq
    dsimp [separationConstant]
    linarith

theorem NormalizedData.T_lower {s z : ℝ} (D : NormalizedData s z)
    (hs : 0 < s) (hz : z ≤ 2) : separationConstant s / 4 ≤ D.T := by
  first
  | have hc := D.separation hs
    have h := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * D.T from mul_nonneg (by norm_num) D.T_pos.le)
    linarith

theorem body_subset_box_of_widths (K : ConvexBody Plane) (h0 : (0 : Plane) ∈ K)
    (hw : width K ≤ 1) (hh : height K ≤ 1) :
    (K : Set Plane) ⊆ Icc (-1, -1) (1, 1) := by
  first
  | intro p hp
    have hpos (i : Fin 4) : 0 ≤ SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | simpa only [map_zero] using SupportGeometry.le_support K.isCompact (axisNormals i) h0
    have hx := support_axisX_sum K
    have hy := support_axisY_sum K
    have hpx := SupportGeometry.le_support K.isCompact (axisNormals 0) hp
    have hnx := SupportGeometry.le_support K.isCompact (axisNormals 1) hp
    have hpy := SupportGeometry.le_support K.isCompact (axisNormals 3) hp
    have hny := SupportGeometry.le_support K.isCompact (axisNormals 2) hp
    have h0' := hpos 0
    have h1' := hpos 1
    have h2' := hpos 2
    have h3' := hpos 3
    simp only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      normal_apply, one_mul, zero_mul, neg_one_mul, sub_zero, zero_sub] at hpx hnx hpy hny h0' h1' h2' h3'
    change (-1 ≤ p.1 ∧ -1 ≤ p.2) ∧ (p.1 ≤ 1 ∧ p.2 ≤ 1)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def centeredBoxBodies : Set (ConvexBody Plane) :=
  {Q | (0 : Plane) ∈ Q ∧ (Q : Set Plane) ⊆ Icc (-1, -1) (1, 1)}

def normalizedTupleConstraints (s t : ℝ) : Set (Fin 3 → ConvexBody Plane) :=
  {K | (∀ i, width (K i) = 1) ∧
    (∀ i, height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i) ∧
    volume.real (K 0 : Set Plane) = 2 * s * volume.real (K 1 : Set Plane) ∧
    volume.real (K 2 : Set Plane) = volume.real (K 1 : Set Plane) ∧
    t ≤ volume.real (K 1 : Set Plane)}

def normalizedCompactTuples (s t : ℝ) : Set (Fin 3 → ConvexBody Plane) :=
  (Set.pi Set.univ (fun _ : Fin 3 => centeredBoxBodies)) ∩ normalizedTupleConstraints s t

theorem isClosed_normalizedTupleConstraints (s t : ℝ) :
    IsClosed (normalizedTupleConstraints s t) := by
  first
  | have hw : IsClosed {K : Fin 3 → ConvexBody Plane | ∀ i, width (K i) = 1} := by
      first
      | simp only [ofPred_forall]
        exact isClosed_iInter (fun i => isClosed_eq (continuous_width.comp (continuous_apply i)) continuous_const)
    have hh : IsClosed {K : Fin 3 → ConvexBody Plane |
        ∀ i, height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i} := by
      first
      | simp only [ofPred_forall]
        exact isClosed_iInter (fun i => isClosed_eq (continuous_height.comp (continuous_apply i)) continuous_const)
    have ha (i : Fin 3) : Continuous (fun K : Fin 3 → ConvexBody Plane => volume.real (K i : Set Plane)) :=
      (continuous_convexBody_realMeasure volume).comp (continuous_apply i)
    exact hw.inter (hh.inter ((isClosed_eq (ha 0) (continuous_const.mul (ha 1))).inter
      ((isClosed_eq (ha 2) (ha 1)).inter (isClosed_le continuous_const (ha 1)))))

theorem isCompact_normalizedCompactTuples (s t : ℝ) :
    IsCompact (normalizedCompactTuples s t) := by
  first
  | exact (isCompact_univ_pi (fun _ : Fin 3 =>
      isCompact_bodies_in_compact (E := Plane) (isCompact_Icc : IsCompact (Icc ((-1, -1) : Plane) (1, 1))))).inter_right
        (isClosed_normalizedTupleConstraints s t)

def normalizedTupleValue (K : Fin 3 → ConvexBody Plane) : ℝ :=
  (6 * triple (K 0) (K 1) (K 2)) / (2 * volume.real (K 1 : Set Plane))

theorem continuous_triple_tuple :
    Continuous (fun K : Fin 3 → ConvexBody Plane => triple (K 0) (K 1) (K 2)) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_mapBody embedXY).comp (continuous_apply 0)
    · exact (continuous_mapBody embedYZ).comp (continuous_apply 1)
    · exact (continuous_mapBody embedXZ).comp (continuous_apply 2)

theorem continuousOn_normalizedTupleValue (s t : ℝ) (ht : 0 < t) :
    ContinuousOn normalizedTupleValue (normalizedCompactTuples s t) := by
  first
  | apply (continuous_const.mul continuous_triple_tuple).continuousOn.div
      (continuous_const.mul ((continuous_convexBody_realMeasure volume).comp (continuous_apply 1))).continuousOn
    intro K hK
    have hT : 0 < volume.real (K 1 : Set Plane) := ht.trans_le hK.2.2.2.2.2
    change (2 * volume.real (K 1 : Set Plane) : ℝ) ≠ 0
    exact mul_ne_zero (by norm_num) hT.ne' 

def dataOfNormalizedTuple {s t : ℝ} (ht : 0 < t)
    (K : Fin 3 → ConvexBody Plane) (hK : K ∈ normalizedCompactTuples s t) :
    NormalizedData s (normalizedTupleValue K) where
  A := K 0
  B := K 1
  C := K 2
  T := volume.real (K 1 : Set Plane)
  T_pos := ht.trans_le hK.2.2.2.2.2
  A_width := hK.2.1 0
  A_height := hK.2.2.1 0
  A_area := hK.2.2.2.1
  B_width := hK.2.1 1
  B_height := hK.2.2.1 1
  C_width := hK.2.1 2
  C_height := hK.2.2.1 2
  B_area := rfl
  C_area := hK.2.2.2.2.1
  triple_value := by
    first
    | dsimp [normalizedTupleValue]
      have hp : 0 < volume.real (K 1 : Set Plane) := ht.trans_le hK.2.2.2.2.2
      field_simp [hp.ne']

theorem NormalizedData.exists_centered_tuple {s z t : ℝ} (D : NormalizedData s z)
    (hs1 : s ≤ 1) (ht : t ≤ D.T) :
    ∃ K ∈ normalizedCompactTuples s t, normalizedTupleValue K = z := by
  first
  | obtain ⟨a, ha⟩ := D.A.nonempty
    obtain ⟨b, hb⟩ := D.B.nonempty
    obtain ⟨c, hc⟩ := D.C.nonempty
    let E := D.translate (-a) (-b) (-c)
    let K : Fin 3 → ConvexBody Plane := ![E.A, E.B, E.C]
    have h0 (i : Fin 3) : (0 : Plane) ∈ K i := by
      first
      | fin_cases i
        · exact zero_mem_translateBody_neg ha
        · exact zero_mem_translateBody_neg hb
        · exact zero_mem_translateBody_neg hc
    have hw (i : Fin 3) : width (K i) = 1 := by
      first
      | fin_cases i
        · exact E.A_width
        · exact E.B_width
        · exact E.C_width
    have hh (i : Fin 3) : height (K i) = (![s, 1, 1] : Fin 3 → ℝ) i := by
      first
      | fin_cases i
        · exact E.A_height
        · exact E.B_height
        · exact E.C_height
    have hKh (i : Fin 3) : height (K i) ≤ 1 := by
      first
      | rw [hh]
        fin_cases i
        · exact hs1
        · norm_num
        · norm_num
    refine ⟨K, ⟨?_, hw, hh, ?_, ?_, ?_⟩, ?_⟩
    · intro i _
      exact ⟨h0 i, body_subset_box_of_widths (K i) (h0 i) (hw i).le (hKh i)⟩
    · change volume.real (E.A : Set Plane) = 2 * s * volume.real (E.B : Set Plane)
      rw [E.A_area, E.B_area]
    · change volume.real (E.C : Set Plane) = volume.real (E.B : Set Plane)
      rw [E.C_area, E.B_area]
    · change t ≤ volume.real (E.B : Set Plane)
      rw [E.B_area]
      exact ht
    · change 6 * triple E.A E.B E.C / (2 * volume.real (E.B : Set Plane)) = z
      rw [E.B_area, E.triple_value]
      field_simp [E.T_pos.ne']

theorem normalized_threshold_attained {s : ℝ} (hs : 0 < s) (hsSmall : s ≤ 1 / 2) :
    NormalizedRealizable s (normalizedThreshold s) ∧
      ∀ z : ℝ, NormalizedRealizable s z → normalizedThreshold s ≤ z := by
  first
  | let t : ℝ := separationConstant s / 4
    have ht : 0 < t := div_pos (separationConstant_pos hs.le (by linarith)) (by norm_num)
    obtain ⟨z0, ⟨D0⟩, hz0⟩ := normalized_nonempty hs hsSmall
    obtain ⟨K0, hK0, hvalue0⟩ := D0.exists_centered_tuple (by linarith) (D0.T_lower hs hz0)
    obtain ⟨Kmin, hKmin, hmin⟩ := (isCompact_normalizedCompactTuples s t).exists_isMinOn
      ⟨K0, hK0⟩ (continuousOn_normalizedTupleValue s t ht)
    have hdata : NormalizedRealizable s (normalizedTupleValue Kmin) :=
      ⟨dataOfNormalizedTuple ht Kmin hKmin⟩
    have hbound (z : ℝ) (hz : NormalizedRealizable s z) : normalizedTupleValue Kmin ≤ z := by
      first
      | rcases hz with ⟨D⟩
        by_cases hz2 : z ≤ 2
        · obtain ⟨K, hK, hvalue⟩ := D.exists_centered_tuple (by linarith) (D.T_lower hs hz2)
          rw [← hvalue]
          exact hmin hK
        · have h := hmin hK0
          change normalizedTupleValue Kmin ≤ normalizedTupleValue K0 at h
          rw [hvalue0] at h
          linarith
    have hleast : IsLeast {z : ℝ | NormalizedRealizable s z} (normalizedTupleValue Kmin) :=
      ⟨hdata, hbound⟩
    have heq : normalizedThreshold s = normalizedTupleValue Kmin := hleast.csInf_eq
    rw [heq]
    exact ⟨hdata, hbound⟩

/-- The full two-sided logarithmic gap for the actual normalized geometry.
The constants are explicit; the fiber minimum is proved to be attained. -/
theorem normalized_threshold_gap {s : ℝ} (hs : 0 < s)
    (hsmall : s < min (1 / 128) (Real.exp (-1))) :
    (3 / 51200) * s ^ 3 * Real.log (1 / s) ≤ comparisonRoot s - normalizedThreshold s ∧
      comparisonRoot s - normalizedThreshold s ≤ 34816 * s ^ 3 * Real.log (1 / s) := by
  first
  | have hsSmall : s ≤ 1 / 2 := by
      first
      | have h := hsmall.trans_le (min_le_left _ _)
        linarith
    obtain ⟨⟨D⟩, hmin⟩ := normalized_threshold_attained hs hsSmall
    constructor
    · obtain ⟨A, B, C, T, z, hT, hAw, hAh, hAa, hBw, hBh, hCw, hCh,
        hBa, hCa, hz, hgap⟩ := geometric_threshold_lower hs hsSmall
      have hle := hmin z ⟨⟨A, B, C, T, hT, hAw, hAh, hAa, hBw, hBh,
        hCw, hCh, hBa, hCa, hz⟩⟩
      linarith
    · obtain ⟨Q, hQ, _⟩ := proposition_4_3 D.B D.C D.B_width D.B_height D.C_width D.C_height
      apply geometric_threshold_upper hs hsmall D.T_pos D.A_width D.A_height D.A_area.ge
        D.B_width D.B_height D.C_width D.C_height D.B_area D.C_area hQ
      rw [← D.triple_value]
      exact hQ.2.2 D.A

theorem normalizedSlice_not_semialgebraic : ¬ TauCeti.IsSemialgebraic normalizedSlice := by
  first
  | let a : ℝ := min (1 / 128) (Real.exp (-1))
    have ha : 0 < a := lt_min (by norm_num) (Real.exp_pos _)
    apply not_semialgebraic_of_logarithmic_minimum_gap_frontier
      (S := normalizedSlice) (b := normalizedThreshold) (a := a)
      (c := 3 / 51200) (C := 34816) ha (by norm_num)
    · intro s hs
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (normalized_threshold_attained hs.1 hssmall).1
    · intro s hs z hz
      have hssmall : s ≤ 1 / 2 := by
        first
        | have h := hs.2.trans_le (min_le_left (1 / 128 : ℝ) (Real.exp (-1)))
          linarith
      exact (normalized_threshold_attained hs.1 hssmall).2 z hz
    · filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ s in 𝓝[>] (0 : ℝ), s < a from
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (show ∀ᶠ s : ℝ in 𝓝 0, s < a from Iio_mem_nhds ha))] with s hs hsa
      simpa only [one_div] using normalized_threshold_gap hs hsa

end VolumePolynomials.PlanarInteraction
