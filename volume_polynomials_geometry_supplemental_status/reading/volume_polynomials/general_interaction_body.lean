module

public import VolumePolynomials.PlanarApproximation

@[expose] public section
set_option autoImplicit false

/-! # Proposition 4.3 for arbitrary planar convex bodies

The finite construction is passed to a Hausdorff limit in a fixed compact box.
The output identity concerns the actual mixed volumes in the three coordinate
planes. A final square thickening includes zero-area and segment inputs.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem area_translate (Q : ConvexBody Plane) (v : Plane) :
    volume.real (translateBody v Q : Set Plane) = volume.real (Q : Set Plane) := by
  first
  | rw [← mixedArea_diagonal volume plane_finrank, mixedArea_translate,
      mixedArea_diagonal volume plane_finrank]

theorem area_le_width_mul_height (Q : ConvexBody Plane) :
    volume.real (Q : Set Plane) ≤ width Q * height Q := by
  first
  | have hsub : (Q : Set Plane) ⊆
        (Prod.fst '' (Q : Set Plane)) ×ˢ (Prod.snd '' (Q : Set Plane)) := by
      first
      | intro p hp
        exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    have hc := (Q.isCompact.image continuous_fst).prod (Q.isCompact.image continuous_snd)
    have h := measureReal_mono (μ := volume) hsub hc.measure_lt_top.ne
    simpa only [width, height, Measure.volume_eq_prod, measureReal_prod_prod] using h

def IsInteraction (B C Q : ConvexBody Plane) : Prop :=
  width Q = 1 ∧ height Q = 1 ∧
    ∀ A : ConvexBody Plane, 6 * triple A B C = 2 * mixedArea volume A Q

theorem IsInteraction.translate {B C Q : ConvexBody Plane}
    (h : IsInteraction B C Q) (v : Plane) : IsInteraction B C (translateBody v Q) := by
  first
  | refine ⟨(width_translate Q v).trans h.1, (height_translate Q v).trans h.2.1, ?_⟩
    intro A
    rw [mixedArea_translate_right]
    exact h.2.2 A

theorem interaction_area_unique {B C Q R : ConvexBody Plane}
    (hQ : IsInteraction B C Q) (hR : IsInteraction B C R) :
    volume.real (Q : Set Plane) = volume.real (R : Set Plane) := by
  first
  | obtain ⟨v, hv⟩ := eq_translate_of_mixedArea_eq Q R (fun A => by
      have hq := hQ.2.2 A
      have hr := hR.2.2 A
      linarith)
    rw [hv, area_translate]

theorem interaction_closed_limit {B C : ConvexBody Plane}
    (Bn Cn : ℕ → ConvexBody Plane) (hB : Tendsto Bn atTop (𝓝 B))
    (hC : Tendsto Cn atTop (𝓝 C))
    (hQ : ∀ n, ∃ Q : ConvexBody Plane, IsInteraction (Bn n) (Cn n) Q ∧
      max (volume.real (Bn n : Set Plane)) (volume.real (Cn n : Set Plane)) ≤ volume.real (Q : Set Plane)) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | choose Q hQI hQa using hQ
    choose p hp using fun n => (Q n).nonempty
    let R : ℕ → ConvexBody Plane := fun n => translateBody (-(p n)) (Q n)
    have hRI (n : ℕ) : IsInteraction (Bn n) (Cn n) (R n) := (hQI n).translate _
    have hRc (n : ℕ) : R n ∈ centeredUnitBodies :=
      ⟨zero_mem_translateBody_neg (hp n), (hRI n).1, (hRI n).2.1⟩
    have hRa (n : ℕ) : volume.real (R n : Set Plane) = volume.real (Q n : Set Plane) :=
      area_translate _ _
    obtain ⟨L, hLc, φ, hφ, hL⟩ := isCompact_centeredUnitBodies.tendsto_subseq hRc
    have hB' := hB.comp hφ.tendsto_atTop
    have hC' := hC.comp hφ.tendsto_atTop
    refine ⟨L, ⟨hLc.2.1, hLc.2.2, ?_⟩, ?_⟩
    · intro A
      have hleft := (tendsto_const_nhds (x := (6 : ℝ))).mul
        ((continuous_triple A).continuousAt.tendsto.comp (hB'.prodMk_nhds hC'))
      have hright := (tendsto_const_nhds (x := (2 : ℝ))).mul
        ((continuous_mixedArea_right A).continuousAt.tendsto.comp hL)
      exact (isClosed_eq continuous_fst continuous_snd).mem_of_tendsto
        (hleft.prodMk_nhds hright) (Filter.Eventually.of_forall (fun n => (hRI (φ n)).2.2 A))
    · have hBa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hB'
      have hCa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hC'
      have hLa := (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hL
      exact le_of_tendsto_of_tendsto (hBa.max hCa) hLa
        (Filter.Eventually.of_forall (fun n => by
          change max (volume.real (Bn (φ n) : Set Plane))
            (volume.real (Cn (φ n) : Set Plane)) ≤ volume.real (R (φ n) : Set Plane)
          rw [hRa]
          exact hQa (φ n)))

theorem interaction_body_of_positive_area (B C : ConvexBody Plane)
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | obtain ⟨Bn, hBn, hBlim⟩ := exists_unit_polygon_sequence B hBa hBw hBh
    obtain ⟨Cn, hCn, hClim⟩ := exists_unit_polygon_sequence C hCa hCw hCh
    apply interaction_closed_limit Bn Cn hBlim hClim
    intro n
    obtain ⟨Q, hQw, hQh, hQV, hQa⟩ := polygon_interaction_body (Bn n) (Cn n)
      (hBn n).1 (hCn n).1 (hBn n).2.2.2.2 (hCn n).2.2.2.2
      (hBn n).2.2.1 (hBn n).2.2.2.1 (hCn n).2.2.1 (hCn n).2.2.2.1
    exact ⟨Q, ⟨hQw, hQh, hQV⟩, hQa⟩

def unitSquare : ConvexBody Plane := unitX + unitY

theorem unitSquare_width : width unitSquare = 1 := by simp [unitSquare, width_add]
theorem unitSquare_height : height unitSquare = 1 := by simp [unitSquare, height_add]
theorem unitSquare_area : volume.real (unitSquare : Set Plane) = 1 := by
  first
  | rw [unitSquare, area_add volume plane_finrank, unitX, unitY, area_segmentBody,
      area_segmentBody]
    change 0 + 2 * mixedArea volume unitX unitY + 0 = 1
    simpa only [zero_add, add_zero] using twice_mixedArea_axes

def squareThickening (K : ConvexBody Plane) (t : ℝ) : ConvexBody Plane :=
  (1 - t) • K + t • unitSquare

theorem squareThickening_widths (K : ConvexBody Plane) (hKw : width K = 1)
    (hKh : height K = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    width (squareThickening K t) = 1 ∧ height (squareThickening K t) = 1 := by
  first
  | have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    constructor
    · rw [squareThickening, width_add, width_smul _ h1, width_smul _ ht.1,
        hKw, unitSquare_width]
      ring
    · rw [squareThickening, height_add, height_smul _ h1, height_smul _ ht.1,
        hKh, unitSquare_height]
      ring

theorem squareThickening_area_pos (K : ConvexBody Plane) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < volume.real (squareThickening K t : Set Plane) := by
  first
  | have h1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [squareThickening, area_add volume plane_finrank, area_smul _ h1,
      area_smul _ ht.1.le, unitSquare_area]
    have hm := mixedArea_nonnegative volume ((1 - t) • K) (t • unitSquare)
    have ha : 0 ≤ (1 - t) ^ 2 * volume.real (K : Set Plane) :=
      mul_nonneg (sq_nonneg _) measureReal_nonneg
    nlinarith [sq_pos_of_pos ht.1]

theorem squareThickening_tendsto (K : ConvexBody Plane) :
    Tendsto (fun n : ℕ => squareThickening K (1 / ((n : ℝ) + 1))) atTop (𝓝 K) := by
  first
  | have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h : Tendsto
        (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) • K +
          (1 / ((n : ℝ) + 1)) • unitSquare) atTop
        (𝓝 (((1 : ℝ) - 0) • K + (0 : ℝ) • unitSquare)) :=
      (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).smul
        (tendsto_const_nhds (x := K))).add
          (ht.smul (tendsto_const_nhds (x := unitSquare)))
    simpa only [sub_zero, one_smul, body_zero_smul, add_zero, squareThickening] using h

/-- Proposition 4.3, including arbitrary compact convex unit-width inputs
with zero area. The normalized mixed volumes have their ordinary Lebesgue
meaning in dimensions two and three. -/
theorem proposition_4_3 (B C : ConvexBody Plane)
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤ volume.real (Q : Set Plane) := by
  first
  | apply interaction_closed_limit
      (fun n : ℕ => squareThickening B (1 / ((n : ℝ) + 1)))
      (fun n : ℕ => squareThickening C (1 / ((n : ℝ) + 1)))
      (squareThickening_tendsto B) (squareThickening_tendsto C)
    intro n
    have ht : (1 : ℝ) / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := by
      first
      | refine ⟨by positivity, ?_⟩
        apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
    have hB := squareThickening_widths B hBw hBh ⟨ht.1.le, ht.2⟩
    have hC := squareThickening_widths C hCw hCh ⟨ht.1.le, ht.2⟩
    exact interaction_body_of_positive_area _ _
      (squareThickening_area_pos B ht) (squareThickening_area_pos C ht)
      hB.1 hB.2 hC.1 hC.2

end VolumePolynomials.PlanarInteraction
