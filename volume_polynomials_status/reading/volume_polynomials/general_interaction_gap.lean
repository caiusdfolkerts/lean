module

public import VolumePolynomials.GeneralInteractionBody

@[expose] public section
set_option autoImplicit false

/-! # The upper logarithmic interaction deficit for arbitrary convex bodies

Separate polygon deficits are retained throughout approximation. They converge
to the prescribed common deficit, so no exact-area approximation theorem is
silently assumed.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem polygon_interaction_with_deficits (B C : ConvexBody Plane)
    (hB : IsFiniteHull (B : Set Plane)) (hC : IsFiniteHull (C : Set Plane))
    (hBa : 0 < volume.real (B : Set Plane)) (hCa : 0 < volume.real (C : Set Plane))
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1) :
    ∃ Q : ConvexBody Plane, IsInteraction B C Q ∧
      ∀ δB δC : ℝ, 0 < δB → 0 < δC →
        2 * δB ≤ min (1 / 64) (Real.exp (-1)) →
        2 * δC ≤ min (1 / 64) (Real.exp (-1)) →
        volume.real (B : Set Plane) = 1 / 2 - δB →
        volume.real (C : Set Plane) = 1 / 2 - δC →
        1 / 2 - volume.real (Q : Set Plane) ≤
          2176 * (δB ^ 2 * Real.log (1 / δB) + δC ^ 2 * Real.log (1 / δC)) := by
  first
  | obtain ⟨m, b, hb⟩ := exists_representation B hB hBa
    obtain ⟨n, c, hc⟩ := exists_representation C hC hCa
    obtain ⟨Q, hQw, hQh, hQV, _, hQrep⟩ := finite_interaction_body hb hc hBw hBh hCw hCh
    refine ⟨Q, ⟨hQw, hQh, hQV⟩, ?_⟩
    intro δB δC hδB hδC hsmallB hsmallC hareaB hareaC
    exact productEdge_body_logarithmic_deficits hb hc hBw hBh hCw hCh hQrep hQw hQh
      hδB hδC hsmallB hsmallC hareaB hareaC

theorem tendsto_deficit_log_square {δ : ℝ} (hδ : 0 < δ) {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 δ)) :
    Tendsto (fun n => d n ^ 2 * Real.log (1 / d n)) atTop
      (𝓝 (δ ^ 2 * Real.log (1 / δ))) := by
  first
  | have hinv := (tendsto_const_nhds (x := (1 : ℝ))).div hd hδ.ne'
    have hlog := (Real.continuousAt_log (by positivity : (1 : ℝ) / δ ≠ 0)).tendsto.comp hinv
    exact (hd.pow 2).mul hlog

/-- Corollary 5.3 with an explicit absolute constant. It holds for every
interaction body satisfying the already proved geometric identity, since
that identity determines its area uniquely. -/
theorem corollary_5_3 {B C Q : ConvexBody Plane}
    (hBw : width B = 1) (hBh : height B = 1) (hCw : width C = 1) (hCh : height C = 1)
    (hQ : IsInteraction B C Q) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : 2 * δ < min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δ)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δ) :
    1 / 2 - volume.real (Q : Set Plane) ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
  first
  | have hδhalf : δ < 1 / 2 := by
      first
      | have hs := hsmall.trans_le (min_le_left (1 / 64 : ℝ) (Real.exp (-1)))
        linarith
    have hBpos : 0 < volume.real (B : Set Plane) := by rw [hBa]; linarith
    have hCpos : 0 < volume.real (C : Set Plane) := by rw [hCa]; linarith
    obtain ⟨Bn, hBn, hBlim⟩ := exists_unit_polygon_sequence B hBpos hBw hBh
    obtain ⟨Cn, hCn, hClim⟩ := exists_unit_polygon_sequence C hCpos hCw hCh
    have hp (n : ℕ) := polygon_interaction_with_deficits (Bn n) (Cn n)
      (hBn n).1 (hCn n).1 (hBn n).2.2.2.2 (hCn n).2.2.2.2
      (hBn n).2.2.1 (hBn n).2.2.2.1 (hCn n).2.2.1 (hCn n).2.2.2.1
    choose R hRI hRbound using hp
    choose p hpR using fun n => (R n).nonempty
    let S : ℕ → ConvexBody Plane := fun n => translateBody (-(p n)) (R n)
    have hSI (n : ℕ) : IsInteraction (Bn n) (Cn n) (S n) := (hRI n).translate _
    have hSc (n : ℕ) : S n ∈ centeredUnitBodies :=
      ⟨zero_mem_translateBody_neg (hpR n), (hSI n).1, (hSI n).2.1⟩
    have hSa (n : ℕ) : volume.real (S n : Set Plane) = volume.real (R n : Set Plane) :=
      area_translate _ _
    obtain ⟨L, hLc, φ, hφ, hLlim⟩ := isCompact_centeredUnitBodies.tendsto_subseq hSc
    have hB' := hBlim.comp hφ.tendsto_atTop
    have hC' := hClim.comp hφ.tendsto_atTop
    have hLI : IsInteraction B C L := by
      first
      | refine ⟨hLc.2.1, hLc.2.2, ?_⟩
        intro A
        have hleft := (tendsto_const_nhds (x := (6 : ℝ))).mul
          ((continuous_triple A).continuousAt.tendsto.comp (hB'.prodMk_nhds hC'))
        have hright := (tendsto_const_nhds (x := (2 : ℝ))).mul
          ((continuous_mixedArea_right A).continuousAt.tendsto.comp hLlim)
        exact (isClosed_eq continuous_fst continuous_snd).mem_of_tendsto
          (hleft.prodMk_nhds hright) (Filter.Eventually.of_forall (fun n => (hSI (φ n)).2.2 A))
    have harea := interaction_area_unique hQ hLI
    rw [harea]
    let dB : ℕ → ℝ := fun n => 1 / 2 - volume.real (Bn (φ n) : Set Plane)
    let dC : ℕ → ℝ := fun n => 1 / 2 - volume.real (Cn (φ n) : Set Plane)
    have hdB : Tendsto dB atTop (𝓝 δ) := by
      first
      | have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
          ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hB')
        simpa only [Function.comp_apply, hBa, sub_sub_cancel, dB] using h
    have hdC : Tendsto dC atTop (𝓝 δ) := by
      first
      | have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
          ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hC')
        simpa only [Function.comp_apply, hCa, sub_sub_cancel, dC] using h
    have heB := hdB.eventually (Ioi_mem_nhds hδ)
    have heC := hdC.eventually (Ioi_mem_nhds hδ)
    have hsB := ((tendsto_const_nhds (x := (2 : ℝ))).mul hdB).eventually (Iio_mem_nhds hsmall)
    have hsC := ((tendsto_const_nhds (x := (2 : ℝ))).mul hdC).eventually (Iio_mem_nhds hsmall)
    have hbound : ∀ᶠ n in atTop,
        1 / 2 - volume.real (S (φ n) : Set Plane) ≤
          2176 * (dB n ^ 2 * Real.log (1 / dB n) + dC n ^ 2 * Real.log (1 / dC n)) := by
      first
      | filter_upwards [heB, heC, hsB, hsC] with n hb hc hsb hsc
        rw [hSa]
        exact hRbound (φ n) (dB n) (dC n) hb hc hsb.le hsc.le (by dsimp [dB]; ring)
          (by dsimp [dC]; ring)
    have hleft := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      ((continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp hLlim)
    have hright := (tendsto_const_nhds (x := (2176 : ℝ))).mul
      ((tendsto_deficit_log_square hδ hdB).add (tendsto_deficit_log_square hδ hdC))
    have h := le_of_tendsto_of_tendsto hleft hright hbound
    nlinarith

end VolumePolynomials.PlanarInteraction
