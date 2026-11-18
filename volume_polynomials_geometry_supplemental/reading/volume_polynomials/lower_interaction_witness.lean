module

public import VolumePolynomials.GeneralInteractionGap
public import VolumePolynomials.FiniteCapLowerWitness
public import VolumePolynomials.FiniteRepresentedPolygons
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option autoImplicit false

/-! # Actual mixed-volume witnesses for the logarithmic lower gap

A finite decreasing chain is closed by its diagonal edge. The balanced-edge
construction produces an actual body with that finite mixed-area
representation. Its interaction body is therefore identified by Proposition
4.3, and its area is exactly the finite convolution energy used in Section 5.3.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped Topology Pointwise BigOperators ComplexConjugate NNReal

namespace VolumePolynomials.PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092
open HalfZonotope

def closedChainEdges (vs : List Plane) : Sum (Fin vs.length) (Fin 1) → Plane :=
  Sum.elim vs.get (fun _ => (-1, 1))

theorem sum_get_map {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β) :
    (∑ i : Fin xs.length, f (xs.get i)) = (xs.map f).sum := by
  first
  | rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem closedChainEdges_balanced {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1)) :
    (∑ i, max (closedChainEdges vs i).1 0) = 1 ∧
    (∑ i, max (-(closedChainEdges vs i).1) 0) = 1 ∧
    (∑ i, max (closedChainEdges vs i).2 0) = 1 ∧
    (∑ i, max (-(closedChainEdges vs i).2) 0) = 1 := by
  first
  | have hx (i : Fin vs.length) : 0 ≤ (vs.get i).1 := (hv _ (List.get_mem _ _)).1
    have hy (i : Fin vs.length) : (vs.get i).2 ≤ 0 := (hv _ (List.get_mem _ _)).2
    have hsum : (∑ i : Fin vs.length, vs.get i) = vs.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    have hsx : (∑ i : Fin vs.length, (vs.get i).1) = 1 := by
      rw [← Prod.fst_sum, hsum, hs]
    have hsy : (∑ i : Fin vs.length, (vs.get i).2) = -1 := by
      rw [← Prod.snd_sum, hsum, hs]
    simp only [closedChainEdges, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fin.sum_univ_one, max_eq_left (hx _), max_eq_right (neg_nonpos.mpr (hx _)),
      max_eq_right (hy _), max_eq_left (neg_nonneg.mpr (hy _)), Finset.sum_const_zero,
      Finset.sum_neg_distrib, hsx, hsy]
    norm_num

theorem slopeAtom_eq_edgeMeasure {v : Plane} (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeAtom v = edgeMeasure v := by
  first
  | simp only [slopeAtom, atomWeight, atomSlope, edgeMeasure, edgeWeight, edgeSlope,
      abs_of_nonneg hv.1, abs_of_nonpos hv.2]

theorem cornerAtom_decreasing {v : Plane} (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (i j : Fin 2) :
    cornerAtom v i j = if i = 0 ∧ j = 1 then edgeMeasure v else 0 := by
  first
  | by_cases hx : v.1 = 0
    · rw [cornerAtom_axis (Or.inl hx)]
      simp [edgeMeasure, edgeWeight, hx]
    by_cases hy : v.2 = 0
    · rw [cornerAtom_axis (Or.inr hy)]
      simp [edgeMeasure, edgeWeight, hy]
    have hyneg : v.2 < 0 := lt_of_le_of_ne hv.2 hy
    simp only [cornerAtom, signIndex, if_pos hv.1, if_neg (not_le_of_gt hyneg),
      slopeAtom_eq_edgeMeasure hv, eq_comm]

theorem cornerMeasure_eq_sum (vs : List Plane) :
    cornerMeasure vs = (vs.map edgeMeasure).sum := by
  first
  | induction vs with
    | nil => rfl
    | cons v vs ih => simp only [cornerMeasure, List.map_cons, List.sum_cons, ih, add_comm]

/-- A two-by-two matrix with zero diagonal and the specified off-diagonal entries. -/
def offDiagonalPair {α : Type*} [Zero α] (x y : α) : Matrix (Fin 2) (Fin 2) α :=
  fun i j => if i = j then 0 else if i = 0 then x else y

theorem closedChain_cornerMatrix {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMatrix (closedChainEdges vs) =
      offDiagonalPair (cornerMeasure vs) (Measure.dirac 0) := by
  first
  | apply Matrix.ext
    intro i j
    simp only [cornerMatrix, closedChainEdges, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one]
    simp_rw [cornerAtom_decreasing (hv _ (List.get_mem _ _))]
    have hsum : (∑ k : Fin vs.length, edgeMeasure (vs.get k)) = cornerMeasure vs := by
      first
      | rw [sum_get_map, cornerMeasure_eq_sum]
    fin_cases i <;> fin_cases j <;>
      simp [cornerAtom, signIndex, slopeAtom, atomWeight, atomSlope, hsum, cornerMeasure_eq_sum,
        offDiagonalPair]

theorem closedChain_secondMoment {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeSecondMoment (cornerMatrix (closedChainEdges vs)) =
      1 + ‖cornerMean (cornerMeasure vs)‖ ^ 2 := by
  first
  | letI : ∀ i j : Fin 2,
        IsFiniteMeasure (offDiagonalPair (cornerMeasure vs) (Measure.dirac 0) i j) := by
      intro i j
      unfold offDiagonalPair
      split_ifs <;> infer_instance
    rw [closedChain_cornerMatrix hv, slopeSecondMoment_eq_entry_energies]
    simp [offDiagonalPair, Fin.sum_univ_two, cornerMean, norm_cornerFeature] <;> ring

theorem matrixSecondTrace_offDiagonal_self (z : ℂ) :
    matrixSecondTrace ((offDiagonalPair z 1)ᴴ * offDiagonalPair z 1) =
      1 + Complex.normSq (z * z) := by
  first
  | simp [offDiagonalPair, matrixSecondTrace_eq_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem closedChain_interactionMoment {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    slopeInteractionMoment (cornerMatrix (closedChainEdges vs))
        (cornerMatrix (closedChainEdges vs)) =
      1 + ‖cornerMean (cornerMeasure vs ∗ cornerMeasure vs)‖ ^ 2 := by
  first
  | have hf (ξ : ℝ) : slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ =
        offDiagonalPair (charFun (cornerMeasure vs) ξ) 1 := by
      first
      | rw [closedChain_cornerMatrix hv]
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [slopeFourierMatrix, offDiagonalPair, charFun_apply_real]
    have htrace (ξ : ℝ) :
        matrixSecondTrace ((slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ)ᴴ *
          slopeFourierMatrix (cornerMatrix (closedChainEdges vs)) ξ) =
        1 + Complex.normSq (charFun (cornerMeasure vs ∗ cornerMeasure vs) ξ) := by
      first
      | rw [hf, matrixSecondTrace_offDiagonal_self, charFun_conv]
    simp only [slopeInteractionMoment, htrace]
    rw [integral_add (integrable_const 1)
      (integrable_spectral_normSq (cornerMeasure vs ∗ cornerMeasure vs)), corner_spectral_energy]
    simp

theorem closedChain_body_area {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1))
    {B : ConvexBody Plane} (hB : Represents B (closedChainEdges vs))
    (hw : width B = 1) (hh : height B = 1) :
    volume.real (B : Set Plane) = volume.real (cap vs) := by
  first
  | have h := hB.unit_second_moment hw hh
    rw [closedChain_secondMoment hv] at h
    rw [area_unit_cap hs, cornerEnergy_eq_mean_norm hv]
    linarith

theorem closedChain_interaction_area {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hs : vs.sum = (1, -1))
    {Q : ConvexBody Plane}
    (hQ : Represents Q (completedEdges (productEdges (closedChainEdges vs) (closedChainEdges vs))))
    (hw : width Q = 1) (hh : height Q = 1) :
    volume.real (Q : Set Plane) = volume.real (cap (interactionGenerators vs vs)) := by
  first
  | have h := hQ.unit_second_moment hw hh
    rw [productEdge_secondMoment, closedChain_interactionMoment hv] at h
    rw [area_self_interaction_cap hv hs]
    linarith

/-- The lower bound in Corollary 5.3 is attained by actual inputs and their
actual three-dimensional mixed-volume interaction, for every real deficit
in the stated interval. It is not restricted to a sequence of deficits. -/
theorem logarithmic_lower_interaction_witness {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ B Q : ConvexBody Plane, width B = 1 ∧ height B = 1 ∧
      volume.real (B : Set Plane) = 1 / 2 - δ ∧ IsInteraction B B Q ∧
      (1 / 2 - δ ≤ volume.real (Q : Set Plane)) ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ 1 / 2 - volume.real (Q : Set Plane) := by
  first
  | obtain ⟨vs, hv, hs, harea, hgap⟩ := finite_caps_logarithmic_lower_gap hδ hδhalf
    have hbal := closedChainEdges_balanced hv hs
    obtain ⟨B, hB, hBw, hBh⟩ := exists_body_of_balanced_edges (closedChainEdges vs)
      hbal.1 hbal.2.1 hbal.2.2.1 hbal.2.2.2
    obtain ⟨Q, hQw, hQh, hQV, hQa, hQrep⟩ := finite_interaction_body hB hB hBw hBh hBw hBh
    have hBa := (closedChain_body_area hv hs hB hBw hBh).trans harea
    have hQarea := closedChain_interaction_area hv hs hQrep hQw hQh
    refine ⟨B, Q, hBw, hBh, hBa, ⟨hQw, hQh, hQV⟩, ?_, ?_⟩
    · simpa only [max_self, hBa] using hQa
    · rw [hQarea]
      exact hgap

theorem logarithmic_lower_polygon_interaction_witness {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ B Q : ConvexBody Plane,
      PolytopeGeometry.IsFiniteHull (B : Set Plane) ∧
      PolytopeGeometry.IsFiniteHull (Q : Set Plane) ∧
      width B = 1 ∧ height B = 1 ∧ volume.real (B : Set Plane) = 1 / 2 - δ ∧
      IsInteraction B B Q ∧ (1 / 2 - δ ≤ volume.real (Q : Set Plane)) ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤ 1 / 2 - volume.real (Q : Set Plane) := by
  first
  | obtain ⟨vs, hv, hs, harea, hgap⟩ := finite_caps_logarithmic_lower_gap hδ hδhalf
    have hbal := closedChainEdges_balanced hv hs
    obtain ⟨B, hB, hBw, hBh⟩ := exists_body_of_balanced_edges (closedChainEdges vs)
      hbal.1 hbal.2.1 hbal.2.2.1 hbal.2.2.2
    obtain ⟨Q, hQw, hQh, hQV, hQa, hQrep⟩ := finite_interaction_body hB hB hBw hBh hBw hBh
    have hBa := (closedChain_body_area hv hs hB hBw hBh).trans harea
    have hQarea := closedChain_interaction_area hv hs hQrep hQw hQh
    refine ⟨B, Q, hB.finiteHull_of_unit_widths hBw hBh,
      hQrep.finiteHull_of_unit_widths hQw hQh, hBw, hBh, hBa,
      ⟨hQw, hQh, hQV⟩, ?_, ?_⟩
    · simpa only [max_self, hBa] using hQa
    · rw [hQarea]
      exact hgap

end VolumePolynomials.PlanarInteraction
