module

public import VolumePolynomials.InteractionFourier
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section
set_option autoImplicit false

/-! # The area bounds for the actual product-edge body

These estimates use its proved finite edge representation and exact Fourier
matrix, followed by the arbitrary-measure contraction and fourth-moment lemmas.
The three-dimensional mixed-volume identification is a separate geometric step.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace VolumePolynomials

theorem IsEuclideanContraction.conjTranspose {F : Matrix (Fin 2) (Fin 2) ℂ}
    (hF : IsEuclideanContraction F) : IsEuclideanContraction Fᴴ := by
  first
  | rw [isEuclideanContraction_iff_operatorNorm_le_one,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map]
    exact (isEuclideanContraction_iff_operatorNorm_le_one F).mp hF

theorem matrixSecondTrace_conjTranspose (F : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixSecondTrace Fᴴ = matrixSecondTrace F := by
  first
  | simp only [matrixSecondTrace_eq_sum, Matrix.conjTranspose_apply,
      ← starRingEnd_apply, Complex.normSq_conj]
    exact Finset.sum_comm (f := fun i j : Fin 2 => Complex.normSq (F j i))

theorem matrixSecondTrace_mul_le_right (F G : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) : matrixSecondTrace (F * G) ≤ matrixSecondTrace G := by
  first
  | rw [matrixSecondTrace_eq_sum, Finset.sum_comm, matrixSecondTrace_eq_sum]
    calc
      (∑ j, ∑ i, Complex.normSq ((F * G) i j)) ≤ ∑ j, ∑ k, Complex.normSq (G k j) := by
        first
        | apply Finset.sum_le_sum
          intro j _
          simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hF (fun k => G k j)
      _ = ∑ k, ∑ j, Complex.normSq (G k j) := Finset.sum_comm

theorem mixed_matrix_trace_le_second (F G : Matrix (Fin 2) (Fin 2) ℂ)
    (hF : IsEuclideanContraction F) (hG : IsEuclideanContraction G) :
    matrixSecondTrace (Fᴴ * G) ≤ matrixSecondTrace F ∧
      matrixSecondTrace (Fᴴ * G) ≤ matrixSecondTrace G := by
  first
  | constructor
    · have he : matrixSecondTrace (Fᴴ * G) = matrixSecondTrace (Gᴴ * F) := by
        first
        | rw [← matrixSecondTrace_conjTranspose (Fᴴ * G), Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
      rw [he]
      exact matrixSecondTrace_mul_le_right _ _ hG.conjTranspose
    · exact matrixSecondTrace_mul_le_right _ _ hF.conjTranspose

theorem slopeInteractionMoment_le_second
    (ρ σ : Matrix (Fin 2) (Fin 2) (Measure ℝ))
    [∀ i j, IsFiniteMeasure (ρ i j)] [∀ i j, IsFiniteMeasure (σ i j)]
    (hρ : IsAdmissibleSlopeMatrix ρ) (hσ : IsAdmissibleSlopeMatrix σ) :
    slopeInteractionMoment ρ σ ≤ slopeSecondMoment ρ ∧
      slopeInteractionMoment ρ σ ≤ slopeSecondMoment σ := by
  first
  | have hp (ξ : ℝ) := mixed_matrix_trace_le_second (slopeFourierMatrix ρ ξ)
      (slopeFourierMatrix σ ξ) (admissible_fourier_contraction ρ hρ ξ)
      (admissible_fourier_contraction σ hσ ξ)
    exact ⟨integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
        (integrable_slopeSecondTrace ρ) (fun ξ => (hp ξ).1),
      integral_mono (integrable_slopeInteractionTrace ρ σ hρ hσ)
        (integrable_slopeSecondTrace σ) (fun ξ => (hp ξ).2)⟩

namespace PlanarEdges

open PlanarExtrusion PlanarMixedForm PlanarCorner OAI.Paper092

theorem productEdge_body_area_ge_inputs {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1) :
    max (volume.real (B : Set Plane)) (volume.real (C : Set Plane)) ≤
      volume.real (Q : Set Plane) := by
  first
  | have h := slopeInteractionMoment_le_second (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    rw [hB.unit_second_moment hBw hBh, hC.unit_second_moment hCw hCh] at h
    exact max_le (by linarith [h.1]) (by linarith [h.2])

/-- The upper logarithmic deficit in Corollary 5.3 for the literal constructed
body, with explicit absolute constants and a full real parameter interval. -/
theorem productEdge_body_logarithmic_deficit {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : 2 * δ ≤ min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δ)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δ) :
    1 / 2 - volume.real (Q : Set Plane) ≤ 4352 * δ ^ 2 * Real.log (1 / δ) := by
  first
  | have hb2 : slopeSecondMoment (cornerMatrix b) = 1 + 2 * δ := by
      first
      | rw [hB.unit_second_moment hBw hBh, hBa]
        ring
    have hc2 : slopeSecondMoment (cornerMatrix c) = 1 + 2 * δ := by
      first
      | rw [hC.unit_second_moment hCw hCh, hCa]
        ring
    have h := slopeInteractionMoment_logarithmic_bound (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
      (mul_pos (by norm_num) hδ) hsmall hb2 hc2
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    have hlog : Real.log (1 / (2 * δ)) ≤ Real.log (1 / δ) := by
      first
      | apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hδ (by linarith)
    have hlogmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4352 * δ ^ 2 by positivity)
    nlinarith

/-- The version with separate deficits is used before taking a Hausdorff
limit; inscribed approximation need not preserve the two areas exactly. -/
theorem productEdge_body_logarithmic_deficits {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B C Q : ConvexBody Plane} {b : ι → Plane} {c : κ → Plane}
    (hB : Represents B b) (hC : Represents C c)
    (hBw : width B = 1) (hBh : height B = 1)
    (hCw : width C = 1) (hCh : height C = 1)
    (hQ : Represents Q (completedEdges (productEdges b c)))
    (hQw : width Q = 1) (hQh : height Q = 1)
    {δB δC : ℝ} (hδB : 0 < δB) (hδC : 0 < δC)
    (hsmallB : 2 * δB ≤ min (1 / 64) (Real.exp (-1)))
    (hsmallC : 2 * δC ≤ min (1 / 64) (Real.exp (-1)))
    (hBa : volume.real (B : Set Plane) = 1 / 2 - δB)
    (hCa : volume.real (C : Set Plane) = 1 / 2 - δC) :
    1 / 2 - volume.real (Q : Set Plane) ≤
      2176 * (δB ^ 2 * Real.log (1 / δB) + δC ^ 2 * Real.log (1 / δC)) := by
  first
  | have hb2 : slopeSecondMoment (cornerMatrix b) = 1 + 2 * δB := by
      first
      | rw [hB.unit_second_moment hBw hBh, hBa]
        ring
    have hc2 : slopeSecondMoment (cornerMatrix c) = 1 + 2 * δC := by
      first
      | rw [hC.unit_second_moment hCw hCh, hCa]
        ring
    have hb := lemma_5_2_fourth_moment (cornerMatrix b) (hB.admissible hBw hBh)
      (mul_pos (by norm_num) hδB) hsmallB hb2
    have hc := lemma_5_2_fourth_moment (cornerMatrix c) (hC.admissible hCw hCh)
      (mul_pos (by norm_num) hδC) hsmallC hc2
    have hi := slopeInteractionMoment_le_mean (cornerMatrix b) (cornerMatrix c)
      (hB.admissible hBw hBh) (hC.admissible hCw hCh)
    have hQmoment := hQ.unit_second_moment hQw hQh
    rw [productEdge_secondMoment] at hQmoment
    have hlog (δ : ℝ) (hδ : 0 < δ) :
        δ ^ 2 * Real.log (1 / (2 * δ)) ≤ δ ^ 2 * Real.log (1 / δ) := by
      first
      | apply mul_le_mul_of_nonneg_left _ (sq_nonneg δ)
        apply Real.log_le_log (by positivity)
        exact one_div_le_one_div_of_le hδ (by linarith)
    nlinarith [hlog δB hδB, hlog δC hδC]

end PlanarEdges
end VolumePolynomials
