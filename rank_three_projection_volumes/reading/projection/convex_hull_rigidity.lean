module

public import Projection.ConvexHullValuation
public import Projection.MixedArea
public import VolumeVerification.MeasureSupportAverage

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace RankThreeProjection
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- For actual support functions, equality of one reference pairing for the
convex hull propagates to every mixed-area support. This is an amplification
theorem: the reference pairing equality remains explicit and must be obtained
separately. Neither weak nor strong AF rigidity is assumed in its proof.

The proof uses the actual convex hull `D = conv(A ∪ B)`. Its quadratic
valuation identity and AF show that the nonnegative support difference
`h_D - h_A` has zero integral against every marked mixed area measure. -/
theorem support_equality_of_hull_reference_pairing {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B H : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a)
    (hHH : 0 < mixedVolume μ (Fin.cons H (Fin.cons H K)))
    (hreference :
      mixedVolume μ (Fin.cons (joinBody A B) (Fin.cons H K)) =
        mixedVolume μ (Fin.cons A (Fin.cons H K))) :
    ∀ T : ConvexBody E, ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
      supportContinuous A u = supportContinuous B u := by
  let D := joinBody A B
  let q : ConvexBody E → ConvexBody E → ℝ :=
    fun X Y => mixedVolume μ (Fin.cons X (Fin.cons Y K))
  have hsymm (X Y : ConvexBody E) : q X Y = q Y X :=
    PolyhedralSupport.mixedVolume_cons_cons_swap μ X Y K
  have hmono : a ≤ q D A := by
    rw [← hAA]
    exact mixedVolume_mono_first_all μ (Fin.cons A K) hdim A D
      (le_joinBody_left A B)
  have hDAall : ∀ T, q D T = q A T :=
    VolumeVerification.AFPairingEquality.hull_pairings_of_weak_equality
      q hsymm
      (fun X Y T => PolyhedralSupport.mixedVolume_cons_add μ X Y (Fin.cons T K))
      (fun r hr X T => PolyhedralSupport.mixedVolume_cons_smul μ X (Fin.cons T K) hr)
      (fun X Y => mixedVolume_alexandrovFenchel μ hdim K X Y)
      A B D H a ha hAA hAB hBB (mixedVolume_joinBody_identity μ K A B)
      hmono hHH hreference
  have hABall : ∀ T, q A T = q B T :=
    mixedVolume_equal_pairings_of_AF_equality μ hdim K A B a ha hAA hAB hBB
  have hDBall (T : ConvexBody E) : q D T = q B T := (hDAall T).trans (hABall T)
  have zero_on_marked_support (C T : ConvexBody E) (hC : C ≤ D)
      (hpair : q D T = q C T) :
      ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
        supportContinuous D u - supportContinuous C u = 0 := by
    apply VolumeVerification.MeasureSupportAverage.zero_on_support_of_integral_zero
      (mixedAreaMeasure μ (Fin.cons T K) hdim)
      (supportContinuous D - supportContinuous C)
      (fun u => sub_nonneg.mpr (supportContinuous_mono hC u))
    change (∫ u, supportContinuous D u - supportContinuous C u
      ∂mixedAreaMeasure μ (Fin.cons T K) hdim) = 0
    have hDint : Integrable (fun u => supportContinuous D u)
        (mixedAreaMeasure μ (Fin.cons T K) hdim) :=
      (BoundedContinuousFunction.mkOfCompact (supportContinuous D)).integrable _
    have hCint : Integrable (fun u => supportContinuous C u)
        (mixedAreaMeasure μ (Fin.cons T K) hdim) :=
      (BoundedContinuousFunction.mkOfCompact (supportContinuous C)).integrable _
    have hpair' : mixedVolume μ (Fin.cons D (Fin.cons T K)) =
        mixedVolume μ (Fin.cons C (Fin.cons T K)) := hpair
    rw [integral_sub hDint hCint,
      mixedAreaMeasure_integral, mixedAreaMeasure_integral, hpair', sub_self]
  intro T u hu
  have hA := zero_on_marked_support A T (le_joinBody_left A B) (hDAall T) u hu
  have hB := zero_on_marked_support B T (le_joinBody_right A B) (hDBall T) u hu
  linarith

/-- The usual weak-to-strong formulation is an immediate consequence of the
reference-pairing version. Weak equality is required only on the actual
area-measure support of one reference body with positive self-pairing. -/
theorem support_equality_of_weak_area_equality {d : ℕ}
    (K : Fin d → ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A B H : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A K)) = a)
    (hAB : mixedVolume μ (Fin.cons A (Fin.cons B K)) = a)
    (hBB : mixedVolume μ (Fin.cons B (Fin.cons B K)) = a)
    (hHH : 0 < mixedVolume μ (Fin.cons H (Fin.cons H K)))
    (hweak : ∀ u ∈ (mixedAreaMeasure μ (Fin.cons H K) hdim).support,
      supportContinuous A u = supportContinuous B u) :
    ∀ T : ConvexBody E, ∀ u ∈ (mixedAreaMeasure μ (Fin.cons T K) hdim).support,
      supportContinuous A u = supportContinuous B u := by
  apply support_equality_of_hull_reference_pairing μ K hdim A B H a ha
    hAA hAB hBB hHH
  have hi : (∫ u, supportContinuous (joinBody A B) u
      ∂mixedAreaMeasure μ (Fin.cons H K) hdim) =
    ∫ u, supportContinuous A u ∂mixedAreaMeasure μ (Fin.cons H K) hdim := by
    apply integral_congr_ae
    filter_upwards [Measure.support_mem_ae
      (μ := mixedAreaMeasure μ (Fin.cons H K) hdim)] with u hu
    have h := hweak u hu
    rw [supportContinuous_join, ContinuousMap.sup_apply, ← h, max_self]
  rw [mixedAreaMeasure_integral, mixedAreaMeasure_integral] at hi
  exact mul_left_cancel₀ (ne_of_gt
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg (d + 1)) zero_lt_one)) hi

end RankThreeProjection
