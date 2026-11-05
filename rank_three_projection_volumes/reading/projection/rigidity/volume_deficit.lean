module

public import Projection.Rigidity.VolumePolynomialJets
public import Projection.Rigidity.PolynomialContact

/-!
# Actual volume deficit under mixed-volume equality

The theorem at the end proves the vanishing normalized midpoint deficit for
the actual bodies K+tA and K+tC. All coefficients come from their actual
Haar-volume polynomials. There is no polynomiality or asymptotic hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Module Polynomial Filter
open scoped BigOperators Pointwise Topology
namespace RankThreeProjection.Rigidity
open VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def minkowskiMidpoint (A C : ConvexBody E) : ConvexBody E := (1 / 2 : ℝ) • (A + C)

theorem minkowskiRay_midpoint (K A C : ConvexBody E) (t : ℝ) (ht : 0 ≤ t) :
    K + t • minkowskiMidpoint A C =
      (1 / 2 : ℝ) • ((K + t • A) + (K + t • C)) := by
  have hK : (1 / 2 : ℝ) • K + (1 / 2 : ℝ) • K = K := by
    rw [← body_add_smul K (by norm_num) (by norm_num)]
    norm_num
  have hmul : t * (1 / 2 : ℝ) = (1 / 2 : ℝ) * t := by ring
  simp only [minkowskiMidpoint, smul_add, smul_smul, hmul]
  conv_lhs => rw [← hK]
  exact add_add_add_comm _ _ _ _

theorem mixedVolume_midpoint_first {d : ℕ} (H : Fin d → ConvexBody E)
    (A C : ConvexBody E) :
    mixedVolume μ (Fin.cons (minkowskiMidpoint A C) H) =
      (mixedVolume μ (Fin.cons A H) + mixedVolume μ (Fin.cons C H)) / 2 := by
  rw [minkowskiMidpoint,
    PolyhedralSupport.mixedVolume_cons_smul μ (A + C) H (by norm_num),
    PolyhedralSupport.mixedVolume_cons_add]
  ring

theorem mixedVolume_midpoint_self {d : ℕ} (H : Fin d → ConvexBody E)
    (A C : ConvexBody E) (a : ℝ)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A H)) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C H)) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C H)) = a) :
    mixedVolume μ (Fin.cons (minkowskiMidpoint A C)
      (Fin.cons (minkowskiMidpoint A C) H)) = a := by
  rw [mixedVolume_midpoint_first]
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap μ A (minkowskiMidpoint A C),
    PolyhedralSupport.mixedVolume_cons_cons_swap μ C (minkowskiMidpoint A C)]
  rw [mixedVolume_midpoint_first, mixedVolume_midpoint_first]
  rw [PolyhedralSupport.mixedVolume_cons_cons_swap μ C A, hAA, hAC, hCC]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The one-sided first derivative of the actual Haar volume, obtained from
the same actual Minkowski polynomial used for the second-order deficit. -/
theorem hasDerivWithinAt_minkowskiRayVolume {d : ℕ}
    (K A : ConvexBody E) (hdim : finrank ℝ E = d + 1) :
    HasDerivWithinAt
      (fun t : ℝ => μ.real ((K + t • A : ConvexBody E) : Set E))
      ((d + 1 : ℝ) * mixedVolume μ (Fin.cons A (fun _ : Fin d => K)))
      (Ici 0) 0 := by
  have hp := HasDerivAt.hasDerivWithinAt (s := Ici (0 : ℝ))
    ((minkowskiRayPolynomial μ K A (d + 1)).hasDerivAt 0)
  rw [minkowskiRayPolynomial_first_zero] at hp
  apply hp.congr
  · intro t ht
    exact (minkowskiRayPolynomial_eval μ hdim K A t ht).symm
  · exact (minkowskiRayPolynomial_eval μ hdim K A 0 le_rfl).symm

set_option backward.isDefEq.respectTransparency false in
/-- Equality in the positive mixed-volume pairing forces equality of the
first volume derivatives. This records the mass cancellation needed when
passing from conditional expectations to unnormalised ridge integrals. -/
theorem actual_ray_volume_difference_derivative_zero {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    HasDerivWithinAt
      (fun t : ℝ => μ.real ((K + t • A : ConvexBody E) : Set E) -
        μ.real ((K + t • C : ConvexBody E) : Set E)) 0 (Ici 0) 0 := by
  have hfirst : mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) =
      mixedVolume μ (Fin.cons C (fun _ : Fin (d + 1) => K)) := by
    simpa only [MultilinearDiagonal.cons_const] using
      mixedVolume_equal_pairings_of_AF_equality μ hdim (fun _ : Fin d => K)
        A C a ha hAA hAC hCC K
  have h := (hasDerivWithinAt_minkowskiRayVolume μ K A hdim).fun_sub
    (hasDerivWithinAt_minkowskiRayVolume μ K C hdim)
  simpa only [hfirst, sub_self] using h

theorem ray_polynomials_cubic_contact_of_AF_equality {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    (X : ℝ[X]) ^ 3 ∣
        minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2) -
          minkowskiRayPolynomial μ K A (d + 2) ∧
      (X : ℝ[X]) ^ 3 ∣
        minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2) -
          minkowskiRayPolynomial μ K C (d + 2) := by
  have hfirst : mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) =
      mixedVolume μ (Fin.cons C (fun _ : Fin (d + 1) => K)) := by
    simpa only [MultilinearDiagonal.cons_const] using
      mixedVolume_equal_pairings_of_AF_equality μ hdim (fun _ : Fin d => K)
        A C a ha hAA hAC hCC K
  have hmfirst : mixedVolume μ
      (Fin.cons (minkowskiMidpoint A C) (fun _ : Fin (d + 1) => K)) =
        mixedVolume μ (Fin.cons A (fun _ : Fin (d + 1) => K)) := by
    rw [mixedVolume_midpoint_first, ← hfirst]
    ring
  have hmsecond := mixedVolume_midpoint_self μ (fun _ : Fin d => K) A C a hAA hAC hCC
  constructor
  · apply X_cube_dvd_sub_of_two_derivatives
    · rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
    · rw [minkowskiRayPolynomial_first_zero, minkowskiRayPolynomial_first_zero, hmfirst]
    · rw [minkowskiRayPolynomial_second_zero, minkowskiRayPolynomial_second_zero,
        hmsecond, hAA]
  · apply X_cube_dvd_sub_of_two_derivatives
    · rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
    · rw [minkowskiRayPolynomial_first_zero, minkowskiRayPolynomial_first_zero,
        hmfirst, hfirst]
    · rw [minkowskiRayPolynomial_second_zero, minkowskiRayPolynomial_second_zero,
        hmsecond, hCC]

/-- The quantitative-transport input obtained from actual AF equality:
the midpoint Brunn--Minkowski volume deficit is little-o of t² as t↓0.
Lower-dimensional comparison bodies A and C are allowed. -/
theorem actual_midpoint_deficit_little_o_sq {d : ℕ}
    (K : ConvexBody E) (hdim : finrank ℝ E = d + 2)
    (hK : 0 < μ.real (K : Set E))
    (A C : ConvexBody E) (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume μ (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume μ (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume μ (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a) :
    Tendsto (fun t : ℝ =>
      (μ.real ((K + t • minkowskiMidpoint A C : ConvexBody E) : Set E) -
        Real.sqrt
          (μ.real ((K + t • A : ConvexBody E) : Set E) *
            μ.real ((K + t • C : ConvexBody E) : Set E))) / t ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let P := minkowskiRayPolynomial μ K (minkowskiMidpoint A C) (d + 2)
  let PA := minkowskiRayPolynomial μ K A (d + 2)
  let PC := minkowskiRayPolynomial μ K C (d + 2)
  have h0A : P.eval 0 = PA.eval 0 := by
    rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
  have h0C : P.eval 0 = PC.eval 0 := by
    rw [minkowskiRayPolynomial_zero, minkowskiRayPolynomial_zero]
  have hpos : 0 < P.eval 0 := by
    rw [minkowskiRayPolynomial_zero, mixedVolume_diagonal μ hdim]
    exact hK
  obtain ⟨hA,hC⟩ := ray_polynomials_cubic_contact_of_AF_equality μ K hdim A C a ha hAA hAC hCC
  have hdiv : (X : ℝ[X]) ^ 3 ∣ P ^ 2 - PA * PC :=
    X_cube_dvd_midpoint_product P PA PC hA hC
  have hlim := (midpoint_sqrt_deficit_little_o_sq P PA PC h0A h0C hpos hdiv).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [minkowskiRayPolynomial_eval μ hdim K (minkowskiMidpoint A C) t ht.le,
    minkowskiRayPolynomial_eval μ hdim K A t ht.le,
    minkowskiRayPolynomial_eval μ hdim K C t ht.le]

end RankThreeProjection.Rigidity

