module

public import Projection.Rigidity.RadialMixedVolume
public import Projection.Rigidity.QuantileTranslation
public import Projection.Rigidity.VolumeDeficit
public import Projection.Rigidity.NormalizedVariation

/-!
# From normalized projected variations to the weak hull conclusion

The quantile argument uses conditional probability measures. The localized
radial formula uses unnormalized Lebesgue integrals. Equal first volume
derivatives remove this difference, including after the exact translation of
one comparison body. Every mass and numerator below is an actual integral.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function Module ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere sigma mean)
open VolumePolynomials RankThreeProjection.Rigidity

theorem conditional_integral_eq_div {n : ℕ} (K : Set (Space n)) (ψ : Space n → ℝ) :
    (∫ x, ψ x ∂volume[|K]) = (∫ x in K, ψ x) / volume.real K := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, measureReal_def, div_eq_mul_inv]
  rw [mul_comm]

/-- Removing normalization for one actual continuous spatial test. -/
theorem raw_variation_zero_of_conditional {d : ℕ}
    (K A B : ConvexBody (Space (d + 1)))
    (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 (0 : Space (d + 1)))
    (hmass : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))) -
        volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      0 (Ici 0) 0)
    (ψ : Space (d + 1) → ℝ) (hψ : Continuous ψ)
    (hnorm : HasDerivWithinAt
      (fun t : ℝ => (∫ x, ψ x
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, ψ x
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0) :
    HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))), ψ x) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))), ψ x)
      0 (Ici 0) 0 := by
  let V : ℝ → ℝ := fun t => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))
  let W : ℝ → ℝ := fun t => volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))
  let F : ℝ → ℝ := fun t => ∫ x in ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))), ψ x
  let G : ℝ → ℝ := fun t => ∫ x in ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))), ψ x
  have hdim : finrank ℝ (Space (d + 1)) = d + 1 := finrank_euclideanSpace_fin
  have hV := hasDerivWithinAt_minkowskiRayVolume volume K A hdim
  have hW := hasDerivWithinAt_minkowskiRayVolume volume K B hdim
  have hsame := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Ici 0) (hV.fun_sub hW) hmass
  have hsame' := sub_eq_zero.mp hsame
  rw [← hsame'] at hW
  have hF : HasDerivWithinAt F
      ((d + 1 : ℝ) * kappa (d + 1) * mean (fun u : Sphere (d + 1) =>
        bodyRadius (K : Set (Space (d + 1))) u ^ (d + 1) *
          ψ (radialBoundary (K : Set (Space (d + 1))) u) *
          support (A : Set (Space (d + 1)))
            (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))))) (Ici 0) 0 := by
    simpa only [F, ConvexBody.coe_add, ConvexBody.coe_smul, radialBoundary,
      Nat.cast_add, Nat.cast_one] using
      minkowski_integral_derivative K.isCompact K.convex h0 A.isCompact A.convex A.nonempty ψ hψ
  have hG : HasDerivWithinAt G
      ((d + 1 : ℝ) * kappa (d + 1) * mean (fun u : Sphere (d + 1) =>
        bodyRadius (K : Set (Space (d + 1))) u ^ (d + 1) *
          ψ (radialBoundary (K : Set (Space (d + 1))) u) *
          support (B : Set (Space (d + 1)))
            (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))))) (Ici 0) 0 := by
    simpa only [G, ConvexBody.coe_add, ConvexBody.coe_smul, radialBoundary,
      Nat.cast_add, Nat.cast_one] using
      minkowski_integral_derivative K.isCompact K.convex h0 B.isCompact B.convex B.nonempty ψ hψ
  have hVpos : 0 < V 0 := by
    simpa only [V, body_zero_smul, add_zero, Measure.real] using
      (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds volume h0).ne' K.isCompact.measure_lt_top.ne)
  have hz : HasDerivWithinAt (fun t => F t / V t - G t / W t) 0 (Ici 0) 0 := by
    simpa only [conditional_integral_eq_div, F, G, V, W] using hnorm
  have h := raw_difference_derivative_zero_of_normalized V W F G _ _ _ 0 (Ici 0)
    (uniqueDiffWithinAt_Ici 0) hV hW hF hG
    (by simp only [V, W, body_zero_smul, add_zero])
    (by simp only [F, G, body_zero_smul, add_zero]) hVpos.ne' hz
  simpa only [F, G, ConvexBody.coe_add, ConvexBody.coe_smul] using h

theorem mixedVolume_join_eq_of_conditional_ridge_variations {d : ℕ}
    (K A B : ConvexBody (Space (d + 1)))
    (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 (0 : Space (d + 1)))
    (hmass : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))) -
        volume.real ((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      0 (Ici 0) 0)
    (hcos : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, Real.cos ⟪x, ξ⟫
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))]) -
        ∫ x, Real.sin ⟪x, ξ⟫
          ∂volume[|((K + t • B : ConvexBody (Space (d + 1))) : Set (Space (d + 1)))])
      0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A B) (fun _ : Fin d => K)) =
      mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) := by
  exact (mixedVolume_join_eq_of_ridge_variations K A B h0
    (fun ξ => raw_variation_zero_of_conditional K A B h0 hmass _ (by fun_prop) (hcos ξ))
    (fun ξ => raw_variation_zero_of_conditional K A B h0 hmass _ (by fun_prop) (hsin ξ))).1

/-- Final radial assembly under actual AF equality. The only analytic input
is the centered conditional sine/cosine variation supplied by the quantiles. -/
theorem weak_hull_of_AF_conditional_ridge_variations {d : ℕ}
    (K A C : ConvexBody (Space (d + 2)))
    (h0 : (K : Set (Space (d + 2))) ∈ 𝓝 (0 : Space (d + 2)))
    (a : ℝ) (ha : 0 < a)
    (hAA : mixedVolume volume (Fin.cons A (Fin.cons A (fun _ : Fin d => K))) = a)
    (hAC : mixedVolume volume (Fin.cons A (Fin.cons C (fun _ : Fin d => K))) = a)
    (hCC : mixedVolume volume (Fin.cons C (Fin.cons C (fun _ : Fin d => K))) = a)
    (v : Space (d + 2))
    (hcos : ∀ ξ : Space (d + 2), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.cos ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]) -
        ∫ x, Real.cos ⟪x, ξ⟫
          ∂volume[|((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))])
      0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 2), HasDerivWithinAt
      (fun t : ℝ => (∫ x, Real.sin ⟪x, ξ⟫
        ∂volume[|((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))]) -
        ∫ x, Real.sin ⟪x, ξ⟫
          ∂volume[|((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2)))])
      0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (RankThreeProjection.joinBody A (translateBody v C))
      (Fin.cons K (fun _ : Fin d => K))) =
      mixedVolume volume (Fin.cons A (Fin.cons K (fun _ : Fin d => K))) := by
  have hdim : finrank ℝ (Space (d + 2)) = d + 2 := finrank_euclideanSpace_fin
  have hmass := actual_ray_volume_difference_derivative_zero volume K hdim A C a ha hAA hAC hCC
  have hmass' : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 2))) : Set (Space (d + 2))) -
        volume.real ((K + t • translateBody v C : ConvexBody (Space (d + 2))) : Set (Space (d + 2))))
      0 (Ici 0) 0 := by
    simpa only [minkowskiRay_volume_translate_comparison] using hmass
  simpa only [MultilinearDiagonal.cons_const] using
    mixedVolume_join_eq_of_conditional_ridge_variations K A (translateBody v C) h0 hmass' hcos hsin

end OAI.PettyProjection
