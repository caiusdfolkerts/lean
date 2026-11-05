module

public import Projection.Rigidity.RadialBoundary
public import Projection.Rigidity.VolumeDeficit
public import Projection.ConvexHullValuation

/-!
# The weak mixed-volume consequence of projected equality

This file connects the radial first variation of actual volume to the mixed
volume already defined by the Minkowski polynomial. A convex-hull argument
then extracts the nonnegative support difference needed for weak rigidity.
The conclusion is an equality of genuine mixed volumes, so it transfers
between Euclidean and other finite-dimensional normed coordinate models
without transporting any normal sphere or area measure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric Filter Topology Function Module
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient

namespace OAI.PettyProjection
open Spherical (Sphere norm_coe sigma mean)
open VolumePolynomials RankThreeProjection

theorem support_joinBody {n : ℕ} (A B : ConvexBody (Space n)) (u : Space n) :
    support (joinBody A B : Set (Space n)) u =
      max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) := by
  apply le_antisymm
  · apply (support_le_iff (joinBody A B).isCompact (joinBody A B).nonempty).mpr
    intro z hz
    obtain ⟨a, ha, b, hb, r, t, hr, ht, hrt, rfl⟩ := mem_convexJoin.mp hz
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have ha' := (inner_le_support A.isCompact ha u).trans
      (le_max_left (support (A : Set (Space n)) u) (support (B : Set (Space n)) u))
    have hb' := (inner_le_support B.isCompact hb u).trans
      (le_max_right (support (A : Set (Space n)) u) (support (B : Set (Space n)) u))
    calc
      _ ≤ r * max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) +
          t * max (support (A : Set (Space n)) u) (support (B : Set (Space n)) u) :=
        add_le_add (mul_le_mul_of_nonneg_left ha' hr) (mul_le_mul_of_nonneg_left hb' ht)
      _ = _ := by rw [← add_mul, hrt, one_mul]
  · apply max_le
    · obtain ⟨a, ha, hea⟩ := support_attained A.isCompact A.nonempty u
      rw [hea]
      exact inner_le_support (joinBody A B).isCompact (le_joinBody_left A B ha) u
    · obtain ⟨b, hb, heb⟩ := support_attained B.isCompact B.nonempty u
      rw [heb]
      exact inner_le_support (joinBody A B).isCompact (le_joinBody_right A B hb) u

/-- First variation of actual Minkowski volume, identified with the exact
coefficient of its actual volume polynomial. -/
theorem mixedVolume_first_radial {d : ℕ}
    (K A : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0) :
    (d + 1 : ℝ) * mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) =
      (d + 1 : ℝ) * kappa (d + 1) *
        ∫ u, radialDensity (K : Set (Space (d + 1)))
          (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
  have hdim : finrank ℝ (Space (d + 1)) = d + 1 := finrank_euclideanSpace_fin
  have hp' := RankThreeProjection.Rigidity.hasDerivWithinAt_minkowskiRayVolume
    volume K A hdim
  have hr := minkowski_volume_derivative K.isCompact K.convex h0 A.isCompact A.convex A.nonempty
  have hr' : HasDerivWithinAt
      (fun t : ℝ => volume.real ((K + t • A : ConvexBody (Space (d + 1))) : Set (Space (d + 1))))
      ((d + 1 : ℝ) * kappa (d + 1) *
        ∫ u, radialDensity (K : Set (Space (d + 1)))
          (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1)) (Ici 0) 0 := by
    simpa only [ConvexBody.coe_add, ConvexBody.coe_smul, radialDensity, bodyRadius,
      mean, Nat.cast_add, Nat.cast_one] using hr
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv (Ici 0) hp' hr'

/-- Equality at almost every radial normal makes the first mixed volume of
the actual convex hull equal to that of each comparison body. -/
theorem mixedVolume_join_eq_of_radial_equality {d : ℕ}
    (K A B : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0)
    (he : ∀ᵐ (u : Sphere (d + 1)) ∂sigma (d + 1),
      support (A : Set (Space (d + 1))) (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1))) =
      support (B : Set (Space (d + 1))) (∇ (gauge (K : Set (Space (d + 1)))) (u : Space (d + 1)))) :
    mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) ∧
      mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons B (fun _ : Fin d => K)) := by
  have hI : (∫ u, radialDensity (K : Set (Space (d + 1)))
      (support (joinBody A B : Set (Space (d + 1)))) u ∂sigma (d + 1)) =
      ∫ u, radialDensity (K : Set (Space (d + 1)))
        (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [radialDensity, support_joinBody, ← hu, max_self]
  have hAB : (∫ u, radialDensity (K : Set (Space (d + 1)))
      (support (A : Set (Space (d + 1)))) u ∂sigma (d + 1)) =
      ∫ u, radialDensity (K : Set (Space (d + 1)))
        (support (B : Set (Space (d + 1)))) u ∂sigma (d + 1) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [radialDensity, hu]
  have hn : (d + 1 : ℝ) ≠ 0 := by positivity
  constructor
  · apply mul_left_cancel₀ hn
    rw [mixedVolume_first_radial K (joinBody A B) h0, mixedVolume_first_radial K A h0, hI]
  · apply mul_left_cancel₀ hn
    rw [mixedVolume_first_radial K (joinBody A B) h0, mixedVolume_first_radial K B h0, hI, hAB]

/-- Norm-independent weak conclusion from equality of the actual projected
first variations. This is the exact bridge consumed by convex-hull rigidity. -/
theorem mixedVolume_join_eq_of_ridge_variations {d : ℕ}
    (K A B : ConvexBody (Space (d + 1))) (h0 : (K : Set (Space (d + 1))) ∈ 𝓝 0)
    (hcos : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))),
        Real.cos ⟪x, ξ⟫) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))),
          Real.cos ⟪x, ξ⟫) 0 (Ici 0) 0)
    (hsin : ∀ ξ : Space (d + 1), HasDerivWithinAt
      (fun t : ℝ => (∫ x in (K : Set (Space (d + 1))) + t • (A : Set (Space (d + 1))),
        Real.sin ⟪x, ξ⟫) -
        ∫ x in (K : Set (Space (d + 1))) + t • (B : Set (Space (d + 1))),
          Real.sin ⟪x, ξ⟫) 0 (Ici 0) 0) :
    mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons A (fun _ : Fin d => K)) ∧
      mixedVolume volume (Fin.cons (joinBody A B) (fun _ : Fin d => K)) =
        mixedVolume volume (Fin.cons B (fun _ : Fin d => K)) := by
  apply mixedVolume_join_eq_of_radial_equality K A B h0
  exact support_gradient_ae_eq_of_ridge_variations K.isCompact K.convex h0
    A.isCompact A.convex A.nonempty B.isCompact B.convex B.nonempty hcos hsin

end OAI.PettyProjection
