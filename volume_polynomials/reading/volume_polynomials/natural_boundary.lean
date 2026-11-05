module

public import VolumePolynomials.RotationFrequencies
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology
open Set Filter Metric

/-- Local continuous continuation across a point of the unit circle. Excluding this
is stronger than excluding local holomorphic continuation. -/
def HasLocalContinuousExtension (F : ℂ → ℂ) (ζ : ℂ) : Prop :=
  ∃ δ > 0, ∃ g : ℂ → ℂ, ContinuousOn g (ball ζ δ) ∧
    ∀ z ∈ ball ζ δ, ‖z‖ < 1 → g z = F z

def radialSequence (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem radialSequence_nonneg (n : ℕ) : 0 ≤ radialSequence n := by
  first
  | unfold radialSequence
    positivity

theorem radialSequence_lt_one (n : ℕ) : radialSequence n < 1 := by
  first
  | unfold radialSequence
    apply (div_lt_one (by positivity)).mpr
    linarith

theorem radialSequence_tendsto : Tendsto radialSequence atTop (𝓝 1) :=
  tendsto_natCast_div_add_atTop (1 : ℝ)

/-- Dense, nonzero Cauchy residues rule out local continuous continuation everywhere on the circle. -/
theorem dense_cauchy_no_boundary_extension {ι : Type*} (β : ι → ℂ) (u : ι → Circle)
    (hβ : Summable fun i => ‖β i‖) (hβne : ∀ i, β i ≠ 0)
    (huinj : Function.Injective u) (hudense : DenseRange u) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (weightedCauchySeries β (fun i => (u i : ℂ))) ζ := by
  first
  | rintro ⟨δ, hδ, g, hgcont, hgeq⟩
    have hdinv : DenseRange (fun i => (u i)⁻¹) :=
      (inv_involutive.surjective.denseRange).comp hudense continuous_inv
    have hopen : IsOpen ((fun z : Circle => (z : ℂ)) ⁻¹' ball (ζ : ℂ) δ) :=
      isOpen_ball.preimage continuous_subtype_val
    have hnonempty : (((fun z : Circle => (z : ℂ)) ⁻¹' ball (ζ : ℂ) δ)).Nonempty :=
      ⟨ζ, mem_ball_self hδ⟩
    obtain ⟨j, hj⟩ := hdinv.exists_mem_open hopen hnonempty
    change ((u j : ℂ)⁻¹) ∈ ball (ζ : ℂ) δ at hj
    have huj : (u j : ℂ) ≠ 0 := by
      first
      | intro h
        simpa [h] using (u j).norm_coe
    have hrC : Tendsto (fun n => (radialSequence n : ℂ)) atTop (𝓝 1) := by
      first
      | simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp radialSequence_tendsto
    have hray : Tendsto (fun n => (radialSequence n : ℂ) / u j)
        atTop (𝓝 ((u j : ℂ)⁻¹)) := by
      first
      | simpa only [one_div] using hrC.div_const (u j : ℂ)
    have hgpoint : ContinuousAt g ((u j : ℂ)⁻¹) := hgcont.continuousAt (isOpen_ball.mem_nhds hj)
    have hlimit : Tendsto (fun n => g ((radialSequence n : ℂ) / u j))
        atTop (𝓝 (g ((u j : ℂ)⁻¹))) := by
      first
      | simpa only [Function.comp_def] using hgpoint.tendsto.comp hray
    have hinside (n : ℕ) : ‖(radialSequence n : ℂ) / u j‖ < 1 := by
      first
      | simpa [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (radialSequence_nonneg n)] using radialSequence_lt_one n
    have hagree : ∀ᶠ n in atTop,
        g ((radialSequence n : ℂ) / u j) =
          weightedCauchySeries β (fun i => (u i : ℂ)) ((radialSequence n : ℂ) / u j) := by
      first
      | filter_upwards [hray (isOpen_ball.mem_nhds hj)] with n hn
        exact hgeq _ hn (hinside n)
    exact no_finite_radial_limit β (fun i => (u i : ℂ)) hβ (fun i => (u i).norm_coe)
      (Subtype.coe_injective.comp huinj) radialSequence radialSequence_nonneg
      radialSequence_lt_one radialSequence_tendsto j (hβne j)
      ⟨g ((u j : ℂ)⁻¹), hlimit.congr' hagree⟩

/-- The unit circle is a boundary of continuous continuation for the actual |sin(nθ)| series. -/
theorem sineGeneratingFunction_no_boundary_extension {θ : ℝ}
    (hθ : Real.cos θ = 1 / 3) (ζ : Circle) :
    ¬ HasLocalContinuousExtension (sineGeneratingFunction θ) ζ := by
  first
  | intro h
    apply dense_cauchy_no_boundary_extension sineFourierCoefficient (rotationUnit θ)
      sineFourier_summable_norm sineFourier_ne_zero (rotationUnit_injective hθ)
      (rotationUnit_dense hθ) ζ
    obtain ⟨δ, hδ, g, hg, hgeq⟩ := h
    refine ⟨δ, hδ, g, hg, ?_⟩
    intro z hz hznorm
    rw [hgeq z hz hznorm, sineGeneratingFunction_eq_cauchy θ z hznorm]
    simp only [rotationUnit_coe]

end VolumePolynomials
