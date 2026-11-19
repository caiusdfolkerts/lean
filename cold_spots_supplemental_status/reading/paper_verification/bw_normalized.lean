module

public import PaperVerification.BWTheorems
public import PaperVerification.BWConstruction
public import PaperVerification.LatticeScaling

@[expose] public section
/-! # The usual integral Barnes–Wall normalization

The set is the explicit √2 scaling of D₁₆+½RM(1,4).  Its squared covering radius
is three, and its universal Gaussian cold spots are exactly all its deep holes.
-/

noncomputable section

namespace PaperVerification.ColdSpots

def bw16Set : Set (Fin 16 → ℝ) := scaledSet (Real.sqrt 2) bwRMConstruction

theorem bw16Set_eq_scaledGamma : bw16Set = scaledSet (Real.sqrt 2) bwGammaSet := by
  rw [bw16Set, bwGammaSet_eq_RMConstruction]

theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem setGaussian_bw16 (α : ℝ) (x : Fin 16 → ℝ) :
    setGaussian bw16Set α (scaleVec (Real.sqrt 2) x) = setGaussian bwGammaSet (2 * α) x := by
  rw [bw16Set_eq_scaledGamma, setGaussian_scaled _ sqrt_two_ne_zero,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), mul_comm α 2]

theorem summable_setGaussian_bw16 {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    Summable (fun v : bw16Set => Real.exp (-α * sqDist v.val z)) := by
  rw [bw16Set_eq_scaledGamma]
  have h := (summable_scaled_iff (Real.sqrt 2) sqrt_two_ne_zero bwGammaSet α
    (scaleVec (Real.sqrt 2)⁻¹ z)).mpr (by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact summable_setGaussian_bwGamma (by positivity) _)
  simpa only [scaleVec_inv _ sqrt_two_ne_zero] using h

theorem squaredDepth_bw16 (x : Fin 16 → ℝ) :
    squaredDepth bw16Set (scaleVec (Real.sqrt 2) x) = 2 * squaredDepth bwGammaSet x := by
  rw [bw16Set_eq_scaledGamma, squaredDepth_scaled _ sqrt_two_ne_zero _ bwGamma_nonempty,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The Barnes–Wall assertion of Theorem 1.1 in its stated integral normalization. -/
theorem coldSpot_bw16_iff_deepHole {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bw16Set α z ↔ IsDeepHole bw16Set z := by
  have hz := scaleVec_inv (Real.sqrt 2) sqrt_two_ne_zero z
  conv_lhs => arg 3; rw [← hz]
  conv_rhs => arg 2; rw [← hz]
  rw [bw16Set_eq_scaledGamma, isColdSpot_scaled_iff _ sqrt_two_ne_zero,
    isDeepHole_scaled_iff _ sqrt_two_ne_zero _ bwGamma_nonempty,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact coldSpot_bwGamma_iff_deepHole (by positivity) _

/-- Squared covering radius three, with a displayed attaining point. -/
theorem bw16_squared_covering_radius :
    (∀ z : Fin 16 → ℝ, squaredDepth bw16Set z ≤ 3) ∧
      ∃ z, squaredDepth bw16Set z = 3 := by
  constructor
  · intro z
    have h := squaredDepth_bwGamma_le (scaleVec (Real.sqrt 2)⁻¹ z)
    have hd := squaredDepth_bw16 (scaleVec (Real.sqrt 2)⁻¹ z)
    rw [scaleVec_inv _ sqrt_two_ne_zero] at hd
    linarith
  · refine ⟨scaleVec (Real.sqrt 2) (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint), ?_⟩
    rw [squaredDepth_bw16, squaredDepth_bwGamma_witness]
    norm_num

/-- The exact attained Gaussian minimum for every positive parameter. -/
theorem bw16_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ, bwGammaMinimum (2 * α) ≤ setGaussian bw16Set α z) ∧
      ∃ z, setGaussian bw16Set α z = bwGammaMinimum (2 * α) := by
  constructor
  · intro z
    have h := setGaussian_bwGamma_lower (by positivity : 0 < 2 * α) (scaleVec (Real.sqrt 2)⁻¹ z)
    have hg := setGaussian_bw16 α (scaleVec (Real.sqrt 2)⁻¹ z)
    rw [scaleVec_inv _ sqrt_two_ne_zero] at hg
    exact hg.symm ▸ h
  · refine ⟨scaleVec (Real.sqrt 2) (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint), ?_⟩
    rw [setGaussian_bw16]
    exact setGaussian_bwGamma_witness (by positivity)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_bw16_iff_deepHole
#print axioms PaperVerification.ColdSpots.bw16_squared_covering_radius
#print axioms PaperVerification.ColdSpots.bw16_gaussian_minimum
