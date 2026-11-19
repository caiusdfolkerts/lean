module
public import PaperVerification.BWHoles
public import PaperVerification.E8Theorems
@[expose] public section
/-! # Universal cold spots of the diagonal Barnes–Wall lattice

All analytic inputs are the proved E8 theorem at α and α/2.  The actual finite
coset factorization and the complete geometric equality criterion give the result
for every real point and every positive parameter.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def bwK (α : ℝ) : ℝ := (gaussian α 0 * gaussian α (1 / 2)) ^ 4
def bwS (α : ℝ) : ℝ := bwK (α / 2)
def bwGammaMinimum (α : ℝ) : ℝ := 2 * bwK α * bwS α - 16 * bwK α ^ 2

theorem bwK_pos {α : ℝ} (hα : 0 < α) : 0 < bwK α :=
  pow_pos (mul_pos (gaussian_pos hα _) (gaussian_pos hα _)) _

theorem bwThetaProfile_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) (q : BWQuotient) :
    bwK α ≤ bwThetaProfile α x q := by
  rw [bwThetaProfile, setGaussian_dPlus_eq (by decide : 0 < 8) hα]
  exact dPlusGaussian_eight_lower hα _

theorem bwThetaProfile_eq_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) (q : BWQuotient) :
    bwThetaProfile α x q = bwK α ↔ bwDepthProfile x q = 1 := by
  rw [bwThetaProfile, bwK, setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_eight_eq_min_iff hα, bwDepthProfile, squaredDepth_E8_eq_one_iff]

theorem bwThetaProfile_sum_lower {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    bwS α ≤ ∑ q : BWQuotient, bwThetaProfile α x q := by
  rw [← setGaussian_bwM_eq_sum_profiles hα, setGaussian_bwM,
    setGaussian_dPlus_eq (by decide : 0 < 8) (by positivity : 0 < α / 2)]
  exact dPlusGaussian_eight_lower (by positivity) _

theorem bwThetaProfile_sum_eq_iff {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    (∑ q : BWQuotient, bwThetaProfile α x q) = bwS α ↔ squaredDepth bwMSet x = 1 / 2 := by
  rw [← setGaussian_bwM_eq_sum_profiles hα, setGaussian_bwM,
    setGaussian_dPlus_eq (by decide : 0 < 8) (by positivity : 0 < α / 2)]
  change dPlusGaussian (α / 2) (fun i => 2 * halfHadamard x i) = bwK (α / 2) ↔ _
  rw [bwK, dPlusGaussian_eight_eq_min_iff (by positivity : 0 < α / 2),
    ← squaredDepth_E8_eq_one_iff, squaredDepth_bwM]
  constructor <;> intro h <;> linarith

/-- The sharp global bound for the actual diagonal lattice. -/
theorem setGaussian_bwGamma_lower {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    bwGammaMinimum α ≤ setGaussian bwGammaSet α z := by
  rw [← append_bw_blocks z, setGaussian_bwGamma_eq_sum_profiles hα]
  have h := PaperVerification.Lattice.diagonal_gluing_bound Finset.univ
    (bwThetaProfile α (bwLeft z)) (bwThetaProfile α (bwRight z)) (bwK α) (bwS α)
    (bwK_pos hα).le (fun q _ => bwThetaProfile_lower hα _ q)
    (fun q _ => bwThetaProfile_lower hα _ q) (bwThetaProfile_sum_lower hα _)
    (bwThetaProfile_sum_lower hα _)
  simpa only [Finset.card_univ, card_bwQuotient, Nat.cast_ofNat, bwGammaMinimum] using h

/-- Exact Gaussian equality is the complete geometric gluing condition. -/
theorem setGaussian_bwGamma_eq_min_iff {α : ℝ} (hα : 0 < α) (x y : Fin 8 → ℝ) :
    setGaussian bwGammaSet α (Fin.append x y) = bwGammaMinimum α ↔ BWGluingCondition x y := by
  rw [setGaussian_bwGamma_eq_sum_profiles hα]
  have h := PaperVerification.Lattice.diagonal_gluing_eq_iff Finset.univ
    (bwThetaProfile α x) (bwThetaProfile α y) (bwK α) (bwS α)
    (bwK_pos hα) (fun q _ => bwThetaProfile_lower hα _ q)
    (fun q _ => bwThetaProfile_lower hα _ q) (bwThetaProfile_sum_lower hα _)
    (bwThetaProfile_sum_lower hα _)
  simpa only [Finset.card_univ, card_bwQuotient, Nat.cast_ofNat, Finset.mem_univ,
    forall_const, bwGammaMinimum, BWGluingCondition, bwThetaProfile_sum_eq_iff hα,
    bwThetaProfile_eq_iff hα] using h

theorem setGaussian_bwGamma_witness {α : ℝ} (hα : 0 < α) :
    setGaussian bwGammaSet α (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint) =
      bwGammaMinimum α :=
  (setGaussian_bwGamma_eq_min_iff hα _ _).mpr bw_witness_gluing

theorem isColdSpot_bwGamma_iff_value {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bwGammaSet α z ↔ setGaussian bwGammaSet α z = bwGammaMinimum α := by
  constructor
  · intro h
    have hw := h (Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint)
    rw [setGaussian_bwGamma_witness hα] at hw
    exact le_antisymm hw (setGaussian_bwGamma_lower hα z)
  · intro hz y
    rw [hz]
    exact setGaussian_bwGamma_lower hα y

/-- Theorem 1.1 for Γ, with every parameter and ambient coordinate unrestricted. -/
theorem coldSpot_bwGamma_iff_deepHole {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    IsColdSpot bwGammaSet α z ↔ IsDeepHole bwGammaSet z := by
  rw [isColdSpot_bwGamma_iff_value hα, isDeepHole_bwGamma_iff_depth,
    ← append_bw_blocks z, setGaussian_bwGamma_eq_min_iff hα, squaredDepth_bwGamma_eq_iff]

/-- The sharp value is attained and is a lower bound at every real point. -/
theorem bwGamma_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ, bwGammaMinimum α ≤ setGaussian bwGammaSet α z) ∧
      ∃ z, setGaussian bwGammaSet α z = bwGammaMinimum α :=
  ⟨setGaussian_bwGamma_lower hα,
    ⟨Fin.append (bwQuarterPoint + e8FirstVector) bwQuarterPoint, setGaussian_bwGamma_witness hα⟩⟩

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.coldSpot_bwGamma_iff_deepHole
#print axioms PaperVerification.ColdSpots.bwGamma_gaussian_minimum
