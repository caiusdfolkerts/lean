module

public import PaperVerification.E8Theorems
public import PaperVerification.LatticeE8Families

@[expose] public section

noncomputable section

namespace PaperVerification.ColdSpots

theorem coldSpot_E8_iff_paper_families {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    IsColdSpot (dPlusSet 8) α x ↔ E8PaperHole x :=
  (coldSpot_E8_iff_deepHole hα x).trans (isDeepHole_E8_iff_paper x)

theorem gaussian_E8_minimum_iff_paper_families {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    setGaussian (dPlusSet 8) α x=(gaussian α 0*gaussian α (1/2))^4 ↔ E8PaperHole x := by
  rw [setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_eight_eq_min_iff hα,e8FoldedHole_iff_paper]

end PaperVerification.ColdSpots
