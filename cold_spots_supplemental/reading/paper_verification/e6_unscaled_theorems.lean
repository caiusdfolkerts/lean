module

public import PaperVerification.E6Geometry
public import PaperVerification.E6Polarization

@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem l6Gaussian_witness {α : ℝ} (hα : 0 < α) :
    l6Gaussian α e6HoleWitness=3*triangularGaussian α 0*triangularGaussian α triC^2 :=
  (l6Gaussian_equality_iff hα _).mpr e6HoleWitness_balanced

theorem isL6ColdSpot_iff {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsL6ColdSpot α z ↔ E6BalancedPhases z := by
  rw [← l6Gaussian_equality_iff hα]
  constructor
  · intro h
    have hw := h e6HoleWitness
    rw [l6Gaussian_witness hα] at hw
    exact le_antisymm hw (l6Gaussian_lower hα z)
  · intro h w
    rw [h]
    exact l6Gaussian_lower hα w

theorem coldSpot_L6_iff_deepHole {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsL6ColdSpot α z ↔ IsL6DeepHole z := by
  rw [isL6ColdSpot_iff hα,isL6DeepHole_iff]

end PaperVerification.ColdSpots
