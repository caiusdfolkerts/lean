module

public import VolumePolynomials.HolonomySeries
public import VolumePolynomials.InfiniteBoundarySegments
public import VolumePolynomials.AffineSemialgebraic

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

/-- The exact infinite Minkowski body of (7.10) is not a semialgebraic subset of the plane. -/
theorem forcedBody_not_semialgebraic (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    ¬ TauCeti.IsSemialgebraic ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
      (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ))) := by
  first
  | obtain ⟨a, ha⟩ := forcedBody_boundary_segments lam hlam₀ hlam₁
    exact not_semialgebraic_of_nonparallel_boundary_segments _ a (weightedOrbit lam)
      (weightedOrbit_nonparallel lam hlam₀) (by simpa only [neg_div] using ha)

/-- Nonsemialgebraicity persists under every injective affine placement into any
finite-dimensional coordinate space, including the specified body in 3D. -/
theorem forcedBody_affine_image_not_semialgebraic
    (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) {m : ℕ}
    (L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Injective L)
    (v : Fin m → ℝ) :
    ¬ TauCeti.IsSemialgebraic ((fun x => v + L x) ''
      ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
        (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)))) :=
  not_semialgebraic_affine_image (forcedBody_not_semialgebraic lam hlam₀ hlam₁) L hL v

end VolumePolynomials.Holonomy
