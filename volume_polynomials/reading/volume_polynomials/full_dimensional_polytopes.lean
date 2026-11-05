module
public import VolumePolynomials.PolytopeDensity
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace VolumePolynomials

/-- No complexity or vertex bound is imposed on the polytopes. This is a transfer
lemma: the nonsemialgebraicity of the full convex-body locus must be established
before applying it. -/
theorem fullDimensionalPolytopeLocus_not_semialgebraic_of_volumeLocus
    {n d : ℕ} (hd : 0 < d) (h : ¬ TauCeti.IsSemialgebraic (VolumeLocus n d)) :
    ¬ TauCeti.IsSemialgebraic (FullDimensionalPolytopeLocus n d) := by
  first
  | intro hp
    apply h
    rw [← closure_fullDimensionalPolytopeLocus n d hd]
    exact hp.closure

end VolumePolynomials
