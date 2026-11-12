module

public import ToricPower.SubfanBoundaryCohomology
public import ToricPower.RestrictedSubfanBoundary
public import ToricPower.ToricActualRestrictionCohomology

/-!
# Boundary stabilization for the literal subspace pullbacks

The restricted fans use the original saturated lattice trace. Their
boundary coefficients are exactly the restrictions of the ambient
boundary coefficients. Consequently the character-complex argument
proves eventual nonvanishing of the actual sheaf pullbacks in every
rational subspace, with no completeness assumption in this comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

/-- A nonzero cohomology class on the original literal subspace pullback
gives nonzero cohomology on the extended pullback at every sufficiently
large nonnegative boundary twist. -/
theorem subfanBoundaryPullbackCohomology_eventually
    (nonempty : Nonempty fan.cones) (regular : extension.IsRegular)
    (rayFull : IsFullOnRays fan extension) (b : fan.Ray → ℤ)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (nonzero : letI := toricSchemeIntegral fan nonempty
      ∃ q : ℕ, Nontrivial (toricSubspacePullbackCohomology fan
        (invariantCartierDivisor fan nonempty
          (subfan_isRegular fan extension included regular) b).sheaf W rational q)) :
    let newNonempty := subfanExtension_nonempty fan extension included nonempty
    letI := toricSchemeIntegral extension newNonempty
    ∃ threshold : ℕ, ∀ a : ℕ, threshold ≤ a →
      ∃ q : ℕ, Nontrivial (toricSubspacePullbackCohomology extension
        (invariantCartierDivisor extension newNonempty regular
          (subfanBoundaryTwist fan extension b a)).sheaf W rational q) := by
  let oldRegular := subfan_isRegular fan extension included regular
  let newNonempty := subfanExtension_nonempty fan extension included nonempty
  letI := toricSchemeIntegral fan nonempty
  letI := toricSchemeIntegral extension newNonempty
  have old := (toricSubspacePullback_nonzero_iff_invariant fan nonempty oldRegular
    W rational b).mp nonzero
  obtain ⟨threshold,eventual⟩ := subfanBoundaryCohomology_eventually
    (restrictedFan fan W rational) (restrictedFan extension W rational)
    (restrictedFan_cones_subset fan extension included W rational)
    (restrictedFan_cones_nonempty fan nonempty W rational)
    (restrictedFan_isRegular extension regular W rational)
    (isFullOnRays_restricted fan extension W rational rayFull)
    (restrictedFanRayCoefficients fan W rational b) old
  refine ⟨threshold,?_⟩
  intro a large
  apply (toricSubspacePullback_nonzero_iff_invariant extension newNonempty regular
    W rational (subfanBoundaryTwist fan extension b a)).mpr
  simpa only [restrictedSubfanBoundaryTwist fan extension W rational b a] using
    eventual a large

end ToricPower

end
