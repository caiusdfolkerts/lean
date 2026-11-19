module

public import ToricPower.SubfanBoundaryCharacters
public import ToricPower.ToricRestrictionCohomology

/-!
# Eventual nonvanishing of the actual boundary-twisted line cohomology

A nonzero cohomology class on the original toric variety has a nonzero
character summand in its genuine affine Čech complex. The exact
character-complex stabilization proves nonvanishing on the extension
for every sufficiently large boundary twist. No injectivity of
cohomology transition maps, bounded character search, or cohomology
colimit assertion is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan extension : Fan i) (included : fan.cones ⊆ extension.cones)

include included in
theorem subfanExtension_nonempty (nonempty : Nonempty fan.cones) : Nonempty extension.cones :=
  nonempty.map (subfanConeEmbedding fan extension included)

/-- Nonzero total cohomology persists at every later boundary twist.
This statement concerns the literal invariant Cartier sheaves on the
two actual toric schemes. The extension need not itself be complete. -/
theorem subfanBoundaryCohomology_eventually
    (nonempty : Nonempty fan.cones) (regular : extension.IsRegular)
    (rayFull : IsFullOnRays fan extension) (b : fan.Ray → ℤ)
    (nonzero : ∃ q : ℕ, Nontrivial (invariantDivisorCohomology fan nonempty
      (subfan_isRegular fan extension included regular) b q)) :
    ∃ threshold : ℕ, ∀ a : ℕ, threshold ≤ a →
      ∃ q : ℕ, Nontrivial (invariantDivisorCohomology extension
        (subfanExtension_nonempty fan extension included nonempty) regular
        (subfanBoundaryTwist fan extension b a) q) := by
  let newNonempty := subfanExtension_nonempty fan extension included nonempty
  let oldRegular := subfan_isRegular fan extension included regular
  letI := toricSchemeIntegral fan nonempty
  letI := toricSchemeIntegral extension newNonempty
  obtain ⟨m,q,hq⟩ := (toricCartierCohomologyWeight_nonzero_iff fan nonempty oldRegular
    (subfanRetractedCechCharts fan extension regular rayFull)
    (subfanRetractedCechCharts_surjective fan extension included regular rayFull) b).mp nonzero
  refine ⟨subfanBoundaryThreshold extension m,?_⟩
  intro a large
  apply (toricCartierCohomologyWeight_nonzero_iff extension newNonempty regular
    (toricFiniteCechCharts extension) (toricFiniteCechCharts_surjective extension)
    (subfanBoundaryTwist fan extension b a)).mpr
  refine ⟨m,q,?_⟩
  exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) q).mapIso
    (subfanBoundaryTwistWeightIso fan extension included regular rayFull b m a large)).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.mpr hq

end ToricPower

end
