module

public import ToricPower.ToricActualRestrictionCohomology
public import ToricPower.ToricFiniteCohomologyPatterns
public import ToricPower.ToricInvariantLineBundleClassification

/-!
# The complete finite criterion for all linear cohomology tests

For every actual invertible sheaf on a smooth finite toric variety,
nonvanishing on every rational linear subspace is equivalent to the finite
ray-span and integer-pattern criterion of Section 5. The left side uses
the literal sheaf pullback along each actual subspace inclusion. The right
side ranges over the finite set of ray-generated linear subspaces and the
finite powerset of their genuine rays, with unbounded integral lattice
feasibility retained exactly.

The reduction is independent of Theorem 1.1. Combining it with that
categorical generation theorem yields the generation assertion of
Theorem 5.2; no generation assertion is assumed or claimed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Actual isomorphic coefficient sheaves have isomorphic actual
subspace-pullback cohomology, in every degree. -/
def toricSubspacePullbackCohomologyIso_of_iso (fan : Fan i)
    {F G : fan.algebraicRealization.Modules} (comparison : F ≅ G)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) (degree : ℕ) :
    AddCommGrpCat.of (toricSubspacePullbackCohomology fan F W hW degree) ≅
      AddCommGrpCat.of (toricSubspacePullbackCohomology fan G W hW degree) :=
  (cohomologyFunctor (restrictedFan fan W hW).algebraicRealization degree).mapIso
    ((Scheme.Modules.pullback (restrictedFanInclusion fan W hW).algebraicMap).mapIso comparison)

theorem toricSubspacePullback_nonzero_iff_of_iso (fan : Fan i)
    {F G : fan.algebraicRealization.Modules} (comparison : F ≅ G)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W hW degree)) ↔
    ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan G W hW degree) := by
  apply exists_congr
  intro degree
  exact (toricSubspacePullbackCohomologyIso_of_iso fan comparison W hW degree).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr

/-- The ray-span reduction for every actual line bundle, without a given
linearization or a supplied invariant-representative hypothesis. -/
theorem toricLineBundleSubspace_nonzero_iff_rayCore (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W hW degree)) ↔
    ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F (linearRayCore fan W)
      (fanRaySpan_rational fan (fanRaysIn fan W)) degree) := by
  letI := toricSchemeIntegral fan nonempty
  let b := toricLineBundleInvariantCoefficients fan nonempty regular F
  let comparison := toricLineBundleInvariantIso fan nonempty regular F
  exact (toricSubspacePullback_nonzero_iff_of_iso fan comparison W hW).trans
    ((toricSubspacePullback_nonzero_iff_rayCore fan nonempty regular W hW b).trans
      (toricSubspacePullback_nonzero_iff_of_iso fan comparison (linearRayCore fan W)
        (fanRaySpan_rational fan (fanRaysIn fan W))).symm)

/-- The retained test subspaces described in Section 5: actual rational
linear subspaces that are spanned by subsets of the original fan rays. -/
def rayGeneratedLinearTests (fan : Fan i) : Set (LinearSubspace fan) :=
  {W | W.space ∈ Set.range (fanRaySpan fan)}

/-- Finiteness is proved from the finite actual ray set, not built into
the definition of the test family. -/
theorem rayGeneratedLinearTests_finite (fan : Fan i) :
    (rayGeneratedLinearTests fan).Finite := by
  have finiteImage : (LinearSubspace.space '' rayGeneratedLinearTests fan).Finite :=
    (fanRaySpan_range_finite fan).subset (by
      rintro space ⟨W, present, rfl⟩
      exact present)
  exact finiteImage.of_finite_image (LinearSubspace.space_injective fan).injOn

/-- The original full family of rational linear cohomology tests, using
literal module-sheaf pullbacks and all nonnegative cohomological degrees. -/
def toricLineBundleLinearCohomologyCriterion (fan : Fan i)
    (F : fan.algebraicRealization.Modules) : Prop :=
  ∀ W : LinearSubspace fan,
    ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W.space W.rational degree)

/-- The full family is equivalent to the actual finite family of retained
ray spans, for every line bundle on every smooth finite toric variety. -/
theorem toricLinearCohomologyCriterion_iff_rayGenerated (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    toricLineBundleLinearCohomologyCriterion fan F ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W.space W.rational degree) := by
  constructor
  · intro all W _
    exact all W
  · intro finiteTests W
    apply (toricLineBundleSubspace_nonzero_iff_rayCore fan nonempty regular F
      W.space W.rational).mpr
    exact finiteTests (rayReducedLinearTest fan W) ⟨fanRaysIn fan W.space, rfl⟩

/-- On every rational subspace, the actual line-sheaf pullback is tested
by exactly the finite patterns and full-lattice inequalities of Section 5. -/
theorem toricLineBundleSubspace_nonzero_iff_finitePattern (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W hW degree)) ↔
      toricFiniteCohomologyPatternCriterion (restrictedFan fan W hW)
        (restrictedFanRayCoefficients fan W hW
          (toricLineBundleInvariantCoefficients fan nonempty regular F)) := by
  letI := toricSchemeIntegral fan nonempty
  let b := toricLineBundleInvariantCoefficients fan nonempty regular F
  exact (toricSubspacePullback_nonzero_iff_of_iso fan
      (toricLineBundleInvariantIso fan nonempty regular F) W hW).trans
    ((toricSubspacePullback_nonzero_iff_invariant fan nonempty regular W hW b).trans
      (toricCartierCohomology_nonzero_iff_finitePattern (restrictedFan fan W hW)
        (restrictedFan_cones_nonempty fan nonempty W hW)
        (restrictedFan_isRegular fan regular W hW)
        (restrictedFanRayCoefficients fan W hW b)))

/-- The complete, unconditional cohomological equivalence underlying
Theorem 5.2. Every linear subspace, degree, lattice character, and actual
sheaf pullback on the left is preserved by the finite formulation. -/
theorem toricLinearCohomologyCriterion_iff_finitePattern (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F] :
    toricLineBundleLinearCohomologyCriterion fan F ↔
      ∀ W ∈ rayGeneratedLinearTests fan,
        toricFiniteCohomologyPatternCriterion (restrictedFan fan W.space W.rational)
          (restrictedFanRayCoefficients fan W.space W.rational
            (toricLineBundleInvariantCoefficients fan nonempty regular F)) := by
  rw [toricLinearCohomologyCriterion_iff_rayGenerated fan nonempty regular F]
  exact forall_congr' fun W => forall_congr' fun _ =>
    toricLineBundleSubspace_nonzero_iff_finitePattern fan nonempty regular F W.space W.rational

end ToricPower
