module

public import ToricPower.ToricActualRestrictionCohomology
public import ToricPower.ToricInvariantLineBundleClassification

/-!
# Removing transverse torus directions preserves cohomological vanishing

Suppose every cone of a regular fan lies in a rational subspace `W`,
while the fan still uses the full ambient lattice. Its actual line-sheaf
cohomology vanishes in a given degree exactly when the actual pullback to
the saturated-trace toric subvariety vanishes in that degree.

Both fans have the same chart and ray incidence. Their integral characters
have exactly the same pairing profiles on these rays: restriction is
surjective because the lattice trace is saturated. Comparing their full
character complexes proves the result without a torus-product isomorphism
or a finite base-change assertion.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules
open ToricPower.NegativeSupportCech
open scoped Classical

namespace ToricPower
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The ambient cones, enumerated by the same finite index as their
saturated-trace counterparts. -/
def retainedAmbientFiniteCharts (fan : Fan i) (W : Submodule ℝ V) :
    Fin (Nat.card (retainedFanCones fan W)) → fan.cones :=
  fun index => ((Finite.equivFin (retainedFanCones fan W)).symm index).val

theorem retainedAmbientFiniteCharts_surjective (fan : Fan i) (W : Submodule ℝ V)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V)) :
    Function.Surjective (retainedAmbientFiniteCharts fan W) := by
  intro cone
  refine ⟨Finite.equivFin (retainedFanCones fan W) ⟨cone, contained cone⟩, ?_⟩
  exact congrArg Subtype.val ((Finite.equivFin (retainedFanCones fan W)).symm_apply_apply
    ⟨cone, contained cone⟩)

/-- The ambient full-character complex has precisely the common retained
ray profile, with every differential unchanged. -/
def ambientRetainedWeightProfileIso (fan : Fan i) (W : Submodule ℝ V)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V))
    (b : fan.Ray → ℤ) (character : N →+ ℤ) :
    toricCechWeightComplex fan (retainedAmbientFiniteCharts fan W) b character ≅
      retainedProfileComplex ℂ fan W b
        (fun ray => character (fanRayPrimitiveGenerator fan ray.val)) :=
  relativeComplexIsoOfForbiddenIff ℂ _ _ _ _ (by
    intro degree tuple
    constructor
    · rintro ⟨ray, negative, incident⟩
      exact ⟨⟨ray, contained ray.toCone⟩, negative, incident⟩
    · rintro ⟨ray, negative, incident⟩
      exact ⟨ray.val, negative, incident⟩)

/-- In every degree, the complete integral-character tests agree for the
ambient lattice and its saturated trace. -/
theorem conesInSubspace_weightHomology_nontrivial_iff (fan : Fan i)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V))
    (b : fan.Ray → ℤ) (degree : ℕ) :
    (∃ character : N →+ ℤ, Nontrivial
      ((toricCechWeightComplex fan (retainedAmbientFiniteCharts fan W) b character).homology degree)) ↔
    ∃ character : latticeTrace i W →+ ℤ, Nontrivial
      ((restrictedWeightComplex ℂ fan W rational b character).homology degree) := by
  have ambient : (∃ character : N →+ ℤ, Nontrivial
      ((toricCechWeightComplex fan (retainedAmbientFiniteCharts fan W) b character).homology degree)) ↔
      ∃ character : N →+ ℤ, Nontrivial ((retainedProfileComplex ℂ fan W b
        (fun ray => character (fanRayPrimitiveGenerator fan ray.val))).homology degree) := by
    apply exists_congr
    intro character
    exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
      (ambientRetainedWeightProfileIso fan W contained b character)).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr
  have restricted : (∃ character : latticeTrace i W →+ ℤ, Nontrivial
      ((restrictedWeightComplex ℂ fan W rational b character).homology degree)) ↔
      ∃ character : latticeTrace i W →+ ℤ, Nontrivial ((retainedProfileComplex ℂ fan W b
        (fun ray => character (retainedRayPrimitiveInSubspace fan W ray))).homology degree) := by
    apply exists_congr
    intro character
    exact ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) degree).mapIso
      (restrictedWeightProfileIso ℂ fan W rational b character)).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr
  refine ambient.trans (Iff.trans ?_ restricted.symm)
  constructor
  · rintro ⟨character, nonzero⟩
    exact ⟨character.comp (latticeTrace i W).subtype.toAddMonoidHom, nonzero⟩
  · rintro ⟨character, nonzero⟩
    refine ⟨latticeTraceCharacterExtension fan.lattice W character, ?_⟩
    have profile : (fun ray : retainedFanRays fan W =>
        latticeTraceCharacterExtension fan.lattice W character
          (fanRayPrimitiveGenerator fan ray.val)) =
        fun ray => character (retainedRayPrimitiveInSubspace fan W ray) := by
      funext ray
      exact latticeTraceCharacterExtension_apply_trace fan.lattice W character
        (retainedRayPrimitiveInSubspace fan W ray)
    simpa only [profile] using nonzero

/-- The degreewise ordinary-cohomology comparison for the actual invariant
Cartier line sheaf and its literal subspace pullback. -/
theorem toricInvariantCohomology_nontrivial_iff_subspace_of_cones_le (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V))
    (b : fan.Ray → ℤ) (degree : ℕ) :
    letI := toricSchemeIntegral fan nonempty
    Nontrivial (invariantDivisorCohomology fan nonempty regular b degree) ↔
      Nontrivial (toricSubspacePullbackCohomology fan
        (invariantCartierDivisor fan nonempty regular b).sheaf W rational degree) := by
  letI := toricSchemeIntegral fan nonempty
  have ambient := toricCartierCohomologyWeight_nontrivial_iff fan nonempty regular
    (retainedAmbientFiniteCharts fan W)
    (retainedAmbientFiniteCharts_surjective fan W contained) b degree
  have restricted := toricCartierCohomologyWeight_nontrivial_iff
    (restrictedFan fan W rational) (restrictedFan_cones_nonempty fan nonempty W rational)
    (restrictedFan_isRegular fan regular W rational)
    (linearRayCoreFiniteCharts fan W rational)
    (linearRayCoreFiniteCharts_surjective fan W rational)
    (restrictedFanRayCoefficients fan W rational b) degree
  exact ambient.trans ((conesInSubspace_weightHomology_nontrivial_iff
    fan W rational contained b degree).trans (restricted.symm.trans
      (toricSubspaceInvariantCohomologyIso fan nonempty regular W rational b degree).addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr))

/-- The same degreewise comparison holds for every actual invertible
module sheaf, without a supplied invariant representative or linearization. -/
theorem toricLineBundleCohomology_nontrivial_iff_subspace_of_cones_le (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V)) (degree : ℕ) :
    Nontrivial (Cohomology F degree) ↔
      Nontrivial (toricSubspacePullbackCohomology fan F W rational degree) := by
  letI := toricSchemeIntegral fan nonempty
  let b := toricLineBundleInvariantCoefficients fan nonempty regular F
  let comparison := toricLineBundleInvariantIso fan nonempty regular F
  let ambient := (cohomologyFunctor fan.algebraicRealization degree).mapIso comparison
  let restricted := (cohomologyFunctor (restrictedFan fan W rational).algebraicRealization degree).mapIso
    ((Scheme.Modules.pullback (restrictedFanInclusion fan W rational).algebraicMap).mapIso comparison)
  exact ambient.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.trans
    ((toricInvariantCohomology_nontrivial_iff_subspace_of_cones_le
      fan nonempty regular W rational contained b degree).trans
      restricted.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr.symm)

/-- Total nonvanishing is unchanged by removal of the transverse torus
coordinates, for every actual line bundle. -/
theorem toricLineBundleCohomology_nonzero_iff_subspace_of_cones_le (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V)) :
    (∃ degree, Nontrivial (Cohomology F degree)) ↔
      ∃ degree, Nontrivial (toricSubspacePullbackCohomology fan F W rational degree) := by
  apply exists_congr
  exact toricLineBundleCohomology_nontrivial_iff_subspace_of_cones_le
    fan nonempty regular F W rational contained

/-- Vanishing in every actual ordinary cohomological degree is equivalent
on the ambient fan and its saturated-trace subvariety. -/
theorem toricLineBundleCohomology_subsingleton_iff_subspace_of_cones_le (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (F : fan.algebraicRealization.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization F]
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W)
    (contained : ∀ cone : fan.cones, cone.val ≤ (W : PointedCone ℝ V)) :
    (∀ degree, Subsingleton (Cohomology F degree)) ↔
      ∀ degree, Subsingleton (toricSubspacePullbackCohomology fan F W rational degree) := by
  apply forall_congr'
  intro degree
  rw [← not_nontrivial_iff_subsingleton, ← not_nontrivial_iff_subsingleton]
  exact not_congr (toricLineBundleCohomology_nontrivial_iff_subspace_of_cones_le
    fan nonempty regular F W rational contained degree)

end ToricPower
