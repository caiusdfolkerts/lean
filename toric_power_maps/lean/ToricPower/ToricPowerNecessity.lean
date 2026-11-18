module

public import ToricPower.OpenCohomologyObstruction
public import ToricPower.PrincipalInvariantTransport
public import ToricPower.DivisorWeightGlobalSplitting
public import ToricPower.ToricFloorRestrictionCohomology
public import ToricPower.ToricOpenNeighbourhoodCohomology

/-!
# Necessity of the paper's linear cohomology criterion

The same-lattice subfan consisting of cones in a rational subspace gives
an actual open subscheme U. For each invertible sheaf, vanishing on U is
equivalent to vanishing on the corresponding saturated-trace subvariety.
The exact floor-pattern identity transfers vanishing of the original
divisor to every summand of its positive power-map direct image.

The finite splitting is a proved isomorphism of the actual sheaves.
Thus the actual open derived-global-sections functor kills that direct
image. It does not kill the structure sheaf, so the direct image cannot
generate the literal bounded derived category of coherent sheaves.

The final theorem applies to every Cartier divisor by the already proved
actual invariant-representative isomorphism. No closed-immersion duality,
Koszul comparison, equivariant presentation, or completeness is assumed.
-/

@[expose] public noncomputable section

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- Acyclicity on a rational linear restriction kills the actual positive
power direct image on the corresponding actual open neighbourhood. -/
theorem toricPowerInvariant_openCohomology_vanishes
    (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (b : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell)
    (W : Submodule ℝ V) (rational : IsRationalSubspace i W) :
    letI := toricSchemeIntegral fan nonempty
    letI := linearAmbientOpenInclusion_isOpenImmersion fan W
    (∀ degree, Subsingleton (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan nonempty regular b).sheaf W rational degree)) →
    ∀ degree, Subsingleton (Cohomology
      ((Scheme.Modules.restrictFunctor (linearAmbientOpenInclusion fan W)).obj
        ((Scheme.Modules.pushforward (toricPowerMap fan ell)).obj
          (invariantCartierDivisor fan nonempty regular b).sheaf)) degree) := by
  letI := toricSchemeIntegral fan nonempty
  letI := linearAmbientOpenInclusion_isOpenImmersion fan W
  intro vanishes
  let basis := latticeCharacterBasis fan.lattice
  apply openCohomology_subsingleton_of_iso_biproduct
    (linearAmbientOpenInclusion fan W)
    (toricResidueSheafFamily fan nonempty regular basis b ell) _
    (toricPowerInvariantCartierSplitting fan nonempty regular basis b ell positive)
  intro residue degree
  let character := basis.equivFun.symm (latticeResidueRepresentative residue)
  let divisor := invariantCartierDivisor fan nonempty regular
    (toricResidueCoefficients fan b ell character)
  letI := divisor.isInvertible_sheaf
  have restrictedVanishes := toricFlooredSubspacePullback_subsingleton
    fan nonempty regular b character ell positive W rational vanishes
  have openVanishes := (toricOpenNeighbourhood_subsingleton_iff_subspace
    fan nonempty regular divisor.sheaf W rational).mpr restrictedVanishes
  exact cohomology_subsingleton_of_sheaf_iso
    ((Scheme.Modules.restrictFunctorIsoPullback
      (linearAmbientOpenInclusion fan W)).app divisor.sheaf)
    degree (openVanishes degree)

/-- The necessity implication for an actual invariant Cartier divisor.
All positive exponents and every permitted linear subspace are retained. -/
theorem toricPowerGeneratesDbCoh_linearCriterion_invariant
    (fan : Fan i) (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (b : fan.Ray → ℤ) (ell : ℕ) (positive : 0 < ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne
      (invariantCartierDivisor fan hne.coe_sort regular b) ell positive →
    linearCohomologyCriterion fan hne
      (invariantCartierDivisor fan hne.coe_sort regular b) := by
  letI := toricScheme_isIntegral fan hne
  letI := toricScheme_isNoetherian fan
  intro generates W
  by_contra zero
  have vanishes : ∀ degree, Subsingleton (toricSubspacePullbackCohomology fan
      (invariantCartierDivisor fan hne.coe_sort regular b).sheaf
        W.space W.rational degree) := by
    intro degree
    apply not_nontrivial_iff_subsingleton.mp
    intro nonzero
    exact zero ⟨degree, nonzero⟩
  let ambient := linearAmbientFan fan W.space
  letI := toricScheme_isNoetherian ambient
  letI := toricSchemeIntegral ambient
    (linearAmbientFan_cones_nonempty fan hne.coe_sort W.space)
  letI := linearAmbientOpenInclusion_isOpenImmersion fan W.space
  let D := invariantCartierDivisor fan hne.coe_sort regular b
  let G : Coh fan.algebraicRealization :=
    ⟨toricPowerDivisorSheaf fan hne D ell,
      toricPowerDivisorSheaf_isFinitePresentation fan regular hne D ell positive⟩
  have obstruction := not_generatesDbCoh_of_nonempty_open_cohomology_vanishes
    (linearAmbientOpenInclusion fan W.space) G
    (toricPowerInvariant_openCohomology_vanishes fan hne.coe_sort regular b ell positive
      W.space W.rational vanishes)
  exact obstruction generates

/-- **The necessity direction of Theorem 1.1.** Every positive power-map
direct image that generates literal DbCoh satisfies the original all-linear
cohomology criterion, for every actual Cartier divisor. -/
theorem paper_theorem_1_1_necessity
    (fan : Fan i) (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) (ell : ℕ) (positive : 0 < ell)
    (generates : toricPowerGeneratesDbCoh fan regular hne D ell positive) :
    linearCohomologyCriterion fan hne D := by
  letI := toricScheme_isIntegral fan hne
  letI := D.isInvertible_sheaf
  let comparison := toricCartierInvariantRepresentativeIso fan regular hne D
  have invariantGenerates :=
    (toricPowerGeneratesDbCoh_iff_of_sheaf_iso fan regular hne comparison ell positive).mp
      generates
  have invariantCriterion := toricPowerGeneratesDbCoh_linearCriterion_invariant
    fan regular hne (toricLineBundleInvariantCoefficients fan hne.coe_sort regular D.sheaf)
      ell positive invariantGenerates
  exact (linearCohomologyCriterion_iff_of_sheaf_iso fan hne comparison).mpr
    invariantCriterion

end ToricPower

end
