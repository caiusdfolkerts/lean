module
public import resolution_existence.part009
public import mixed_results.part001
public import mixed_results.disjoint_monomial_generation
public import mixed_results.regular_substitution_propagation
public import mixed_results.nonminimal_identity_resolution
public import mixed_results.regular_substitution_derived_tor

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.Corollary58 -/
section

/-!
# Corollary 5.8: faithful universal preservation and all algebra clauses

A finite minimal fine source resolution is constructed for every literal
monomial ideal and every power. Its actual scalar extension is a minimal
free resolution of the literal substituted power. Every other given
minimal multigraded source resolution enjoys the same preservation theorem. Its actual term grading, differential, augmentation and
fine shifts retain the prescribed weighted degrees. The substitution is
proved free from the positive homogeneous regular-sequence hypotheses.

The actual Tor algebra comparison preserves products and Rees components,
giving Rees-degree-one generation and first-power propagation. Positive
monomials with pairwise disjoint supports are included with regularity proved.

The separate identity-substitution counterexample records why an arbitrary
nonminimal source resolution cannot become minimal merely by base change.
The constructed power resolutions, their actual augmentations, and the
additive shift equations are included through RegularSubstitutionFineResolution.
-/

#print axioms FourPapers.PolynomialRegularSubstitution.literalSubstitution_free
#print axioms FourPapers.PolynomialRegularSubstitution.baseChangedResolution
#print axioms FourPapers.PolynomialRegularSubstitution.baseChangedResolution_minimal
#print axioms FourPapers.PolynomialRegularSubstitution.fineResolutionEntries_iff_graded
#print axioms FourPapers.PolynomialRegularSubstitution.fineAugmentationEntries_iff_graded
#print axioms FourPapers.Sublattice.substitutedPowerResolution
#print axioms FourPapers.Sublattice.substitutedPower_minimal
#print axioms FourPapers.Sublattice.substitutedPower_shift_degree
#print axioms FourPapers.Sublattice.substitutedPower_differential_graded
#print axioms FourPapers.Sublattice.substitutedPower_augmentation_graded
#print axioms FourPapers.PolynomialRegularSubstitution.torAlgebraEquiv
#print axioms FourPapers.PolynomialRegularSubstitution.regularSourceDifferential_eq_polynomial
#print axioms FourPapers.PolynomialRegularSubstitution.regularTargetDifferential_eq_polynomial
#print axioms FourPapers.PolynomialRegularSubstitution.regularSourceKoszulComplex_differential_val
#print axioms FourPapers.PolynomialRegularSubstitution.regularTargetKoszulComplex_differential_val
#print axioms FourPapers.PolynomialRegularSubstitution.regularSourceDerivedTorIso
#print axioms FourPapers.PolynomialRegularSubstitution.regularTargetDerivedTorIso
#print axioms FourPapers.Sublattice.corollary58_generation
#print axioms FourPapers.Sublattice.corollary58_propagation
#print axioms FourPapers.Sublattice.corollary58_disjoint_monomial_generation
#print axioms FourPapers.Sublattice.NonminimalIdentityResolution.identity_resolution_nonminimal

#print axioms FourPapers.Sublattice.MonomialFineResolution.resolution
#print axioms FourPapers.Sublattice.MonomialFineResolution.resolution_minimal
#print axioms FourPapers.Sublattice.MonomialFineResolution.resolution_shift_multiplicity
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_minimal
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_regraded
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_degree
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_bounded
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_augmentation_regraded
#print axioms FourPapers.Sublattice.corollary58_powerFreeResolution_shift_multiplicity

end

end
