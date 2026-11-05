module
public import mixed_results.part001
public import mixed_results.regular_substitution_rees_generation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.DisjointMonomialGeneration -/
section

/-! # Rees-degree-one generation for disjoint monomial substitutions -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial DisjointMonomialRegularity
universe u
variable {K Y : Type u} [Field K] [Fintype Y] [LinearOrder Y]
  {d : ℕ} {n : Fin d → ℕ}
  (a : FiniteVariable.{u} n → Y →₀ ℕ)
  (hpos : ∀ v, a v ≠ 0)
  (hdis : Pairwise (fun v w => Disjoint (a v).support (a w).support))

include hpos hdis in
/-- The actual Koszul homology algebra is generated in Rees degree one;
regularity of these monomial substitutions is proved from their supports. -/
theorem corollary58_disjoint_monomial_generation
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E) :
    Algebra.adjoin K
      (PolynomialRegularSubstitution.coefficientReesClasses
        (substitutedSublatticeIdeal (fun v => monomial (a v) (1 : K)) E) 1) = ⊤ :=
  corollary58_generation E (fun v => monomial (a v) (1 : K))
    (fun v => (a v).degree) (disjoint_monomials_homogeneous a)
    (disjoint_monomials_regular a hpos hdis) (monomial_degrees_positive a hpos) hE

end FourPapers.Sublattice

end
end
end

end
