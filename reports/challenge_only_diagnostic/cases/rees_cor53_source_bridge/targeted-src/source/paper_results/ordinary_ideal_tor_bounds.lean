module
public import shared_results.part011
public import paper_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.OrdinaryIdealTorBounds -/
section

/-! # A genuine ordinary Tor entry detects projective dimension -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open CategoryTheory CategoryTheory.Limits CommAlg.Koszul MvPolynomial

universe u
variable {K V : Type u} [Field K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule K (fun _ : V => (1 : ℕ))))

/-- The graded group is the actual submodule of the paper's derived Tor.
Consequently its nonzero dimension forces the full derived Tor to be nonzero. -/
theorem ordinaryIdealTor_nonzero_of_betti (p q : ℕ)
    (h : ordinaryIdealBettiNumber P hJ p q ≠ 0) :
    ¬ IsZero (finitePolynomialTor p (ModuleCat.of (MvPolynomial V K) P.ideal)) := by
  intro hz
  let M := ModuleCat.of (MvPolynomial V K) P.ideal
  have hz' := (finitePolynomialTorPaperIso p M).isZero_iff.mp hz
  letI : Subsingleton (actualIdealTor P p) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).map_isZero hz')
  letI : Subsingleton (ordinaryIdealGradedTor P hJ q p) := inferInstance
  exact h (Module.finrank_zero_of_subsingleton (R:=K)
    (M:=ordinaryIdealGradedTor P hJ q p))

/-- Nonzero ordinary graded Tor in homological degree p gives the usual
lower bound for Mathlib's projective dimension of the original ideal. -/
theorem ordinaryIdealBetti_nonzero_le_projectiveDimension (p q : ℕ)
    (h : ordinaryIdealBettiNumber P hJ p q ≠ 0) :
    (p : WithBot ℕ∞) ≤ projectiveDimension (ModuleCat.of (MvPolynomial V K) P.ideal) :=
  finitePolynomialTor_nonzero_le_projectiveDimension _ p
    (ordinaryIdealTor_nonzero_of_betti P hJ p q h)

end FourPapers.Sublattice

end
end
end


end
