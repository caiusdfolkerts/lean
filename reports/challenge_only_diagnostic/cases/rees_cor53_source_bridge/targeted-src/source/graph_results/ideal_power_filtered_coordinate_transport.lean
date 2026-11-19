module
public import shared_results.part021
public import graph_results.filtered_lifts_equivalence

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealPowerFilteredCoordinateTransport -/
section

/-! # Weight-filtered transport from native ideal powers to Rees coefficients

The coefficient equivalence is the identity on underlying polynomials.
Its basis and differential compatibility identify the full filtered
cycle-lifting predicates, without identifying their module dictionaries.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul MvPolynomial FilteredHomology

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J^s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

/-- The same coefficient-plus-exterior weight on native ideal coordinates. -/
def nativePowerCoordinateFiltration (w : V → ℕ) (s p : ℕ) :
    Filtration (K := K) (Set.powersetCard V p →₀ ↥(J^s)) :=
  Universal.basisFiltration (nativePowerCoefficientBasis m J G hG hu s p)
    (fun a : PowerIdealIndex m J s p =>
      Finsupp.weight w (a.2.val + faceExponent a.1.val))

section
attribute [local irreducible] nativePowerCoefficientBasis powerIdealCoefficientBasis
  powerIdealCoordinateEquiv actualIdealPreviousDifferential powerPreviousDifferential

set_option diagnostics true in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
/-- Exact transport of every leading cycle and every lower-weight error. -/
theorem nativePowerCoordinateLifts_iff (w : V → ℕ) (s p : ℕ) :
    LiftsCycles (nativePowerCoordinateFiltration m J G hG hu w s p)
      (nativePowerCoordinateFiltration m J G hG hu w s p.pred)
      (actualIdealPreviousDifferential (J^s) p) ↔
    LiftsCycles (powerCoordinateFiltration m J G hG hu w s p)
      (powerCoordinateFiltration m J G hG hu w s p.pred)
      (powerPreviousDifferential J s p) := by
  unfold nativePowerCoordinateFiltration powerCoordinateFiltration
  apply FilteredHomology.basisLiftsCycles_iff_of_equiv
    (e := powerIdealCoordinateEquiv J s p)
    (f := powerIdealCoordinateEquiv J s p.pred)
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p
  · exact powerIdealCoordinateEquiv_basis m J G hG hu s p.pred
  · exact powerIdealCoordinateEquiv_differential J s p

end
end FourPapers.Sublattice

end
end
end


end
