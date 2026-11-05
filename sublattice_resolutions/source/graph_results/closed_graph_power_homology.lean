module
public import shared_results.part009
public import paper_results.part005
public import graph_results.closed_graph_multiplicative_lifting
public import graph_results.closed_graph_power_leading_bridge
public import graph_homology
public import shared_results.part020

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphPowerHomology -/
section

/-! # All-power homology of the actual closed-graph parameter ideal

The coefficient ring may be ℤ[z]. Every ordinary homogeneous homology group
of every positive power is finite free over that ring. The homological and
ordinary support bounds are explicit. All inputs to the filtered comparison
are proved for the displayed ideal; no Betti equality or freeness assumption
is retained in these endpoint statements.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule
universe u
variable {k : Type u} [CommRing k] [IsDomain k] {N : ℕ} {G : SimpleGraph (Fin N)}

abbrev graphParameterPowerOrdinaryHomology (hG : IntervalLabeling G)
    (t : k) (ht : t ≠ 0) (s q p : ℕ) :=
  actualIdealOrdinaryHomology (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s) q p

/-- Every ordinary-degree homology module of every positive power of the
literal parameter ideal is free over the original coefficient domain. -/
theorem intervalGraph_parameter_power_homology_free (hG : IntervalLabeling G)
    (t : k) (ht : t ≠ 0) (s : ℕ) (hs : 0 < s) (q p : ℕ) :
    Module.Free k (graphParameterPowerOrdinaryHomology hG t ht s q p) :=
  actualIdealOrdinaryHomology_free_of_monomial
    (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s)
    (intervalGraph_parameter_power_previous_strictly_lowers hG t ht s)
    N graphDiagonalWeight_le
    (intervalGraph_parameter_power_coordinate_lifts hG t ht s) q p
    (fun α => closedGraph_monomial_power_homology_free hG s hs α p)

/-- Finite generation is proved separately from freeness; it comes from
the actual finite fine-degree products and a finite filtration. -/
theorem intervalGraph_parameter_power_homology_finite (hG : IntervalLabeling G)
    (t : k) (ht : t ≠ 0) (s : ℕ) (hs : 0 < s) (q p : ℕ) :
    Module.Finite k (graphParameterPowerOrdinaryHomology hG t ht s q p) :=
  actualIdealOrdinaryHomology_finite_of_monomial
    (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s)
    (intervalGraph_parameter_power_previous_strictly_lowers hG t ht s)
    N graphDiagonalWeight_le
    (intervalGraph_parameter_power_coordinate_lifts hG t ht s) q p
    (fun α => closedGraph_monomial_power_homology_free hG s hs α p)
    (fun α => closedGraph_monomial_power_homology_finite hG s hs α p)

/-- No homology occurs beyond the explicit ordinary-degree bound. The
proof transfers the actual monomial creation contraction through the finite
weight filtration, not merely a numerical regularity estimate. -/
theorem intervalGraph_parameter_power_homology_zero_of_degree_gt
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (s q p : ℕ)
    (hq : Fintype.card (FiniteVariable.{u} (GraphRows N)) * s < q) :
    Subsingleton (graphParameterPowerOrdinaryHomology hG t ht s q p) := by
  apply actualIdealOrdinaryHomology_subsingleton_of_monomial
    (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s)
    (intervalGraph_parameter_power_previous_strictly_lowers hG t ht s) q p
  intro α hα
  exact finitePowerFamily_homology_subsingleton_of_degree_gt
    (graphEdgeLattice G) s α (by simpa only [hα] using hq) p

theorem intervalGraph_parameter_power_homology_zero_of_exterior_degree_gt
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (s q p : ℕ)
    (hp : Fintype.card (FiniteVariable.{u} (GraphRows N)) < p) :
    Subsingleton (graphParameterPowerOrdinaryHomology hG t ht s q p) := by
  apply actualIdealOrdinaryHomology_subsingleton_of_monomial
    (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s)
    (intervalGraph_parameter_power_previous_strictly_lowers hG t ht s) q p
  intro α _
  exact monomial_fine_homology_subsingleton_of_exterior_degree_gt
    (exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) s) α p hp

/-- Only finitely many actual ordinary and homological pieces can be
nonzero. This is the support bound needed for a finite free resolution. -/
theorem intervalGraph_parameter_power_homology_support
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (s q p : ℕ)
    (hH : Nontrivial (graphParameterPowerOrdinaryHomology hG t ht s q p)) :
    p ≤ Fintype.card (FiniteVariable.{u} (GraphRows N)) ∧
      q ≤ Fintype.card (FiniteVariable.{u} (GraphRows N)) * s := by
  letI := hH
  constructor
  · by_contra hp
    letI := intervalGraph_parameter_power_homology_zero_of_exterior_degree_gt
      hG t ht s q p (Nat.lt_of_not_ge hp)
    exact not_subsingleton (graphParameterPowerOrdinaryHomology hG t ht s q p) inferInstance
  · by_contra hq
    letI := intervalGraph_parameter_power_homology_zero_of_degree_gt
      hG t ht s q p (Nat.lt_of_not_ge hq)
    exact not_subsingleton (graphParameterPowerOrdinaryHomology hG t ht s q p) inferInstance

/-- The coefficient ring in the common family is literally ℤ[z]. -/
theorem intervalGraph_integral_parameter_power_homology
    (hG : IntervalLabeling G) (s : ℕ) (hs : 0 < s) (q p : ℕ) :
    Module.Free (Polynomial ℤ)
        (graphParameterPowerOrdinaryHomology hG (Polynomial.X : Polynomial ℤ)
          Polynomial.X_ne_zero s q p) ∧
      Module.Finite (Polynomial ℤ)
        (graphParameterPowerOrdinaryHomology hG (Polynomial.X : Polynomial ℤ)
          Polynomial.X_ne_zero s q p) :=
  ⟨intervalGraph_parameter_power_homology_free hG _ Polynomial.X_ne_zero s hs q p,
    intervalGraph_parameter_power_homology_finite hG _ Polynomial.X_ne_zero s hs q p⟩

end FourPapers.Sublattice

namespace FourPapers.Sublattice
open Classical MvPolynomial
universe u
variable {k : Type u} [Field k] {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The actual parameter-power homology and its literal monomial model
have identical dimensions in every ordinary and homological degree. -/
theorem intervalGraph_parameter_power_homology_finrank_eq_initial
    (hG : IntervalLabeling G) (t : k) (ht : t ≠ 0) (s q p : ℕ) :
    Module.finrank k (graphParameterPowerOrdinaryHomology hG t ht s q p) =
      Module.finrank k (initialActualIdealOrdinaryHomology
        (graphParameterPowerQuotientData t ht hG s) q p) :=
  actualIdealOrdinaryHomology_finrank_eq_initial
    (graphParameterPowerQuotientData t ht hG s)
    (graphParameterPower_ordinary_homogeneous t G s)
    graphDiagonalWeight (graphParameterProducts_weight_tails t ht G s)
    (intervalGraph_parameter_power_previous_strictly_lowers hG t ht s)
    N graphDiagonalWeight_le
    (intervalGraph_parameter_power_coordinate_lifts hG t ht s) q p

end FourPapers.Sublattice

end
end
end


end
