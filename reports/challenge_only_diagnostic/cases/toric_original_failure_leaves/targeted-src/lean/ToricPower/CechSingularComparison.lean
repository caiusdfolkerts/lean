module

public import ToricPower.CechSingular.IncidenceSingularGlobalEquivalence

/-!
# The ordinary singular comparison

The sixteen preceding modules construct the actual affine simplex map, its
small-chain inverse through subdivision, and both integral chain homotopies.
This public endpoint names their composite without adding assumptions.
-/

@[expose] public noncomputable section

open ToricPower.CechIncidenceChains ToricPower.CechAcyclicCarrier
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative

namespace ToricPower.CechSingularComparison

open BondalThomsen.ConvexNerveReducedCochainAcyclicity
open BondalThomsen.ConvexNerveIncidenceSingularGlobalEquivalence

/-- The complete actual integral comparison. Both maps and both homotopies
are constructed by the preceding proof bodies. No comparison hypothesis
is supplied. -/
def incidenceSingularChainHomotopyEquiv {Ray : Type*} {Chart : Type} [Finite Chart]
    (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    HomotopyEquiv (incidenceChains incidence negative)
      (integralSingularChains (incidenceRealization incidence negative)) :=
  canonicalIncidenceSingularChainHomotopyEquiv incidence negative

end ToricPower.CechSingularComparison
