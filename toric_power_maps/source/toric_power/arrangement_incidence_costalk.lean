module

public import ToricPower.ArrangementIncidenceCategory
public import ToricPower.ArrangementCostalkTranslation
public import ToricPower.ArrangementCostalkCochainMaps
public import ToricPower.LinearDualHomologyClass

/-!
# Actual costalk maps for translated face incidences

Every morphism of the normalized incidence category retains its integer
translation. Translate the source costalk by that vector, then restrict
its open support to the target star. These are genuine cellular chain
maps. Their scalar duals have exactly the opposite character shift of
the unreflected Cartier label in Appendix A.1. The fixed top classes
commute with these actual maps, including incidences with zero cellular
boundary coefficient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)

/-- The point used to evaluate a normalized cell is in that actual cell. -/
def incidenceCellCenter (c : IncidenceObject matrix) : Fin n → ℝ :=
  cellCenter (augmentedForms matrix) c.2.val

/-- A literal translated incidence reverses the inclusion of open
stars after applying the same literal lattice translation. -/
theorem incidence_costalkRegion_subset {c d : IncidenceObject matrix} (f : c ⟶ d)
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) :
    costalkRegion (augmentedForms matrix) selected weight (incidenceCellCenter matrix d) ⊆
      costalkRegion (augmentedForms matrix) selected weight
        (incidenceCellCenter matrix c + latticeLift f.val) := by
  apply costalkRegion_subset_of_point_mem_closedCell
  have sourcePoint := cellCenter_mem (augmentedForms matrix) c.2.val
  have targetPoint := cellCenter_mem (augmentedForms matrix) d.2.val
  have contained := f.property (incidenceCellCenter matrix c)
    (cell_subset_closedCell _ _ _ sourcePoint)
  have targetCeiling : ceilingVector (augmentedForms matrix)
      (incidenceCellCenter matrix d) = d.2.val.val.1 := by
    funext i
    exact ceil_eq_of_mem_cell _ _ _ targetPoint i
  have targetIntegral : integralIndices (augmentedForms matrix)
      (incidenceCellCenter matrix d) = d.2.val.val.2 :=
    integralIndices_eq_of_mem_cell _ _ _ targetPoint
  rw [targetCeiling, targetIntegral]
  exact contained

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- An actual chain map for each translated incidence and each full
integral weight. The shift is the pairing with the recorded translation. -/
def incidenceCostalkChainMap {c d : IncidenceObject matrix} (f : c ⟶ d)
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) :
    periodicCostalkCellComplex matrix selected weight (incidenceCellCenter matrix c) M ⟶
      periodicCostalkCellComplex matrix selected
        (weight + augmentedLatticePairing matrix f.val) (incidenceCellCenter matrix d) M :=
  periodicCostalkTranslation matrix selected weight (incidenceCellCenter matrix c) f.val M ≫
    periodicCostalkRestriction matrix M selected selected
      (weight + augmentedLatticePairing matrix f.val)
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix d) (incidenceCellCenter matrix c + latticeLift f.val)
      (incidence_costalkRegion_subset matrix f selected _)

/-- Every nonzero top coefficient is transported with coefficient one
under every actual translated face map. -/
theorem incidenceCostalkChainMap_topClass {c d : IncidenceObject matrix} (f : c ⟶ d)
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ)
    (nonemptySource : (costalkRegion (augmentedForms matrix) selected weight
      (incidenceCellCenter matrix c)).Nonempty)
    (nonemptyTarget : (costalkRegion (augmentedForms matrix) selected
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix d)).Nonempty) :
    HomologicalComplex.homologyMap (incidenceCostalkChainMap matrix M f selected weight) n ≫
        (periodicCostalkCellHomologyIso matrix selected
          (weight + augmentedLatticePairing matrix f.val)
          (incidenceCellCenter matrix d) M nonemptyTarget).hom =
      (periodicCostalkCellHomologyIso matrix selected weight
        (incidenceCellCenter matrix c) M nonemptySource).hom := by
  have nonemptyMiddle : (costalkRegion (augmentedForms matrix) selected
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix c + latticeLift f.val)).Nonempty := by
    rw [← periodicCostalkRegion_translation]
    exact nonemptySource.image _
  rw [incidenceCostalkChainMap, HomologicalComplex.homologyMap_comp, Category.assoc,
    periodicCostalkCellHomologyIso_natural matrix M selected selected
      (weight + augmentedLatticePairing matrix f.val)
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix d) (incidenceCellCenter matrix c + latticeLift f.val)
      (incidence_costalkRegion_subset matrix f selected _) nonemptyTarget nonemptyMiddle]
  exact periodicCostalkCellHomologyIso_translation matrix selected weight
    (incidenceCellCenter matrix c) f.val M nonemptySource nonemptyMiddle

variable (𝕜 : Type) [Field 𝕜]

/-- The actual scalar cochain incidence map reverses both the arrow and
the recorded character shift, exactly as the right Cartier-label map. -/
def incidenceCostalkCochainMap {c d : IncidenceObject matrix} (f : c ⟶ d)
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ) :
    periodicCostalkCochainComplex matrix selected
        (weight + augmentedLatticePairing matrix f.val) (incidenceCellCenter matrix d) 𝕜 ⟶
      periodicCostalkCochainComplex matrix selected weight (incidenceCellCenter matrix c) 𝕜 :=
  scalarDualMap 𝕜 (incidenceCostalkChainMap matrix (ModuleCat.of 𝕜 𝕜) f selected weight)

/-- The actual cochain map induces precisely the canonical monomial
coefficient map whenever both weights are present. -/
theorem incidenceCostalkCochainMap_topClass {c d : IncidenceObject matrix} (f : c ⟶ d)
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ)
    (nonemptySource : (costalkRegion (augmentedForms matrix) selected weight
      (incidenceCellCenter matrix c)).Nonempty)
    (nonemptyTarget : (costalkRegion (augmentedForms matrix) selected
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix d)).Nonempty) :
    HomologicalComplex.homologyMap (incidenceCostalkCochainMap matrix 𝕜 f selected weight) n ≫
        (periodicCostalkCochainHomologyIso matrix selected weight
          (incidenceCellCenter matrix c) 𝕜 nonemptySource).hom =
      (periodicCostalkCochainHomologyIso matrix selected
        (weight + augmentedLatticePairing matrix f.val)
        (incidenceCellCenter matrix d) 𝕜 nonemptyTarget).hom :=
  scalarDualHomologyClassIso_natural 𝕜
    (incidenceCostalkChainMap matrix (ModuleCat.of 𝕜 𝕜) f selected weight) n
    (periodicCostalkCellHomologyIso matrix selected weight
      (incidenceCellCenter matrix c) (ModuleCat.of 𝕜 𝕜) nonemptySource)
    (periodicCostalkCellHomologyIso matrix selected
      (weight + augmentedLatticePairing matrix f.val)
      (incidenceCellCenter matrix d) (ModuleCat.of 𝕜 𝕜) nonemptyTarget)
    (incidenceCostalkChainMap_topClass matrix (ModuleCat.of 𝕜 𝕜) f selected weight
      nonemptySource nonemptyTarget)

end ToricPower.IntegralArrangement
