module

public import ToricPower.ArrangementCostalkRestriction
public import ToricPower.ArrangementCostalkDuality

/-!
# Scalar costalk cochains and their actual restriction maps

Scalar duality reverses the genuine relative cellular chain maps. The
chosen top cohomology coefficients commute with these maps as morphisms
of vector spaces. No finite-dimensional duality or chosen representative
of a homology class is needed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)
  (𝕜 : Type) [Field 𝕜]
  (S T : Set (Fin s ⊕ Fin n)) (a b : Fin s ⊕ Fin n → ℤ)
  (x y : Fin n → ℝ)

/-- The actual scalar dual of the relative cellular support map. -/
def periodicCostalkCochainRestriction
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y) :
    periodicCostalkCochainComplex matrix S a x 𝕜 ⟶
      periodicCostalkCochainComplex matrix T b y 𝕜 :=
  scalarDualMap 𝕜
    (periodicCostalkRestriction matrix (ModuleCat.of 𝕜 𝕜) S T a b x y h)

/-- The fixed ambient orientation identifies every nonzero top
coefficient compatibly with the genuine cellular cochain maps. -/
theorem periodicCostalkCochainHomologyIso_natural
    (h : costalkRegion (augmentedForms matrix) S a x ⊆
      costalkRegion (augmentedForms matrix) T b y)
    (nonemptyS : (costalkRegion (augmentedForms matrix) S a x).Nonempty)
    (nonemptyT : (costalkRegion (augmentedForms matrix) T b y).Nonempty) :
    HomologicalComplex.homologyMap
        (periodicCostalkCochainRestriction matrix 𝕜 S T a b x y h) n ≫
        (periodicCostalkCochainHomologyIso matrix T b y 𝕜 nonemptyT).hom =
      (periodicCostalkCochainHomologyIso matrix S a x 𝕜 nonemptyS).hom := by
  let eS := periodicCostalkCellHomologyIso matrix S a x (ModuleCat.of 𝕜 𝕜) nonemptyS
  let eT := periodicCostalkCellHomologyIso matrix T b y (ModuleCat.of 𝕜 𝕜) nonemptyT
  let f := periodicCostalkRestriction matrix (ModuleCat.of 𝕜 𝕜) S T a b x y h
  have inverseSquare : eT.inv ≫ HomologicalComplex.homologyMap f n = eS.inv := by
    apply (cancel_mono eS.hom).mp
    rw [Category.assoc, periodicCostalkCellHomologyIso_natural
      matrix (ModuleCat.of 𝕜 𝕜) S T a b x y h nonemptyS nonemptyT,
      Iso.inv_hom_id, Iso.inv_hom_id]
  simp only [periodicCostalkCochainHomologyIso, periodicCostalkCochainRestriction,
    periodicCostalkCochainComplex, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom]
  rw [← Category.assoc, scalarDualHomologyIso_natural, Category.assoc,
    ← Functor.map_comp_assoc, ← op_comp]
  change (scalarDualHomologyIso 𝕜
      (periodicCostalkCellComplex matrix S a x (ModuleCat.of 𝕜 𝕜)) n).hom ≫
      (scalarDual 𝕜).map (eT.inv ≫ HomologicalComplex.homologyMap f n).op ≫
        (scalarDualUnitIso 𝕜).hom = _
  rw [inverseSquare]

end ToricPower.IntegralArrangement
