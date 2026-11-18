module

public import ToricPower.DiagonalCellularIdentification
public import ToricPower.InternalDualCellularInclusions

/-!
# The actual dual diagonal comparison on each inverse-cell inclusion

The equality concerns the original internal-dual sheaf complex and its
original cellular coefficient comparison. It supplies the generator
identity needed when its genuine top quotient is evaluated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Y" => toricDiagonalProduct fan
local notation "P" => arrangementDiagonalKernelDiagram fan nonempty regular basis rays
local notation "M" => diagonalExteriorDualDiagram fan nonempty regular basis rays

local instance diagonalCellularInclusionCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance diagonalCellularInclusionBiproducts : HasFiniteBiproducts (Y).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Every original cellular inclusion is the original inverse-label
inclusion into the actual dual diagonal term. -/
@[reassoc]
theorem diagonalExteriorDualComplexIso_inclusion (q : ℕ)
    (c : NormalizedCell A q) :
    arrangementCellularCochainInclusion A ℂ M q c ≫
      (diagonalExteriorDualComplexIso fan nonempty regular basis rays).inv.f q =
    biproduct.ι (fun d : NormalizedCell A q =>
      diagonalInverseProductSheaf fan nonempty regular basis rays d) c ≫
        (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom := by
  change arrangementCellularCochainInclusion A ℂ M q c ≫
      ((arrangementCellularCochainFunctor A ℂ).map
        (diagonalExteriorDualDiagramIso fan nonempty regular basis rays).hom).f q ≫
      (internalDualCellularTermIso A ℂ P q).inv ≫
        (internalDual (Y).Modules).map
          ((diagonalGlobalCellularComplexIso fan nonempty regular basis rays).hom.f q).op = _
  rw [cellularCochainMap_inclusion_assoc,
    internalDualCellularTermIso_inclusion_assoc]
  change (diagonalProductInternalDualIso fan nonempty regular basis rays c).hom ≫
      (internalDual (Y).Modules).map
        (biproduct.π (fun d : NormalizedCell A q =>
          diagonalProductSheaf fan nonempty regular basis rays d) c).op ≫
        (internalDual (Y).Modules).map (𝟙 _).op = _
  rw [op_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  simp only [diagonalExteriorDualTermIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_hom, biproduct.ι_map_assoc, internalDualBiproductIso_ι_inv]

end ToricPower

end
