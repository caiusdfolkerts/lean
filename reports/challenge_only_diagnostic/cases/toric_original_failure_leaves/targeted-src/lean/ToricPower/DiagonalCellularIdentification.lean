module

public import ToricPower.ArrangementCartierDiagram
public import ToricPower.ArrangementInternalDualComplex
public import ToricPower.DiagonalExteriorDualLabels
public import ToricPower.SheafInternalDualLinear

/-!
# The actual diagonal is the actual cellular coefficient complex

The genuine global diagonal boundary and the original cellular functor
have identical supported columns. This proves a complete complex
isomorphism. Internal duality and the actual exterior inverse pairings
then identify the full dual diagonal with the cellular cochain complex
of the inverse exterior labels, retaining every character map.
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
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Y" => toricDiagonalProduct fan
local notation "C" => IncidenceObject A
local notation "P" => arrangementDiagonalKernelDiagram fan nonempty regular basis rays
local notation "Q" => Functor.rightOp
  (arrangementDiagonalKernelDiagram fan nonempty regular basis rays) ⋙
    internalDual (Scheme.Modules (toricDiagonalProduct fan))
local notation "G" => diagonalGlobalSheafComplex fan nonempty regular basis rays

local instance : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

/-- The two actual columns agree on the full original finite support. -/
theorem diagonalCellularColumn_eq (q : ℕ) (j : NormalizedCell A (q+1)) :
    arrangementCellularColumn A ℂ P q j =
      diagonalGlobalLinearColumn fan nonempty regular basis rays q j := by
  simp only [arrangementCellularColumn, diagonalGlobalLinearColumn,
    Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro p supported
  congr 1
  have incidence := incidenceTranslation_of_column_ne_zero A ℂ q j p.1 p.2
    (Finsupp.mem_support_iff.mp supported)
  let arrow : (⟨q,p.1⟩ : C) ⟶ ⟨q+1,j⟩ := ⟨p.2, incidence⟩
  have positive := diagonalEntryRegular_of_incidence fan basis rays arrow
  rw [cellularCoefficientHom, dif_pos incidence,
    diagonalProductCharacterHom, dif_pos positive]
  rfl

/-- The complete actual boundary, before any homology comparison. -/
theorem diagonalCellularBoundary_eq (q : ℕ) :
    arrangementCellularBoundary A ℂ P q =
      diagonalGlobalSheafBoundary fan nonempty regular basis rays q := by
  rw [diagonalGlobalSheafBoundary_eq_linear]
  apply biproduct.hom_ext'
  intro j
  rw [arrangementCellularBoundary_column]
  change arrangementCellularColumn A ℂ P q j =
    biproduct.ι (fun c : NormalizedCell A (q+1) =>
      diagonalProductSheaf fan nonempty regular basis rays c) j ≫
        diagonalGlobalLinearBoundary fan nonempty regular basis rays q
  rw [diagonalGlobalLinearBoundary_column, diagonalCellularColumn_eq]

/-- No matrix or sign changes enter this full complex identification. -/
def diagonalGlobalCellularComplexIso :
    G ≅ arrangementCellularChainComplex A ℂ P :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro q r relation
    obtain rfl : q = r+1 := relation.symm
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rw [arrangementCellularChainComplex_d]
    simpa only [diagonalGlobalSheafComplex, ChainComplex.of_d] using
      diagonalCellularBoundary_eq fan nonempty regular basis rays r)

/-- The actual global internal-dual complex is the genuine cellular
cochain complex of the actual dual kernel coefficient functor. -/
def diagonalInternalDualCellularIso :
    internalDualComplex (Y).Modules G ≅ arrangementCellularCochainComplex A ℂ Q :=
  internalDualComplexIso (Y).Modules
      (diagonalGlobalCellularComplexIso fan nonempty regular basis rays) ≪≫
    internalDualCellularComplexIso A ℂ P

/-- The exterior inverse diagram is transported through the actual
evaluation isomorphisms; its maps are computed explicitly below. -/
def diagonalExteriorDualDiagram : C ⥤ (Y).Modules where
  obj c := diagonalInverseProductSheaf fan nonempty regular basis rays c.2
  map {c d} f :=
    (diagonalProductInternalDualIso fan nonempty regular basis rays c.2).hom ≫
      (Q).map f ≫
        (diagonalProductInternalDualIso fan nonempty regular basis rays d.2).inv
  map_id c := by
    rw [CategoryTheory.Functor.map_id]
    change (diagonalProductInternalDualIso fan nonempty regular basis rays c.2).hom ≫
        𝟙 ((internalDual (Y).Modules).obj
          (op (diagonalProductSheaf fan nonempty regular basis rays c.2))) ≫
        (diagonalProductInternalDualIso fan nonempty regular basis rays c.2).inv = _
    rw [Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by simp

/-- The evaluation pairings give a genuine natural isomorphism. -/
def diagonalExteriorDualDiagramIso :
    diagonalExteriorDualDiagram fan nonempty regular basis rays ≅ Q :=
  NatIso.ofComponents
    (fun c => diagonalProductInternalDualIso fan nonempty regular basis rays c.2)
    (by intro c d f; simp [diagonalExteriorDualDiagram])

/-- Every transported incidence map is the independently specified
same-character reverse map on the two inverse Cartier factors. -/
theorem diagonalExteriorDualDiagram_map {c d : C} (f : c ⟶ d) :
    (diagonalExteriorDualDiagram fan nonempty regular basis rays).map f =
      diagonalInverseProductCharacterMap fan nonempty regular basis rays d.2 c.2 f.val
        (diagonalEntryRegular_of_incidence fan basis rays f) := by
  change (diagonalProductInternalDualIso fan nonempty regular basis rays c.2).hom ≫
      (internalDual (Y).Modules).map ((P).map f.op).op ≫
        (diagonalProductInternalDualIso fan nonempty regular basis rays d.2).inv = _
  rw [arrangementDiagonalKernelDiagram_map,
    ← Category.assoc, diagonalProductInternalDualIso_character,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The full internal dual is the cellular cochain complex of the
actual exterior inverse labels, with all original maps verified. -/
def diagonalExteriorDualComplexIso :
    internalDualComplex (Y).Modules G ≅
      arrangementCellularCochainComplex A ℂ
        (diagonalExteriorDualDiagram fan nonempty regular basis rays) :=
  diagonalInternalDualCellularIso fan nonempty regular basis rays ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (diagonalExteriorDualDiagramIso fan nonempty regular basis rays).symm

end ToricPower

end
