module

public import ToricPower.ArrangementCellularExact
public import ToricPower.AffineSectionsDetection
public import ToricPower.FiniteFunctorTotalExact

/-!
# The genuine unbounded cellular total

The horizontal terms are the original finite cellular cochains of the
actual Cartier labels. The vertical input may be unbounded in either
direction. Exact coefficient degrees and the actual affine-section
zero detectors prove preservation of all quasi-isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Φ" => arrangementQuasicoherentCellularRealization fan nonempty regular basis rays

local instance cellularTotalBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual finite signed total, retaining every term of the
unbounded coefficient complex and every original cellular incidence. -/
def arrangementCellularTotalFunctor :
    CochainComplex (C ⥤ ModuleCat ℂ) ℤ ⥤ CochainComplex (QCoh X) ℤ :=
  FunctorTotal.functor Φ (n + 1)

instance arrangementCellularTotalFunctor_additive :
    (arrangementCellularTotalFunctor fan nonempty regular basis rays).Additive := by
  unfold arrangementCellularTotalFunctor
  infer_instance

/-- Quasi-isomorphism preservation is proved for the literal total,
without a boundedness hypothesis on either input complex. -/
theorem arrangementCellularTotalFunctor_map_quasiIso
    {K L : CochainComplex (C ⥤ ModuleCat ℂ) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((arrangementCellularTotalFunctor fan nonempty regular basis rays).map f) := by
  letI (σ : fan.cones) : PreservesFiniteLimits (arrangementAffineSectionFunctor fan σ) :=
    (FiniteCover.schemeBaseSections_exact ℂ X (fan.affineToricChartι σ).opensRange
      (isAffineOpen_opensRange (fan.affineToricChartι σ))).1
  letI (σ : fan.cones) : PreservesFiniteColimits (arrangementAffineSectionFunctor fan σ) :=
    (FiniteCover.schemeBaseSections_exact ℂ X (fan.affineToricChartι σ).opensRange
      (isAffineOpen_opensRange (fan.affineToricChartι σ))).2
  apply FunctorTotal.map_quasiIso_of_exact_detectors Φ (n + 1)
    (arrangementAffineSectionFunctor fan)
  intro M zeroSections
  exact quasicoherent_isZero_of_affineSections ℂ X
    (fun σ : fan.cones => (fan.affineToricChartι σ).opensRange)
    fan.affineToricOpenCover.isOpenCover_opensRange
    (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ)) M zeroSections

end ToricPower

end
