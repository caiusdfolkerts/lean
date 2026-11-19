module

public import ToricPower.ArrangementClosedDerivedSource
public import ToricPower.ArrangementClosedDualSections
public import ToricPower.ClosedDualFunctorExact
public import ToricPower.ArrangementCellularExact
public import ToricPower.AffineSectionsDetection
public import ToricPower.QuasicoherentEnoughInjectives
public import ToricPower.QuasicoherentNegativeFunctorTotalExact
public import ToricPower.FiniteDualDerivedHom
public import ToricPower.QuasicoherentFiniteDualHomModel
public import ToricPower.FiniteCochainSourceBounds
public import ToricPower.CellularOrdinaryHomFunctorComparison
public import ToricPower.ToricSeparated

/-!
# The actual closed-subtorus full Hom complex

The source here is the original cellular realization of the closed
integral-row diagram. Its full derived Hom is computed by the actual
finite inverse-Cartier chain, followed by the genuine right-derived
global-section functor. Exactness is detected on the original affine
toric cover; all injective-preservation and finite-support hypotheses
are proved for these objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open CochainComplex HomComplex

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (selected : Set (Fin s ⊕ Fin n))

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Φ" => arrangementClosedDualFunctor fan regular basis rays selected
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤
local notation "K₊" => arrangementClosedSubtorusCochain fan regular basis rays selected

attribute [local instance] closedDerivedIntegral closedDerivedNoetherian closedDerivedSeparated
  closedDerivedBiproducts closedDerivedQCoh closedDerivedScalar closedDerivedAdditive
  closedDerivedDegreeLimits closedDerivedDegreeColimits

/-- The full Hom complex, with its original target differential. -/

def arrangementClosedDualHomModelIso (I : CochainComplex (QCoh X) ℤ) :
    ((Γ).mapHomologicalComplex (.up ℤ)).obj (NegativeFunctorTotal.total Φ (n+1) I) ≅
      linearHomComplex ℂ ((K₊).extend ComplexShape.embeddingUpNat) I :=
  quasicoherentFiniteDualHomModelIso ℂ X Φ (K₊) I (n+1)
    (fun q high => arrangementClosedSubtorusCochain_isZero_X_above fan regular basis rays
      selected q (by omega))
    (arrangementClosedDualOrdinaryHomFunctorIso fan regular basis rays selected)


end ToricPower
end
