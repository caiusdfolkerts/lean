module

public import ToricPower.ArrangementClosedDualSections
public import ToricPower.ClosedDualFunctorExact
public import ToricPower.ArrangementCellularExact
public import ToricPower.AffineSectionsDetection
public import ToricPower.QuasicoherentEnoughInjectives
public import ToricPower.QuasicoherentNegativeFunctorTotalExact
public import ToricPower.FiniteDualDerivedHom
public import ToricPower.FiniteDualHomModel
public import ToricPower.FiniteCochainSourceBounds
public import ToricPower.CellularOrdinaryHomFunctorComparison
public import ToricPower.ToricSeparated

/-!
# Exactness and coefficients of the actual closed-subtorus dual model

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

local instance closedDerivedIntegral : IsIntegral X := toricSchemeIntegral fan nonempty
local instance closedDerivedNoetherian : IsNoetherian X := toricScheme_isNoetherian fan
local instance closedDerivedSeparated : fan.algebraicRealization.IsSeparated :=
  fan.algebraicRealization_isSeparated
local instance closedDerivedBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedDerivedQCoh : HasDerivedCategory.{1} (QCoh X) :=
  HasDerivedCategory.standard _
local instance closedDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance closedDerivedAdditive : (Φ).Additive :=
  arrangementClosedDualFunctor_additive fan regular basis rays selected
local instance closedDerivedDegreeLimits (q : ℕ) :
    PreservesFiniteLimits (NegativeFunctorTotal.degree Φ q) :=
  arrangementClosedDualFunctor_degree_preservesFiniteLimits fan regular basis rays selected q
local instance closedDerivedDegreeColimits (q : ℕ) :
    PreservesFiniteColimits (NegativeFunctorTotal.degree Φ q) :=
  arrangementClosedDualFunctor_degree_preservesFiniteColimits fan regular basis rays selected q


/-- No coefficient above the full lattice rank occurs. -/
theorem arrangementClosedSubtorusCochain_isZero_X_above (q : ℕ) (above : n < q) :
    IsZero ((K₊).X q) :=
  arrangementQuasicoherentCellularRealization_isZero_X_above fan nonempty regular basis rays
    (closedIntegralRowsDiagram A selected ℂ) q above

/-- The original source, extended by zero to integer cochain degrees. -/
def arrangementClosedSubtorusIntegerCochain : CochainComplex (QCoh X) ℤ :=
  (K₊).extend ComplexShape.embeddingUpNat

theorem arrangementClosedSubtorusIntegerCochain_isZero_outside (p : ℤ)
    (outside : ¬ (0 ≤ p ∧ p < (n+1 : ℕ))) :
    IsZero ((arrangementClosedSubtorusIntegerCochain fan regular basis rays selected).X p) :=
  finiteCochain_extend_isZero_outside (K₊) (n+1)
    (fun q high => arrangementClosedSubtorusCochain_isZero_X_above fan regular basis rays
      selected q (by omega)) p outside


/-- The finite dual total preserves every quasi-isomorphism, including
maps of unbounded input complexes. -/
theorem arrangementClosedDualTotal_map_quasiIso
    {K L : CochainComplex (QCoh X) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (NegativeFunctorTotal.map Φ (n+1) f) :=
  quasicoherent_negativeTotal_map_quasiIso ℂ X Φ
    (fun σ : fan.cones => (fan.affineToricChartι σ).opensRange)
    fan.affineToricOpenCover.isOpenCover_opensRange
    (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ)) (n+1) f


/-- A named equality prevents expansion of the full toric diagram
when comparing the two already proved ordinary-Hom presentations. -/
theorem arrangementClosedSubtorusCochain_eq_cellular :
    K₊ = arrangementCellularCochainComplex A ℂ
      (Cellular.covariantCopowerDiagram ℂ
        (arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays)
        (closedIntegralRowsDiagram A selected ℂ)) := rfl

def arrangementClosedDualOrdinaryHomFunctorIso :
    NegativeFunctorTotal.postcompose Φ Γ ≅ ordinaryCochainCoefficientFunctor ℂ K₊ :=
  arrangementClosedDualSectionsFunctorIso fan regular basis rays selected ≪≫
    eqToIso (cellularOrdinaryHomFunctor_eq A ℂ _) ≪≫
    eqToIso (congrArg (ordinaryCochainCoefficientFunctor ℂ)
      (arrangementClosedSubtorusCochain_eq_cellular fan regular basis rays selected).symm)



end ToricPower
end
