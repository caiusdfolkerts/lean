module

public import ToricPower.ArrangementClosedDerivedHomModel
public import ToricPower.ArrangementClosedDualSections
public import ToricPower.ClosedDualFunctorExact
public import ToricPower.ArrangementCellularExact
public import ToricPower.AffineSectionsDetection
public import ToricPower.QuasicoherentEnoughInjectives
public import ToricPower.QuasicoherentNegativeFunctorTotalExact
public import ToricPower.QuasicoherentFiniteDualDerivedHom
public import ToricPower.FiniteDualHomModel
public import ToricPower.FiniteCochainSourceBounds
public import ToricPower.CellularOrdinaryHomFunctorComparison
public import ToricPower.ToricSeparated

/-!
# Derived Hom for the actual closed-subtorus cellular source

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

/-- The actual bounded dual chain, retaining its original differential. -/
def arrangementClosedDualChainPlus (M : QCoh X) : CochainComplex.Plus (QCoh X) :=
  finiteDualChainPlus Φ (n+1) M
    (fun q high => arrangementClosedDualFunctor_isZero_X_above fan regular basis rays
      selected M q (by omega))


/-- Genuine derived global sections of the actual dual chain compute
full derived-category Hom from the original cellular source, in every
integer degree and for every quasicoherent target. -/
def arrangementClosedDualDerivedHomEquiv (M : QCoh X) (q : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℂ) q).obj
      ((Γ).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (arrangementClosedDualChainPlus fan regular basis rays selected M)))) ≃ₗ[ℂ]
      (DerivedCategory.Q.obj ((K₊).extend ComplexShape.embeddingUpNat) ⟶
          ((DerivedCategory.singleFunctor (QCoh X) 0).obj M)⟦q⟧) := by
  let above (T : QCoh X) (r : ℕ) (high : n+1 ≤ r) : IsZero (((Φ).obj T).X r) :=
    arrangementClosedDualFunctor_isZero_X_above fan regular basis rays selected T r (by omega)
  let C := arrangementClosedDualChainPlus fan regular basis rays selected M
  let identification : C ≅ finiteDualChainPlus Φ (n+1) M (above M) :=
    eqToIso (show C = finiteDualChainPlus Φ (n+1) M (above M) from rfl)
  exact quasicoherentFiniteDualDerivedHomEquiv ℂ X Φ (n+1)
    (arrangementClosedDualFunctor_preservesInjectives fan regular basis rays selected)
    ((K₊).extend ComplexShape.embeddingUpNat) above
    (fun f quasi => by
      letI := quasi
      exact arrangementClosedDualTotal_map_quasiIso fan regular basis rays selected f)
    (arrangementClosedDualHomModelIso fan regular basis rays selected)
    M C identification q


end ToricPower

end
