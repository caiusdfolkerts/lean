module

public import ToricPower.ClosedCartierChainSections
public import ToricPower.ArrangementClosedDualFunctor
public import ToricPower.ArrangementCellularAffineSections

/-! # Genuine global Hom of the closed-subtorus cellular source

The source is the original quasicoherent cellular realization of the
closed integral-row coefficient diagram. Global sections of its actual
finite inverse-Cartier chain are naturally the full ordinary Hom chain.
This comparison retains the original target maps and all incidence maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (selected : Set (Fin s ⊕ Fin n))

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤

local instance closedDualSectionIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty
local instance closedDualSectionBiproducts : HasFiniteBiproducts (QCoh fan.algebraicRealization) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual source complex used by the normalized adjunction. -/
def arrangementClosedSubtorusCochain : CochainComplex (QCoh X) ℕ :=
  (arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj
    (closedIntegralRowsDiagram A selected ℂ)

theorem arrangementClosedDualFunctor_eq_closedCartier :
    arrangementClosedDualFunctor fan regular basis rays selected =
      closedCartierChainFunctor A ℂ X
        (arrangementDualLeftCartierSources fan regular basis rays)
        (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected) := by
  exact Functor.assoc (arrangementDualInverseTensorFunctor fan regular basis rays).flip
    (Cellular.closedContravariantLabelEndofunctor
      (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected))
    (arrangementCellularChainFunctor A ℂ)

theorem arrangementDualLeftCartierSourcesQuasicoherent_eq :
    arrangementDualLeftCartierSources fan regular basis rays ⋙
      cartierSourcesQuasicoherent X =
        arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays := rfl

theorem arrangementClosedCartierCopower_eq :
    Cellular.covariantCopowerDiagram ℂ
      (arrangementDualLeftCartierSources fan regular basis rays ⋙ cartierSourcesQuasicoherent X)
      (Cellular.closedScalarDiagram ℂ (closedIntegralRowsSupport A selected)
        (closedIntegralRowsSupport_incidence A selected)) =
    Cellular.covariantCopowerDiagram ℂ
      (arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays)
      (closedIntegralRowsDiagram A selected ℂ) := by
  rw [arrangementDualLeftCartierSourcesQuasicoherent_eq]
  rfl

/-- Full target-functor comparison, including differentials in a
subsequent injective target resolution. -/
def arrangementClosedDualSectionsFunctorIso :
    arrangementClosedDualFunctor fan regular basis rays selected ⋙
      (Γ).mapHomologicalComplex (.down ℕ) ≅
    cellularOrdinaryHomFunctor A ℂ
      (Cellular.covariantCopowerDiagram ℂ
        (arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays)
          (closedIntegralRowsDiagram A selected ℂ)) :=
  eqToIso (congrArg (fun F => F ⋙ (Γ).mapHomologicalComplex (.down ℕ))
      (arrangementClosedDualFunctor_eq_closedCartier fan regular basis rays selected)) ≪≫
    closedCartierChainSectionsFunctorIso A ℂ X
      (arrangementDualLeftCartierSources fan regular basis rays)
      (closedIntegralRowsSupport A selected) (closedIntegralRowsSupport_incidence A selected) ≪≫
    eqToIso (congrArg (cellularOrdinaryHomFunctor A ℂ)
      (arrangementClosedCartierCopower_eq fan regular basis rays selected))

/-- The component is the literal Hom chain of the original source. -/
def arrangementClosedDualSectionsIso (M : QCoh X) :
    (((Γ).mapHomologicalComplex (.down ℕ)).obj
      ((arrangementClosedDualFunctor fan regular basis rays selected).obj M)) ≅
    ordinaryCochainCoefficients ℂ
      (arrangementClosedSubtorusCochain fan regular basis rays selected) M :=
  (arrangementClosedDualSectionsFunctorIso fan regular basis rays selected).app M

end ToricPower

end

