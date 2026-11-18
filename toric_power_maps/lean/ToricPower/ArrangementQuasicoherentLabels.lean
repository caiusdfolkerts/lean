module

public import ToricPower.ArrangementCochainLabels
public import ToricPower.QuasicoherentBaseLinear

/-!
# The actual arrangement labels in quasicoherent sheaves

The contravariant Cartier diagrams and the covariant reflected inverse
diagram take values in actual quasicoherent sheaves because their labels
are invertible. Their maps are unchanged: the full-subcategory lift keeps
every literal monomial morphism. No derived full-faithfulness assertion
is used to construct these diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

/-- The genuine unreflected Cartier diagram in the actual quasicoherent
category; its underlying functor is the original monomial diagram. -/
def arrangementRightQuasicoherentDiagram : Cᵒᵖ ⥤ QCoh fan.algebraicRealization :=
  ObjectProperty.lift _ (arrangementRightCartierDiagram fan nonempty regular basis rays)
    (fun c => by
      letI := toricSchemeIntegral fan nonempty
      letI := (invariantCartierDivisor fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)).isInvertible_sheaf
      change (invariantCartierDivisor fan nonempty regular
        (diagonalRightCoefficients fan basis rays c.unop.2)).sheaf.IsQuasicoherent
      infer_instance)

instance arrangementRightQuasicoherentDiagram_invertible (c : C) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization
      ((arrangementRightQuasicoherentDiagram fan nonempty regular basis rays).obj (op c)).obj := by
  letI := toricSchemeIntegral fan nonempty
  change TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible fan.algebraicRealization
    (invariantCartierDivisor fan nonempty regular
      (diagonalRightCoefficients fan basis rays c.2)).sheaf
  exact (invariantCartierDivisor fan nonempty regular
    (diagonalRightCoefficients fan basis rays c.2)).isInvertible_sheaf

/-- The actual reflected inverse labels of `A_cell`, now in `QCoh`.
All coefficient maps remain the original positive characters. -/
def arrangementDualLeftQuasicoherentDiagram : C ⥤ QCoh fan.algebraicRealization :=
  ObjectProperty.lift _ (arrangementDualLeftCartierDiagram fan nonempty regular basis rays)
    (fun c => by
      letI := toricSchemeIntegral fan nonempty
      letI := (invariantCartierDivisor fan nonempty regular
        (arrangementDualLeftCoefficients fan basis rays c)).isInvertible_sheaf
      change (invariantCartierDivisor fan nonempty regular
        (arrangementDualLeftCoefficients fan basis rays c)).sheaf.IsQuasicoherent
      infer_instance)

/-- Forgetting quasicoherence gives exactly the previously constructed
literal Cartier functor, on objects and every incidence map. -/
def arrangementRightQuasicoherentInclusionIso :
    arrangementRightQuasicoherentDiagram fan nonempty regular basis rays ⋙
        quasicoherentInclusion fan.algebraicRealization ≅
      arrangementRightCartierDiagram fan nonempty regular basis rays := Iso.refl _

def arrangementDualLeftQuasicoherentInclusionIso :
    arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays ⋙
        quasicoherentInclusion fan.algebraicRealization ≅
      arrangementDualLeftCartierDiagram fan nonempty regular basis rays := Iso.refl _

end ToricPower

end
