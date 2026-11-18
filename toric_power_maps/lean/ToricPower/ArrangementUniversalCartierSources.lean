module

public import ToricPower.ArrangementUniversalCartierLabels
public import ToricPower.CartierMeetDerivedCech
public import ToricPower.CartierHomSectionsDiagram

/-! # Actual universal Cartier sources and their complete Hom diagrams

The contravariant source at an actual universal cell is the inverse of
its absolute ceiling-minus-one label. Its inverse tensor diagram is
identified with the literal covariant universal labels, including all
face maps and all quasicoherent coefficient morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X

def universalCartierCoefficientSources : Uᵒᵖ ⥤ ToricMonomial.Object fan :=
  (universalDualCoefficientDiagram fan basis rays).op ⋙ ToricMonomial.dual fan

def universalCartierSources : letI := toricSchemeIntegral fan nonempty
    Uᵒᵖ ⥤ CartierSources X := by
  letI := toricSchemeIntegral fan nonempty
  exact universalCartierCoefficientSources fan basis rays ⋙
    ToricMonomial.sources fan nonempty regular

def universalCartierQuasicoherentSources : Uᵒᵖ ⥤ Q := by
  letI := toricSchemeIntegral fan nonempty
  exact universalCartierSources fan nonempty regular basis rays ⋙ cartierSourcesQuasicoherent X

def universalSourceDualCoefficientIso :
    (universalCartierCoefficientSources fan basis rays).rightOp ⋙ ToricMonomial.dual fan ≅
      universalDualCoefficientDiagram fan basis rays :=
  NatIso.ofComponents (fun c => ToricMonomial.coefficientIso fan _ _ (by
    change - -(universalDualCoefficients fan basis rays c) = _
    exact neg_neg _)) (by
      intro c d f
      apply Subtype.ext
      exact (add_zero _).trans (zero_add _).symm)

def universalCartierInverseTensorIso :
    letI := toricSchemeIntegral fan nonempty
    cartierLabelTwistDiagram X (universalCartierSources fan nonempty regular basis rays) ≅
      universalDualTensorDiagram fan basis rays nonempty regular := by
  letI := toricSchemeIntegral fan nonempty
  change ((universalCartierCoefficientSources fan basis rays).rightOp ⋙
      (ToricMonomial.sources fan nonempty regular).op ⋙
        cartierSourcesQuasicoherentInverseTensor X).flip ≅
    (universalDualCoefficientDiagram fan basis rays ⋙
      ToricMonomial.quasicoherent fan nonempty regular ⋙ tensoringLeft Q).flip
  exact (flipFunctor U Q Q).mapIso
    (Functor.isoWhiskerLeft (universalCartierCoefficientSources fan basis rays).rightOp
        (ToricMonomial.inverseTensorQuasicoherentIso fan nonempty regular) ≪≫
      Functor.isoWhiskerRight (universalSourceDualCoefficientIso fan basis rays)
        (ToricMonomial.quasicoherent fan nonempty regular ⋙ tensoringLeft Q))

/-- The full actual Hom diagram is the scalar-linear global section
diagram of absolute inverse twists, naturally in both variables. -/
def universalCartierHomSectionsIso :
    letI := toricSchemeIntegral fan nonempty
    Cellular.homDiagram ℂ (universalCartierQuasicoherentSources fan nonempty regular basis rays) ≅
      universalDualTensorDiagram fan basis rays nonempty regular ⋙
        (Functor.whiskeringRight U Q (ModuleCat ℂ)).obj
          (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierHomSectionsDiagramIso ℂ X
      (universalCartierSources fan nonempty regular basis rays) ≪≫
    Functor.isoWhiskerRight (universalCartierInverseTensorIso fan nonempty regular basis rays)
      ((Functor.whiskeringRight U Q (ModuleCat ℂ)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤))

end ToricPower

end
