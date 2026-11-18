module

public import ToricPower.ArrangementUniversalCartierSources
public import ToricPower.ArrangementNormalizedSources

/-! # Actual normalized Hom diagrams on universal cells

The comparison keeps every deck character and every incidence map.
It is a natural isomorphism on arbitrary quasicoherent coefficients,
before passage to complexes or derived categories.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

section Interchange

universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} D] [Category.{v₅} E]

/-- Precomposition and coefficient postcomposition commute through
the same literal map of a diagram. -/
def diagramPrePostcomposeIso (F : A ⥤ B ⥤ C) (q : D ⥤ B) (S : C ⥤ E) :
    F ⋙ (Functor.whiskeringLeft D B C).obj q ⋙
      (Functor.whiskeringRight D C E).obj S ≅
    F ⋙ (Functor.whiskeringRight B C E).obj S ⋙
      (Functor.whiskeringLeft D B E).obj q := Iso.refl _

end Interchange

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X

/-- Full scalar-linear Hom sections for the normalized sources. -/
def normalizedCartierHomSectionsIso :
    letI := toricSchemeIntegral fan nonempty
    Cellular.homDiagram ℂ (normalizedCartierQuasicoherentSources fan nonempty regular basis rays) ≅
      normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays ⋙
        (Functor.whiskeringRight C Q (ModuleCat ℂ)).obj
          (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierHomSectionsDiagramIso ℂ X
      (normalizedCartierSources fan nonempty regular basis rays) ≪≫
    Functor.isoWhiskerRight (normalizedCartierInverseTensorIso fan nonempty regular basis rays)
      ((Functor.whiskeringRight C Q (ModuleCat ℂ)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤))

/-- Pulling back the actual normalized Hom diagram to universal cells
agrees with the absolute Cartier Hom diagram, with genuine deck maps. -/
def universalNormalizedHomDiagramIso :
    Cellular.homDiagram ℂ (universalCartierQuasicoherentSources fan nonempty regular basis rays) ≅
      Cellular.homDiagram ℂ (normalizedCartierQuasicoherentSources fan nonempty regular basis rays) ⋙
        (Functor.whiskeringLeft U C (ModuleCat ℂ)).obj (universalCoverProjection A) := by
  letI := toricSchemeIntegral fan nonempty
  exact universalCartierHomSectionsIso fan nonempty regular basis rays ≪≫
    Functor.isoWhiskerRight (universalNormalizedTensorDiagramIso fan basis rays nonempty regular)
      ((Functor.whiskeringRight U Q (ModuleCat ℂ)).obj
        (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤)) ≪≫
    diagramPrePostcomposeIso (normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays)
      (universalCoverProjection A)
      (quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X ⊤) ≪≫
    Functor.isoWhiskerRight (normalizedCartierHomSectionsIso fan nonempty regular basis rays).symm
      ((Functor.whiskeringLeft U C (ModuleCat ℂ)).obj (universalCoverProjection A))

end ToricPower

end
