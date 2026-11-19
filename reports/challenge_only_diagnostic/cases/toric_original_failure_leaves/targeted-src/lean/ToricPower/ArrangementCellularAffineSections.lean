module

public import ToricPower.ReflectedToricLaurentSections
public import ToricPower.AffineSectionsColimits
public import ToricPower.CovariantCopowerComparison
public import ToricPower.ArrangementCellularCoefficientFunctor
public import ToricPower.ArrangementRepresentableTerms

/-!
# Actual affine sections of quasicoherent cellular realization

The cellular complex is first formed in the actual quasicoherent category.
Its exact affine section functor carries it, with every differential, to
the full Laurent coefficient complex. Copowers are unrestricted, so the
comparison applies to arbitrary vector diagrams and their genuine free
representables. The top-class identification is a subsequent theorem.
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
local notation "Q" => arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays

local instance : HasFiniteBiproducts (QCoh X) := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (X).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original finite cellular construction in actual quasicoherent
sheaves, with all positive-character incidence arrows. -/
def arrangementQuasicoherentCellularRealization :
    (C ⥤ ModuleCat ℂ) ⥤ CochainComplex (QCoh X) ℕ :=
  arrangementCellularRealization A ℂ Q

/-- The literal scalar sections of a quasicoherent coefficient on a
genuine affine toric chart. -/
abbrev arrangementAffineSectionFunctor (σ : fan.cones) : QCoh X ⥤ ModuleCat ℂ :=
  quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections ℂ X
    (fan.affineToricChartι σ).opensRange

instance arrangementAffineSectionFunctor_preservesColimits (σ : fan.cones) :
    PreservesColimitsOfSize.{0,0} (arrangementAffineSectionFunctor fan σ) :=
  affineBaseSections_preservesColimits ℂ X (fan.affineToricChartι σ).opensRange
    (isAffineOpen_opensRange (fan.affineToricChartι σ))

/-- After actual affine sections, the complete cellular realization is
the original scalar cellular complex of the full Laurent labels. -/
def arrangementCellularAffineSectionsIso (σ : fan.cones) (F : C ⥤ ModuleCat ℂ) :
    (((arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
      ((arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj F)) ≅
        (arrangementCellularRealization A ℂ
          (reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ)).obj F := by
  let H := arrangementAffineSectionFunctor fan σ
  let e : Q ⋙ H ≅ reflectedLaurentDiagram A (fanConeRaySet fan rays σ) ℂ :=
    (reflectedToricSectionsDiagramIso fan nonempty regular basis rays σ).symm
  exact cellularCoefficientComplexIso A ℂ H
      (Cellular.covariantCopowerDiagram ℂ Q F) ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (Cellular.covariantCopowerCoefficientIso ℂ F H Q) ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      ((Cellular.covariantCopowerLabelFunctor ℂ F).mapIso e)

/-- The representable specialization retains the independently defined
full Laurent complex, rather than substituting its cohomology. -/
def arrangementRepresentableAffineSectionsIso (σ : fan.cones) (c : C) :
    (((arrangementAffineSectionFunctor fan σ).mapHomologicalComplex (.up ℕ)).obj
      ((arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj
        (Cellular.representable ℂ c))) ≅
      representableLaurentCellularComplex A (fanConeRaySet fan rays σ) ℂ c :=
  arrangementCellularAffineSectionsIso fan nonempty regular basis rays σ
    (Cellular.representable ℂ c)

/-- Forgetting quasicoherence recovers the original sheaf complex,
through the actual coproduct-preserving full inclusion. -/
def arrangementCellularUnderlyingIso (F : C ⥤ ModuleCat ℂ) :
    (((quasicoherentInclusion X).mapHomologicalComplex (.up ℕ)).obj
      ((arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj F)) ≅
      (arrangementCellularSheafRealization fan nonempty regular basis rays).obj F :=
  cellularCoefficientComplexIso A ℂ (quasicoherentInclusion X)
      (Cellular.covariantCopowerDiagram ℂ Q F) ≪≫
    (arrangementCellularCochainFunctor A ℂ).mapIso
      (Cellular.covariantCopowerCoefficientIso ℂ F (quasicoherentInclusion X) Q)

end ToricPower

end
