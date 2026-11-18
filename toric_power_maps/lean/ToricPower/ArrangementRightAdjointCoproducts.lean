module

public import ToricPower.ArrangementNormalizedRHom
public import ToricPower.ArrangementDerivedCoproducts
public import ToricPower.CartierMeetCoproducts
public import ToricPower.DerivedExactCoproducts
public import ToricPower.CoproductPreservationByFactor
public import ToricPower.ReflectiveCoproducts
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-!
# Arbitrary coproducts for the actual normalized toric right adjoint

The finite signed Čech model preserves actual sums on unbounded
complexes. The diagram localization preserves sums by exactness and
K-projective replacement. If geometric reconstruction gives full
faithfulness, these facts descend through the actual source localization
to all quasicoherent derived objects. No boundedness, properness, or
finite-dimensional coefficient hypothesis enters this argument.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "Cells" => IncidenceObject (fanArrangementMatrix fan basis rays)
local notation "Q" => QCoh fan.algebraicRealization

local instance arrangementCoproductsDerivedQCoh : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance arrangementCoproductsDerivedCells : HasDerivedCategory.{1}
    (Cells ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The literal full finite model, including the normalization shift. -/
def arrangementNormalizedComplexModel :
    CochainComplex Q ℤ ⥤ CochainComplex (Cells ⥤ ModuleCat.{0} ℂ) ℤ :=
  shiftFunctor (CochainComplex Q ℤ) (n : ℤ) ⋙
    normalizedCartierFiniteComplexModel fan nonempty regular basis rays

/-- All factors are the already proved actual comparisons. -/
def arrangementNormalizedComplexModelFactors :
    DerivedCategory.Q ⋙ arrangementNormalizedDerivedHom fan regular basis rays ≅
      arrangementNormalizedComplexModel fan regular basis rays ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (arrangementNormalizedHomFiniteModelIso fan nonempty regular basis rays) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Q.commShiftIso (n : ℤ)).symm
      (normalizedCartierFiniteModel fan nonempty regular basis rays) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (CochainComplex Q ℤ) (n : ℤ))
      (normalizedCartierFiniteModelFactors fan nonempty regular basis rays) ≪≫
    (Functor.associator _ _ _).symm

theorem normalizedCartierFiniteComplexModel_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (normalizedCartierFiniteComplexModel fan nonempty regular basis rays) := by
  letI := toricSchemeIntegral fan nonempty
  exact cartierFiniteMeetComplex_preservesCoproducts ℂ fan.algebraicRealization
    (normalizedCartierSources fan nonempty regular basis rays)
    (toricMeetChartOpenFunctor fan)
    (fun a => isAffineOpen_opensRange (fan.affineToricChartι (toricMeetChartEquiv fan a))) I

theorem arrangementNormalizedComplexModel_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (arrangementNormalizedComplexModel fan regular basis rays) := by
  letI := normalizedCartierFiniteComplexModel_preservesCoproducts fan regular basis rays I
  unfold arrangementNormalizedComplexModel
  infer_instance

theorem arrangementDiagramLocalization_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q (C := Cells ⥤ ModuleCat.{0} ℂ)) :=
  CoproductComplex.derivedQ_preservesCoproducts
    (Cellular.diagramDerived_kProjective_representative ℂ (fun c : Cells => c.1)
      (fun f => incidence_dimension_le _ f)
      (fun f h => (incidence_eq_of_dimension_eq _ f h).1) n
      (fun c => cell_dimension_le _ c.2.val)) I

variable (fullyFaithful : (arrangementNormalizedDerivedHom fan regular basis rays).FullyFaithful)
include fullyFaithful in
/-- Every coproduct, with arbitrary unbounded quasicoherent inputs. -/
theorem arrangementNormalizedDerivedHom_preservesCoproducts (I : Type) :
    PreservesColimitsOfShape (Discrete I)
      (arrangementNormalizedDerivedHom fan regular basis rays) := by
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Full := fullyFaithful.full
  letI : (arrangementNormalizedDerivedHom fan regular basis rays).Faithful := fullyFaithful.faithful
  letI := arrangementNormalizedComplexModel_preservesCoproducts fan regular basis rays I
  letI := arrangementDiagramLocalization_preservesCoproducts fan basis rays I
  letI : PreservesColimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ arrangementNormalizedDerivedHom fan regular basis rays) :=
    preservesColimitsOfShape_of_natIso
      (arrangementNormalizedComplexModelFactors fan regular basis rays).symm
  exact preservesCoproducts_of_essentiallySurjective_factor DerivedCategory.Q
    (arrangementNormalizedDerivedHom fan regular basis rays) I

end ToricPower
end
