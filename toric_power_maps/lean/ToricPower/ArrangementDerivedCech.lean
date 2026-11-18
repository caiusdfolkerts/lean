module

public import ToricPower.CartierMeetSingleCech
public import ToricPower.ArrangementLiftedCechPushdown
public import ToricPower.ArrangementToricAdjunction
public import ToricPower.AffineRightDerivedPlusComparison
public import ToricPower.ToricCohomologyBound

/-!
# The genuine weighted lift represents the actual toric derived Hom diagram

The finite cone-poset cover retains every actual toric chart. Actual
Cartier inverse multiplication identifies its full Čech diagram with
the difference-coefficient diagram, including every character incidence.
The derived comparison therefore identifies the unrestricted weighted
pushdown with the actual unbounded derived Hom functor on Cartier lines.
No conclusion is inferred merely from matching cohomology groups.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "X" => fan.algebraicRealization
local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "P" => arrangementRightCartierSources fan regular basis rays
local notation "Pq" => arrangementRightQuasicoherentDiagram fan nonempty regular basis rays
local notation "charts" => toricMeetChartOpenFunctor fan
local notation "chartIndex" => toricMeetChartEquiv fan

local instance : IsIntegral X := toricSchemeIntegral fan nonempty
local instance : IsNoetherian X := toricScheme_isNoetherian fan
local instance : fan.algebraicRealization.IsSeparated := fan.algebraicRealization_isSeparated
local instance : Fintype (ToricMeetChartIndex fan) := Fintype.ofFinite _
local instance : HasDerivedCategory.{1} (QCoh X) := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- The actual quasicoherent coefficient line for arbitrary integral ray coefficients. -/
def arrangementCartierCoefficient (b : fan.Ray → ℤ) : QCoh X :=
  quasicoherentCartierObject X (invariantCartierDivisor fan nonempty regular b)

/-- The ordinary inverse-Cartier Čech diagram has exactly the actual
difference-coefficient diagram, with all of its monomial maps. -/
def arrangementCartierLinearCechIso (b : fan.Ray → ℤ) :
    cartierLabelLinearCechDiagram ℂ X P charts
        (arrangementCartierCoefficient fan regular b) ≅
      arrangementDifferenceLinearCechDiagram fan regular basis rays chartIndex b :=
  Functor.isoWhiskerRight (arrangementInverseTensorCoefficientIso fan regular basis rays b)
    (schemeLinearCechComplexFunctor ℂ X (toricCechChartOpen fan chartIndex))

/-- The actual derived Hom diagram on a line is represented by the
whole literal difference-coefficient Čech diagram. -/
def arrangementRHomPlusCechIso (b : fan.Ray → ℤ) :
    ((Cellular.homDiagram ℂ Pq).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (QCoh X) 0).obj
          (arrangementCartierCoefficient fan regular b)) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (arrangementDifferenceLinearCechDiagram fan regular basis rays chartIndex b ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))) :=
  cartierRHomPlusSingleCechIso ℂ X P charts
      (toricMeetChartOpen_tupleMeet fan)
      (fun a b => map_inf (toricMeetChartOpenHom fan) a b)
      (toricMeetChartOpen_covers fan)
      (fun a => isAffineOpen_opensRange (fan.affineToricChartι (chartIndex a)))
      (arrangementCartierCoefficient fan regular b) ≪≫
    DerivedCategory.Q.mapIso (complexDiagramTransposeFunctor.mapIso
      (Functor.isoWhiskerRight
        (arrangementCartierLinearCechIso fan regular basis rays b)
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))))

local instance toricArrangementLabelLocalLimits (cone : fan.cones) :
    PreservesFiniteLimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.homDiagram ℂ Pq) :=
  (toricDerivedLabelLocalExact fan Pq (fun _ => inferInstance) cone).1

local instance toricArrangementLabelLocalColimits (cone : fan.cones) :
    PreservesFiniteColimits
      (quasicoherentOpenLocalization (toricDerivedChartOpen fan cone).ι ⋙
        Cellular.homDiagram ℂ Pq) :=
  (toricDerivedLabelLocalExact fan Pq (fun _ => inferInstance) cone).2

/-- The same actual Čech representation for the genuine unbounded
right-derived Hom functor constructed by the fan's affine cover. -/
def arrangementRHomAffineCechIso (b : fan.Ray → ℤ) :
    (arrangementToricDerivedHom fan nonempty regular basis rays).obj
        ((DerivedCategory.singleFunctor (QCoh X) 0).obj
          (arrangementCartierCoefficient fan regular b)) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (arrangementDifferenceLinearCechDiagram fan regular basis rays chartIndex b ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))) :=
  (arrangementToricDerivedHom fan nonempty regular basis rays).mapIso
      (((DerivedCategory.Plus.singleFunctorιIso (QCoh X) 0).app
        (arrangementCartierCoefficient fan regular b)).symm) ≪≫
    (affineRightDerivedPlusNatIso (toricDerivedChartOpen fan)
      (toricDerivedChartOpen_covers fan) (Cellular.homDiagram ℂ Pq)
      (toricDerivedChartList fan) (mem_toricDerivedChartList fan)).app
        ((DerivedCategory.Plus.singleFunctor (QCoh X) 0).obj
          (arrangementCartierCoefficient fan regular b)) ≪≫
    arrangementRHomPlusCechIso fan regular basis rays b

/-- The unrestricted all-character weighted pushdown is the actual
derived Hom diagram of the actual Cartier line, with every incidence
and the specified complex scalar structure retained. -/
def arrangementRHomAffineWeightedPushdownIso (b : fan.Ray → ℤ) :
    (arrangementToricDerivedHom fan nonempty regular basis rays).obj
        ((DerivedCategory.singleFunctor (QCoh X) 0).obj
          (arrangementCartierCoefficient fan regular b)) ≅
      DerivedCategory.Q.obj (complexDiagramTranspose
        (arrangementLiftedCechPushdown fan basis rays chartIndex b ⋙
          ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))) :=
  arrangementRHomAffineCechIso fan regular basis rays b ≪≫
    DerivedCategory.Q.mapIso (complexDiagramTransposeFunctor.mapIso
      (Functor.isoWhiskerRight
        (arrangementLiftedCechPushdownActualIso fan basis rays chartIndex b regular).symm
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℂ))))

end ToricPower
