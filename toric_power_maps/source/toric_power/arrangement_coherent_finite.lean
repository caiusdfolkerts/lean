module

public import ToricPower.ArrangementNormalizedLinear
public import ToricPower.AffineRightDerivedPlusComparison
public import ToricPower.ToricCartierCechFinite
public import ToricPower.CoherentBaseLinear
public import ToricPower.DerivedPropertyFromSingles

/-!
# Actual finite incidence models of coherent toric derived objects

Every coherent sheaf is compared with the full scalar-linear Čech
complex for all inverse Cartier labels. Proper cohomology finiteness and
the uniform affine-cover bound give a bounded finite incidence model.
Actual truncation triangles extend this to the literal bounded coherent
derived category. The normalized adjoint retains both the boundary
Cartier twist and the dimension shift.
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
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X
local notation "P" => normalizedCartierSources fan nonempty regular basis rays
local notation "Pq" => normalizedCartierQuasicoherentSources fan nonempty regular basis rays
local notation "U" => toricDerivedChartOpen fan
local notation "l" => toricDerivedChartList fan
local notation "charts" => toricMeetChartOpenFunctor fan
local notation "Baff" => normalizedCartierAffineRHom fan nonempty regular basis rays
local notation "iCoh" => boundedCoherentToQuasicoherent X

local instance arrangementCoherentFiniteInstance1 : IsIntegral X := toricSchemeIntegral fan nonempty
local instance arrangementCoherentFiniteInstance2 : IsNoetherian X := toricScheme_isNoetherian fan
local instance arrangementCoherentFiniteInstance3 : fan.algebraicRealization.IsSeparated := fan.algebraicRealization_isSeparated
local instance arrangementCoherentFiniteInstance4 : Fintype (ToricMeetChartIndex fan) := Fintype.ofFinite _
local instance arrangementCoherentFiniteInstance5 : HasDerivedCategory.{1} (Coh X) := HasDerivedCategory.standard _
local instance arrangementCoherentFiniteInstance6 : HasDerivedCategory.{1} Q := HasDerivedCategory.standard _
local instance arrangementCoherentFiniteInstance7 : HasDerivedCategory.{1} (C ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

local instance normalizedCoherentLabelLimits (cone : fan.cones) :
    PreservesFiniteLimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ Pq) :=
  (toricDerivedLabelLocalExact fan Pq
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).1
local instance normalizedCoherentLabelColimits (cone : fan.cones) :
    PreservesFiniteColimits (quasicoherentOpenLocalization (U cone).ι ⋙ Cellular.homDiagram ℂ Pq) :=
  (toricDerivedLabelLocalExact fan Pq
    (normalizedCartierSources_invertible fan nonempty regular basis rays) cone).2

instance normalizedCartierAffineRHom_commShift : (normalizedCartierAffineRHom fan nonempty regular basis rays).CommShift ℤ :=
  affineRightDerivedCommShift U l (mem_toricDerivedChartList fan)
    (toricDerivedChartOpen_covers fan) (Cellular.homDiagram ℂ Pq)

instance normalizedCartierAffineRHom_isTriangulated : (normalizedCartierAffineRHom fan nonempty regular basis rays).IsTriangulated :=
  affineRightDerived_isTriangulated U l (mem_toricDerivedChartList fan)
    (toricDerivedChartOpen_covers fan) (Cellular.homDiagram ℂ Pq)

/-- Every actual quasicoherent sheaf, with no coherence assumption, has
this full source-natural Čech representative for normalized Cartier Hom. -/
def normalizedCartierAffineSingleCechIso (M : Q) :
    (normalizedCartierAffineRHom fan nonempty regular basis rays).obj ((DerivedCategory.singleFunctor Q 0).obj M) ≅
      natDiagramDerivedObject ℂ
        (cartierLabelLinearCechDiagram ℂ X P charts M) :=
  (normalizedCartierAffineRHom fan nonempty regular basis rays).mapIso (((DerivedCategory.Plus.singleFunctorιIso Q 0).app M).symm) ≪≫
    (affineRightDerivedPlusNatIso U (toricDerivedChartOpen_covers fan)
      (Cellular.homDiagram ℂ Pq) l (mem_toricDerivedChartList fan)).app
        ((DerivedCategory.Plus.singleFunctor Q 0).obj M) ≪≫
    cartierRHomPlusSingleCechIso ℂ X P charts
      (toricMeetChartOpen_tupleMeet fan)
      (fun a b => map_inf (toricMeetChartOpenHom fan) a b)
      (toricMeetChartOpen_covers fan)
      (fun a => isAffineOpen_opensRange
        (fan.affineToricChartι (toricMeetChartEquiv fan a))) M

/-- The finite model is supplied by the actual finite directed
incidence category, after proving bounded finite cohomology geometrically. -/
theorem normalizedCartierAffineSingle_finiteModel (complete : fan.IsComplete)
    (M : Q) [M.obj.IsFinitePresentation] :
    Cellular.finiteInjectiveModels ℂ ((normalizedCartierAffineRHom fan nonempty regular basis rays).obj ((DerivedCategory.singleFunctor Q 0).obj M)) := by
  let model := natDiagramDerivedObject ℂ
    (cartierLabelLinearCechDiagram ℂ X P charts M)
  have hm : Cellular.finiteInjectiveModels ℂ model :=
    Cellular.bounded_finiteInjectiveModel ℂ (fun c : C => c.1)
      (fun f => incidence_dimension_le A f)
      (fun f h => (incidence_eq_of_dimension_eq A f h).1) n
      (fun c => cell_dimension_le A c.2.val) model
      (toricCartierCechDerived_bounded fan P M)
      (toricCartierCechDerived_pointwiseFinite fan P regular complete M)
  exact (Cellular.finiteInjectiveModels ℂ).prop_of_iso
    (normalizedCartierAffineSingleCechIso fan regular basis rays M).symm hm

/-- Every literal bounded coherent object has an actual finite injective
incidence model after applying the normalized-source affine Hom functor. -/
theorem normalizedCartierAffineCoherent_finiteModel (complete : fan.IsComplete)
    (K : DbCoh X) : Cellular.finiteInjectiveModels ℂ ((normalizedCartierAffineRHom fan nonempty regular basis rays).obj ((boundedCoherentToQuasicoherent fan.algebraicRealization).obj K)) := by
  let F := (coherentToQuasicoherent X).mapDerivedCategory ⋙ Baff
  apply derivedBoundedProperty_of_singles F (Cellular.finiteInjectiveModels ℂ) ?_ K.obj K.property
  intro M
  letI : ((coherentToQuasicoherent X).obj M).obj.IsFinitePresentation := M.property
  exact (Cellular.finiteInjectiveModels ℂ).prop_of_iso
    ((normalizedCartierAffineRHom fan nonempty regular basis rays).mapIso (((coherentToQuasicoherent X).mapDerivedCategorySingleFunctor 0).app M)).symm
    (normalizedCartierAffineSingle_finiteModel fan regular basis rays complete
      ((coherentToQuasicoherent X).obj M))

/-- The actual normalized right adjoint differs from the normalized-source
Cartier Hom functor by exactly the displayed inverse dimension shift. -/
def arrangementNormalizedHomAffineIso :
    arrangementNormalizedDerivedHom fan regular basis rays ≅
      shiftFunctor (DerivedCategory Q) (n : ℤ) ⋙ Baff :=
  arrangementNormalizedHomFiniteModelIso fan nonempty regular basis rays ≪≫
    Functor.isoWhiskerLeft (shiftFunctor (DerivedCategory Q) (n : ℤ))
      (normalizedCartierFiniteRHomIso fan nonempty regular basis rays)

/-- The complete-case geometric finiteness theorem for the actual right
adjoint on the original bounded coherent derived category. -/
theorem arrangementNormalizedCoherent_finiteModel (complete : fan.IsComplete)
    (K : DbCoh X) :
    Cellular.finiteInjectiveModels ℂ
      ((arrangementNormalizedDerivedHom fan regular basis rays).obj ((boundedCoherentToQuasicoherent fan.algebraicRealization).obj K)) := by
  have h := normalizedCartierAffineCoherent_finiteModel fan regular basis rays complete
    (K⟦(n : ℤ)⟧)
  have h' := (Cellular.finiteInjectiveModels ℂ).prop_of_iso
    ((normalizedCartierAffineRHom fan nonempty regular basis rays).mapIso (((boundedCoherentToQuasicoherent fan.algebraicRealization).commShiftIso (n : ℤ)).app K)) h
  exact (Cellular.finiteInjectiveModels ℂ).prop_of_iso
    ((arrangementNormalizedHomAffineIso fan regular basis rays).app ((boundedCoherentToQuasicoherent fan.algebraicRealization).obj K)).symm h'

end ToricPower
end
