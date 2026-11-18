module

public import ToricPower.ArrangementNormalizedCoverSupport
public import ToricPower.ArrangementCompactLiftModel
public import ToricPower.ArrangementNormalizedSupport
public import ToricPower.ArrangementPowerCoverDetection

/-!
# Detection of the original normalized Cartier object from a geometric branch

This applies the full covering transfer to the actual Čech lift. The
complete-fan cohomology theorem discharges its fiber-support hypothesis.
The inverse boundary twist and the rank shift are retained exactly.
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
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

local instance normalizedBranchDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance normalizedBranchDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalizedBranchDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalizedBranchDerivedElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalizedBranchDerivedWeighted :
    HasDerivedCategory.{1} (WeightedIncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- Every original integral character is retained in the target. The
conclusion uses the actual normalized right adjoint of the Cartier line. -/
theorem exists_nonzero_normalized_power_of_geometric_branch
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (ell : ℕ) (positive : 0 < ell)
    (E : CochainComplex (IncidenceObject A ⥤ ModuleCat.{0} ℂ) ℤ)
    (u : Fin n → ℤ) (q : ℤ)
    (f : (ElementPushdown.baseRestriction (powerInverseBranchFunctor A ell positive u)
      (D := ModuleCat.{0} ℂ)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (universalPeriodicComplex A ℂ E)) ⟶
      (DerivedCategory.Q.obj (normalizedUniversalLiftComplex fan basis rays b))⟦q⟧)
    (nonzeroMap : f ≠ 0) :
    ∃ r : ℤ, ∃ g : (powerDerivedPushdown A ell positive ℂ).obj (DerivedCategory.Q.obj E) ⟶
      ((arrangementNormalizedDerivedHom fan regular basis rays).obj
        ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
          (arrangementCartierCoefficient fan regular b)))⟦r⟧, g ≠ 0 := by
  let K := complexDiagramTranspose
    (arrangementNormalizedLiftedCech fan basis rays b ⋙
      ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} ℂ))
  let branch := (ElementPushdown.baseRestriction (powerInverseBranchFunctor A ell positive u)
    (D := ModuleCat.{0} ℂ)).mapDerivedCategory
  let source := branch.mapIso
    ((ElementPushdown.baseRestriction (universalCoverProjection A)
      (D := ModuleCat.{0} ℂ)).mapDerivedCategoryFactors.app E)
  have nonzeroSource : source.hom ≫ f ≠ 0 := by
    intro zero
    apply nonzeroMap
    rw [← cancel_epi source.hom,comp_zero]
    exact zero
  obtain ⟨a,ha⟩ := exists_nonzero_power_pushdown_of_geometric_branch A ell positive ℂ K
    (arrangementNormalizedCoverComplex_finite_support fan regular basis rays complete b)
    (DerivedCategory.Q.obj E) u q (source.hom ≫ f) nonzeroSource
  let target := (ElementPushdown.functor (universalWeightFunctor A)
    (D := ModuleCat.{0} ℂ)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (arrangementNormalizedCoverComplex fan basis rays b))
  let line := (DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
    (arrangementCartierCoefficient fan regular b)
  let frame : target⟦q⟧ ≅
      ((arrangementNormalizedDerivedHom fan regular basis rays).obj line)⟦q-(n : ℤ)⟧ :=
    (shiftFunctorAdd' _ (n : ℤ) (q-(n : ℤ)) q (by omega)).app target ≪≫
      (shiftFunctor _ (q-(n : ℤ))).mapIso
        (arrangementNormalizedRHomCoverPushdownIso fan regular basis rays b).symm
  refine ⟨q-(n : ℤ),a ≫ frame.hom,?_⟩
  intro zero
  apply ha
  rw [← cancel_mono frame.hom,zero_comp]
  exact zero

end ToricPower

end
