module

public import ToricPower.ArrangementClosedSliceTests
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Geometric realization tests give the actual closed-row scalar tests

This is the genuine normalized adjunction, including its actual shift
comparison. The source comparison and nonzero morphism must be proved
for the original cellular realization; neither is assumed by the final
geometric theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays

local instance closedRowsAdjunctionDerivedQCoh : HasDerivedCategory.{1} (QCoh fan.algebraicRealization) :=
  HasDerivedCategory.standard _
local instance closedRowsAdjunctionDerivedIncidence : HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- A genuine nonzero geometric Hom from the normalized cellular
realization gives the precise base closed-row test used for detection. -/
theorem normalizedClosedRowsTest_of_realizationMap (b : fan.Ray → ℤ)
    (selected : Set (Fin s ⊕ Fin n)) (T : DerivedQCoh fan.algebraicRealization)
    (sourceIso :
      (arrangementNormalizedDerivedRealization fan regular basis rays).obj
        ((DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat.{0} ℂ) 0).obj
          (closedIntegralRowsDiagram A selected ℂ)) ≅ T)
    (q : ℤ)
    (f : T ⟶ ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
      (arrangementCartierCoefficient fan regular b))⟦q⟧)
    (nonzero : f ≠ 0) : NormalizedClosedRowsTest fan regular basis rays b selected := by
  let adj := arrangementNormalizedDerivedAdjunction fan regular basis rays
  let source := (DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat.{0} ℂ) 0).obj
    (closedIntegralRowsDiagram A selected ℂ)
  let target := (DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
    (arrangementCartierCoefficient fan regular b)
  let g := adj.homEquiv source (target⟦q⟧) (sourceIso.hom ≫ f)
  let shifted := ((arrangementNormalizedDerivedHom fan regular basis rays).commShiftIso q).app target
  refine ⟨q,g ≫ shifted.hom,?_⟩
  intro zero
  have zeroG : g = 0 := (cancel_mono shifted.hom).mp
    (by simpa only [zero_comp] using zero)
  have zeroF : sourceIso.hom ≫ f = 0 :=
    (adj.homEquiv source (target⟦q⟧)).injective
      (zeroG.trans (adj.homAddEquiv_zero source (target⟦q⟧)).symm)
  exact nonzero ((cancel_epi sourceIso.hom).mp
    (by simpa only [comp_zero] using zeroF))

end ToricPower

end
