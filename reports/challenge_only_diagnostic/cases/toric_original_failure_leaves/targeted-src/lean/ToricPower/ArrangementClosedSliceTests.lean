module

public import ToricPower.ArrangementCoverTestPullback
public import ToricPower.UniversalClosedRowsDetection
public import ToricPower.ArrangementNormalizedCoverSupport
public import ToricPower.ArrangementCompactLiftModel

/-!
# Closed-subtorus tests give actual affine-plane scalar tests

The proof uses the full normalized Cartier lift, its proved finite
cohomological support, the actual covering right adjunction, and the
unrestricted component coproduct. The normalization shift is explicit.
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

local instance closedSliceTestDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance closedSliceTestDerivedQCoh :
    HasDerivedCategory.{1} (QCoh fan.algebraicRealization) := HasDerivedCategory.standard _
local instance closedSliceTestDerivedCells :
    HasDerivedCategory.{1} (IncidenceObject A ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
local instance closedSliceTestDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _
local instance closedSliceTestDerivedElements :
    HasDerivedCategory.{1} ((universalWeightFunctor A).Elements ⥤ ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _

/-- This is a test on the actual closed constant quotient-cell diagram.
Its geometric verification comes from linear-inclusion duality. -/
def NormalizedClosedRowsTest (b : fan.Ray → ℤ) (selected : Set (Fin s ⊕ Fin n)) : Prop :=
  ∃ q : ℤ, ∃ f :
    (DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat.{0} ℂ) 0).obj
      (closedIntegralRowsDiagram A selected ℂ) ⟶
    ((arrangementNormalizedDerivedHom fan regular basis rays).obj
      ((DerivedCategory.singleFunctor (QCoh fan.algebraicRealization) 0).obj
        (arrangementCartierCoefficient fan regular b)))⟦q⟧, f ≠ 0

/-- Every nonzero closed-subtorus test yields a nonzero test on one
literal affine-plane component of the full universal cover. -/
theorem exists_normalized_affine_slice_test_of_closed_rows
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (selected : Set (Fin s ⊕ Fin n))
    (covered : ∀ {q : ℕ} (c : Cell (augmentedForms A) q), selected ⊆ c.val.2 →
      ∃ a : Fin n → ℤ, cellCenter (augmentedForms A) c - latticeLift a ∈
        arrangementZeroSlice (augmentedForms A) selected)
    (test : NormalizedClosedRowsTest fan regular basis rays b selected) :
    ∃ m : Fin n → ℤ, ∃ q : ℤ, ∃ f :
      (Cellular.closedConstantFunctor ℂ (universalAffineSliceSupport A selected m)
        (universalAffineSliceSupport_downward A selected m)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{0} ℂ) 0).obj (ModuleCat.of ℂ ℂ)) ⟶
        (DerivedCategory.Q.obj (normalizedUniversalLiftComplex fan basis rays b))⟦q⟧,
      f ≠ 0 := by
  obtain ⟨r,f,hf⟩ := test
  let K := complexDiagramTranspose
    (arrangementNormalizedLiftedCech fan basis rays b ⋙
      ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} ℂ))
  let sumTarget := (ElementPushdown.functor (universalWeightFunctor A)
    (D := ModuleCat.{0} ℂ)).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (arrangementNormalizedCoverComplex fan basis rays b))
  let target := (shiftFunctor _ r).mapIso
      (arrangementNormalizedRHomCoverPushdownIso fan regular basis rays b) ≪≫
    ((shiftFunctorAdd' _ (n : ℤ) r ((n : ℤ)+r) rfl).app sumTarget).symm
  have sumNonzero : f ≫ target.hom ≠ 0 := by
    intro zero
    apply hf
    rw [← cancel_mono target.hom,zero_comp]
    exact zero
  obtain ⟨a,ha⟩ := exists_nonzero_universal_pullback_of_sum A ℂ K
    (arrangementNormalizedCoverComplex_finite_support fan regular basis rays complete b)
    ((DerivedCategory.singleFunctor (IncidenceObject A ⥤ ModuleCat.{0} ℂ) 0).obj
      (closedIntegralRowsDiagram A selected ℂ)) ((n : ℤ)+r) (f ≫ target.hom) sumNonzero
  let source := ((ElementPushdown.baseRestriction (universalCoverProjection A)
    (D := ModuleCat.{0} ℂ)).mapDerivedCategorySingleFunctor 0).app
      (closedIntegralRowsDiagram A selected ℂ)
  have pulledNonzero : source.inv ≫ a ≠ 0 := by
    intro zero
    apply ha
    rw [← cancel_epi source.inv,comp_zero]
    exact zero
  obtain ⟨m,g,hg⟩ := exists_nonzero_affine_plane_of_closed_rows A selected covered ℂ
    ((DerivedCategory.Q.obj (normalizedUniversalLiftComplex fan basis rays b))⟦(n : ℤ)+r⟧)
    (source.inv ≫ a) pulledNonzero
  exact ⟨m,(n : ℤ)+r,g,hg⟩

end ToricPower

end
