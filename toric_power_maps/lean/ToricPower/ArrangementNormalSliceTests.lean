module

public import ToricPower.ArrangementClosedSliceTests
public import ToricPower.ArrangementUniformDetection
public import ToricPower.ToricClosedSliceConcentration

/-!
# Tests for all genuine maximal-support directions

Every eligible cell has a normal space which is a complete linear
subspace for the original fan. An actual cone spans that space, so its
closed-subtorus test supplies precisely the affine slice used by the
uniform shrinking theorem, including auxiliary arrangement walls.
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

local instance normalSliceTestDerivedScalar : HasDerivedCategory.{1} (ModuleCat.{0} ℂ) :=
  HasDerivedCategory.standard _
local instance normalSliceTestDerivedUniversal :
    HasDerivedCategory.{1} (UniversalIncidenceObject A ⥤ ModuleCat.{0} ℂ) := HasDerivedCategory.standard _

/-- Genuine complete-cone closed-subtorus tests give every scalar test
required by the target-independent uniform detection theorem. -/
theorem normal_scalar_slice_tests_of_closed_rows
    (complete : fan.IsComplete) (b : fan.Ray → ℤ)
    (tests : ∀ σ : fan.cones,
      Submodule.span ℝ (σ.val : Set V) ∈ fanCompleteSubspaces fan →
        NormalizedClosedRowsTest fan regular basis rays b (fanConeSliceRows fan rays σ)) :
    ∀ c : NormalCoveredNormalizedCell fan regular basis rays,
      ∃ m : Fin n → ℤ, NormalizedScalarSliceTest fan regular basis rays b c m := by
  intro c
  let lifted := normalizedUniversalCell A c.val
  let W := universalCellFanNormal fan basis rays lifted
  have completeW : W ∈ fanCompleteSubspaces fan :=
    universalCellFanNormal_complete_of_cover fan basis rays regular lifted c.property
  obtain ⟨σ,member,_,spans⟩ := fanCompleteSubspaces_exists_cone_span fan completeW
  let cone : fan.cones := ⟨σ,member⟩
  have completeCone : Submodule.span ℝ (cone.val : Set V) ∈ fanCompleteSubspaces fan := by
    rw [spans]
    exact completeW
  obtain ⟨m,q,f,hf⟩ := exists_normalized_affine_slice_test_of_closed_rows
    fan regular basis rays complete b (fanConeSliceRows fan rays cone)
    (fun cell active => fanConeSlice_integralComponents fan regular basis rays cone cell active)
    (tests cone completeCone)
  have sameZero : arrangementZeroSlice (augmentedForms A) (fanConeSliceRows fan rays cone) =
      arrangementZeroSlice (augmentedForms A) lifted.2.val.2 :=
    (fanCharacterAnnihilator_eq_zeroSlice fan basis rays cone W spans).symm.trans
      (universalCellFanNormal_annihilator fan basis rays lifted)
  have sameSupport : ∀ d : UniversalIncidenceObject A,
      universalAffineSliceSupport A lifted.2.val.2 m d ↔
        universalAffineSliceSupport A (fanConeSliceRows fan rays cone) m d := by
    intro d
    unfold universalAffineSliceSupport arrangementAffineSlice
    rw [sameZero]
  let frame := (exactDerivedFunctorIso (Cellular.closedConstantCongrIso ℂ
    (universalAffineSliceSupport A lifted.2.val.2 m)
    (universalAffineSliceSupport A (fanConeSliceRows fan rays cone) m)
    (universalAffineSliceSupport_downward A lifted.2.val.2 m)
    (universalAffineSliceSupport_downward A (fanConeSliceRows fan rays cone) m)
    sameSupport)).app ((DerivedCategory.singleFunctor (ModuleCat.{0} ℂ) 0).obj (ModuleCat.of ℂ ℂ))
  refine ⟨m,q,frame.hom ≫ f,?_⟩
  intro zero
  apply hf
  rw [← cancel_epi frame.hom,comp_zero]
  exact zero

end ToricPower

end
