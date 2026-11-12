module

public import ToricPower.ArrangementUniversalTheta
public import ToricPower.ArrangementStrictMorse
public import ToricPower.FanStrictCharacter

/-! # Local Morse vanishing for the actual affine theta summands

Each Laurent character is compared to the literal strict-support face
diagram. A genuine positive integral character of the fan cone supplies
the strict feasibility direction. Thus no interior-direction hypothesis
is added in the toric specialization.
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
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ

variable (cone : fan.cones) (m : N →+ ℤ)

abbrev universalThetaWeight : U ⥤ ModuleCat ℂ :=
  universalThetaFamily fan basis rays cone ⋙
    (evaluation (Discrete (N →+ ℤ)) (ModuleCat ℂ)).obj ⟨m⟩

theorem universalThetaScalarSubmodule_eq (c : U) :
    MorseCoefficients.openScalar ℂ (¬universalChartAllowed fan basis rays cone c m) =
      MorseCoefficients.openScalar ℂ
        (universalStrictClosedPredicate A (universalThetaLower fan rays m)
          (universalThetaSelected fan rays cone) c) := by
  apply Submodule.ext
  intro a
  change ((¬universalChartAllowed fan basis rays cone c m) → a = 0) ↔
    (universalStrictClosedPredicate A (universalThetaLower fan rays m)
      (universalThetaSelected fan rays cone) c → a = 0)
  exact imp_congr (not_congr (universalChartAllowed_iff_strict fan basis rays cone c m)) Iff.rfl

/-- The canonical scalar-preserving identification, natural in every
face incidence of the entire universal arrangement. -/
def universalThetaWeightStrictIso :
    universalThetaWeight fan basis rays cone m ≅
      universalStrictCoefficientDiagram A ℂ (universalThetaLower fan rays m)
        (universalThetaSelected fan rays cone) :=
  NatIso.ofComponents (fun c =>
    (LinearEquiv.ofEq _ _
      (universalThetaScalarSubmodule_eq fan basis rays cone m c)).toModuleIso) (by
      intro c d f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      rfl)

theorem universalTheta_strictDirection :
    ∃ w : E, ∀ j ∈ universalThetaSelected fan rays cone,
      0 < augmentedForms A j w := by
  obtain ⟨character,positive⟩ := fanCone_exists_strictPositive_character fan cone
  refine ⟨latticeLift (basis.equivFun character),?_⟩
  intro j selected
  cases j with
  | inl r =>
      rw [augmentedForms_latticeLift]
      change (0 : ℝ) < (rayPairing A (basis.equivFun character) r : ℝ)
      have value : rayPairing A (basis.equivFun character) r =
          character (fanRayPrimitiveGenerator fan (rays r)) := by
        simpa only [Equiv.symm_apply_apply,LinearEquiv.symm_apply_apply] using
          fanArrangementMatrix_character fan basis rays (basis.equivFun character) (rays r)
      rw [value]
      exact_mod_cast positive (rays r) selected
  | inr r => exact selected.elim

/-- The actual theta summand has zero signed local Morse complex in
every direction outside its negative active fan cone, in all degrees. -/
theorem universalThetaWeight_localMorse_acyclic
    (c : U) (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))
    (outsideCone : -ξ ∉ PointedCone.hull ℝ (Set.range
      (fun j : strictActive (augmentedForms A) (universalThetaLower fan rays m)
        (universalThetaSelected fan rays cone) (cellCenter (augmentedForms A) c.2) =>
          augmentedForms A j.val))) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
        (universalThetaWeight fan basis rays cone m))).Acyclic := by
  obtain ⟨w,positive⟩ := universalTheta_strictDirection fan basis rays cone
  have vanished := universalStrict_localMorse_acyclic_outside_activeCone A ℂ
    (universalThetaLower fan rays m) (universalThetaSelected fan rays cone) c neighborhood ξ
    convex openNeighborhood center inside
    ⟨w,fun j => positive j.val j.property.1⟩ outsideCone
  let comparison := (universalLocalMorse A ℂ c
      (universalNegativeHalf A c neighborhood ξ)).mapIso
    ((CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).mapIso
      (universalThetaWeightStrictIso fan basis rays cone m))
  intro q
  exact (exactAt_iff_of_quasiIsoAt comparison.hom q).mpr (vanished q)

end ToricPower

end
