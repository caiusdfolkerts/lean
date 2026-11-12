module

public import ToricPower.ArrangementUniversalThetaMorse
public import ToricPower.ArrangementMorseSumVanishing
public import ToricPower.FanArrangementNormals

/-! # Genuine fan directions for the unrestricted affine theta sum

Every active strict inequality is an original primitive ray at an
integral level. Its cone lies in the actual integral face of the chosen
smooth fan cone. The local Morse calculation consequently applies to
the complete affine Cartier-section diagram, with every lattice
character and every incidence map retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric Set
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A
local notation "E" => Fin n → ℝ

variable (regular : fan.IsRegular) (cone : fan.cones)
  (c : UniversalIncidenceObject (fanArrangementMatrix fan basis rays))

/-- The full active cone of every character is contained in the same
genuine fan face selected by integrality at the cell center. -/
theorem universalThetaActiveCone_le_integralFace (m : N →+ ℤ) :
    PointedCone.hull ℝ (Set.range
      (fun j : strictActive (augmentedForms A) (universalThetaLower fan rays m)
        (universalThetaSelected fan rays cone) (cellCenter (augmentedForms A) c.2) =>
          augmentedForms A j.val)) ≤
      (fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone).comap
        (normalCoordinateEquiv fan.lattice basis).symm.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  rcases j with ⟨j,selected,active⟩
  cases j with
  | inr r => exact selected.elim
  | inl r =>
      let ρ := Fan.Ray.toToricRay fan (rays r) cone selected
      have same : Fan.Ray.ofToricRay fan cone ρ = rays r := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      have primitive : primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ =
          fanRayPrimitiveGenerator fan (rays r) := by
        rw [← fanRayPrimitiveGenerator_ofToricRay,same]
      have integral : ρ ∈ integralConeRays fan
          (universalCellCharacter fan basis rays c) cone := by
        refine ⟨-m (fanRayPrimitiveGenerator fan (rays r)),?_⟩
        rw [primitive]
        change characterCoordinateEquiv fan.lattice basis
          (cellCenter (augmentedForms A) c.2)
          (i (fanRayPrimitiveGenerator fan (rays r))) = _
        rw [characterCoordinateEquiv_primitive fan basis rays,
          Equiv.symm_apply_apply]
        exact active
      change (normalCoordinateEquiv fan.lattice basis).symm
        (augmentedForms A (.inl r)) ∈
          fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone
      have row : augmentedForms A (.inl r) =
          normalCoordinateEquiv fan.lattice basis (i (fanRayPrimitiveGenerator fan (rays r))) := by
        simpa only [Equiv.symm_apply_apply] using
          (normalCoordinateEquiv_primitive fan basis rays (rays r)).symm
      rw [row,LinearEquiv.symm_apply_apply]
      change i (fanRayPrimitiveGenerator fan (rays r)) ∈ PointedCone.hull ℝ _
      exact PointedCone.subset_hull ⟨ρ,integral,congrArg i primitive⟩

/-- The actual categorical coproduct, with the full character family,
is the whole actual affine-section diagram. -/
def universalThetaCoproductActualIso [Nonempty fan.cones] :
    (∐ fun m : N →+ ℤ => universalThetaWeight fan basis rays cone m) ≅
      universalCartierChartSections fan basis rays cone regular :=
  HasColimit.isoOfNatIso
      (show Discrete.functor (fun m => universalThetaWeight fan basis rays cone m) ≅
          (universalThetaFamily fan basis rays cone).flip from
        Discrete.natIso (fun _ => Iso.refl _)) ≪≫
    colimitFlipIsoCompColim (universalThetaFamily fan basis rays cone) ≪≫
    Functor.isoWhiskerLeft (universalThetaFamily fan basis rays cone)
      (ModuleDirectSum.sumFunctorIsoColim ℂ).symm ≪≫
    universalThetaSumActualIso fan basis rays cone regular

def universalThetaSingleCoproductActualIso [Nonempty fan.cones] :
    (∐ fun m : N →+ ℤ =>
      (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
        (universalThetaWeight fan basis rays cone m)) ≅
      (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
        (universalCartierChartSections fan basis rays cone regular) :=
  HasColimit.isoOfNatIso
      (show Discrete.functor (fun m =>
          (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
            (universalThetaWeight fan basis rays cone m)) ≅
          Discrete.functor (fun m => universalThetaWeight fan basis rays cone m) ⋙
            CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0 from
        Discrete.natIso (fun _ => Iso.refl _)) ≪≫
    (preservesColimitIso (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0)
      (Discrete.functor (fun m => universalThetaWeight fan basis rays cone m))).symm ≪≫
    (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).mapIso
      (universalThetaCoproductActualIso fan basis rays regular cone)

/-- No character cutoff is used: the true affine-section diagram has
acyclic local Morse fiber in every direction outside the actual active
fan face. -/
theorem universalCartierChartSections_localMorse_acyclic [Nonempty fan.cones]
    (neighborhood : Set E) (ξ : Module.Dual ℝ E)
    (convex : Convex ℝ neighborhood) (openNeighborhood : IsOpen neighborhood)
    (center : cellCenter (augmentedForms A) c.2 ∈ neighborhood)
    (inside : neighborhood ⊆
      localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2))
    (outside : (normalCoordinateEquiv fan.lattice basis).symm (-ξ) ∉
      fanIntegralFace fan regular (universalCellCharacter fan basis rays c) cone) :
    ((universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).obj
      ((CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
        (universalCartierChartSections fan basis rays cone regular))).Acyclic := by
  have every (m : N →+ ℤ) := universalThetaWeight_localMorse_acyclic
    fan basis rays cone m c neighborhood ξ convex openNeighborhood center inside
    (fun h => outside (universalThetaActiveCone_le_integralFace
      fan basis rays regular cone c m h))
  have vanishes := universalLocalMorse_coproduct_acyclic A ℂ c
    (universalNegativeHalf A c neighborhood ξ)
    (fun m => (CochainComplex.singleFunctor (U ⥤ ModuleCat ℂ) 0).obj
      (universalThetaWeight fan basis rays cone m)) every
  let e := (universalLocalMorse A ℂ c (universalNegativeHalf A c neighborhood ξ)).mapIso
    (universalThetaSingleCoproductActualIso fan basis rays regular cone)
  intro q
  exact (exactAt_iff_of_quasiIsoAt e.hom q).mp (vanishes q)

end ToricPower

end
