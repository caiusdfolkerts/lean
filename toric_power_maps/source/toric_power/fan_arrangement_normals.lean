module

public import ToricPower.FanIntegralFaces
public import ToricPower.LatticeCharacterCoordinates
public import ToricPower.DiagonalFanLabels
public import ToricPower.ArrangementUniversalCells

/-! # Actual fan vectors in the normal space of an arrangement cell

The normal-coordinate equivalence sends a primitive fan vector to its
literal arrangement row. Thus every ray integral at the cell center is
normal to the entire cell. The integral faces of all fan cones are
contained in the resulting actual subspace of the original lattice space.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A

theorem normalCoordinateEquiv_primitive (ρ : fan.Ray) :
    normalCoordinateEquiv fan.lattice basis (i (fanRayPrimitiveGenerator fan ρ)) =
      augmentedForms A (.inl (rays.symm ρ)) := by
  apply LinearMap.ext
  intro x
  rw [normalCoordinateEquiv_lattice]
  simp only [augmentedForms,Sum.elim_inl,integralRowForm,LinearMap.coe_mk,
    AddHom.coe_mk,fanArrangementMatrix,Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem characterCoordinateEquiv_primitive (x : Fin n → ℝ) (ρ : fan.Ray) :
    characterCoordinateEquiv fan.lattice basis x (i (fanRayPrimitiveGenerator fan ρ)) =
      augmentedForms A (.inl (rays.symm ρ)) x :=
  DFunLike.congr_fun (normalCoordinateEquiv_primitive fan basis rays ρ) x

/-- The normal space is a subspace of the original real lattice space,
transported by genuine finite-dimensional evaluation duality. -/
def universalCellFanNormal (c : U) : Submodule ℝ V :=
  (cellNormal (augmentedForms A) c.2.val.2).comap
    (normalCoordinateEquiv fan.lattice basis).toLinearMap

def universalCellCharacter (c : U) : Module.Dual ℝ V :=
  characterCoordinateEquiv fan.lattice basis (cellCenter (augmentedForms A) c.2)

/-- Every actual primitive ray at an integral level belongs to the
normal space, including cells of arbitrary dimension. -/
theorem integralPrimitive_mem_universalCellFanNormal (c : U) (ρ : fan.Ray)
    (integral : ∃ z : ℤ,
      universalCellCharacter fan basis rays c (i (fanRayPrimitiveGenerator fan ρ)) =
        (z : ℝ)) :
    i (fanRayPrimitiveGenerator fan ρ) ∈ universalCellFanNormal fan basis rays c := by
  obtain ⟨z,hz⟩ := integral
  change characterCoordinateEquiv fan.lattice basis
    (cellCenter (augmentedForms A) c.2) (i (fanRayPrimitiveGenerator fan ρ)) = (z : ℝ) at hz
  rw [characterCoordinateEquiv_primitive] at hz
  have active : Sum.inl (rays.symm ρ) ∈ c.2.val.2 := by
    rw [← cellCenter_integralIndices A c.2]
    change augmentedForms A (.inl (rays.symm ρ)) (cellCenter (augmentedForms A) c.2) =
      (⌈augmentedForms A (.inl (rays.symm ρ)) (cellCenter (augmentedForms A) c.2)⌉ : ℝ)
    rw [hz,Int.ceil_intCast]
  change normalCoordinateEquiv fan.lattice basis
    (i (fanRayPrimitiveGenerator fan ρ)) ∈ cellNormal (augmentedForms A) c.2.val.2
  rw [normalCoordinateEquiv_primitive]
  exact Submodule.subset_span ⟨_,active,rfl⟩

/-- Integral active faces of every cone lie in the normal space; this
containment is proved before asking whether those faces cover it. -/
theorem fanIntegralFace_le_universalCellFanNormal (regular : fan.IsRegular)
    (c : U) (σ : fan.cones) :
    fanIntegralFace fan regular (universalCellCharacter fan basis rays c) σ ≤
      (universalCellFanNormal fan basis rays c : PointedCone ℝ V) := by
  apply fanIntegralFace_le_submodule fan regular (universalCellCharacter fan basis rays c)
  intro ρ integral
  simp only [integralConeRays,Set.mem_setOf_eq] at integral
  have h := integralPrimitive_mem_universalCellFanNormal fan basis rays c
    (Fan.Ray.ofToricRay fan σ ρ)
    (by simpa only [fanRayPrimitiveGenerator_ofToricRay] using integral)
  simpa only [fanRayPrimitiveGenerator_ofToricRay] using h

/-- A normal-direction cover by actual active faces proves the complete
linear-subspace criterion for the original fan. -/
theorem universalCellFanNormal_complete_of_cover (regular : fan.IsRegular) (c : U)
    (cover : ∀ v ∈ universalCellFanNormal fan basis rays c,
      ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
        (universalCellCharacter fan basis rays c) σ) :
    universalCellFanNormal fan basis rays c ∈ fanCompleteSubspaces fan :=
  fanIntegralFace_cover_complete fan regular (universalCellCharacter fan basis rays c)
    (universalCellFanNormal fan basis rays c)
    (fanIntegralFace_le_universalCellFanNormal fan basis rays regular c) cover

/-- The same genuine cover gives an integral translate of the whole
affine annihilator slice, without a full-dimensional original cone. -/
theorem universalCellFanNormal_integralSlice_of_cover (regular : fan.IsRegular) (c : U)
    (cover : ∀ v ∈ universalCellFanNormal fan basis rays c,
      ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
        (universalCellCharacter fan basis rays c) σ) :
    ∃ m : N →+ ℤ, ∀ y : Module.Dual ℝ V,
      y-universalCellCharacter fan basis rays c ∈
          (universalCellFanNormal fan basis rays c).dualAnnihilator ↔
        y-fan.lattice.realCharacter m ∈
          (universalCellFanNormal fan basis rays c).dualAnnihilator :=
  fanIntegralFace_cover_integralSlice fan regular (universalCellCharacter fan basis rays c)
    (universalCellFanNormal fan basis rays c)
    (fanIntegralFace_le_universalCellFanNormal fan basis rays regular c) cover

end ToricPower

end
