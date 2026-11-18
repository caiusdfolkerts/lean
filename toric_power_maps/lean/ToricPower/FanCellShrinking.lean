module

public import ToricPower.FanAnnihilatorLatticeSpan
public import ToricPower.ArrangementShrunkSlice
public import ToricPower.FanArrangementNormals

/-!
# Shrinking into the genuine local star of a fan arrangement cell

Normal coverage supplies both required arithmetic facts: the direction
is spanned by its integral lattice, and the cell lies in an integral
affine translate of that direction. The resulting inverse branch works
for every sufficiently large integer, with the exact affine-slice
compatibility needed by local detection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "U" => UniversalIncidenceObject A

/-- The character annihilator of the actual fan normal space is
exactly the direction of the original cell. -/
theorem universalCellFanNormal_annihilator (c : U) :
    fanCharacterAnnihilator fan basis (universalCellFanNormal fan basis rays c) =
      cellDirection (augmentedForms A) c.2.val.2 := by
  rw [cellDirection_eq_dualCoannihilator]
  apply Submodule.ext
  intro x
  change characterCoordinateEquiv fan.lattice basis x ∈
      (universalCellFanNormal fan basis rays c).dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator,Submodule.mem_dualCoannihilator]
  constructor
  · intro annihilates ξ inside
    obtain ⟨v,rfl⟩ := (normalCoordinateEquiv fan.lattice basis).surjective ξ
    exact annihilates v inside
  · intro annihilates v inside
    exact annihilates (normalCoordinateEquiv fan.lattice basis v) inside

/-- The center belongs to an actual integral translate of its whole
direction space, with no denominator restriction. -/
theorem universalCell_integralTranslate_of_normalCover
    (regular : fan.IsRegular) (c : U)
    (cover : ∀ v ∈ universalCellFanNormal fan basis rays c,
      ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
        (universalCellCharacter fan basis rays c) σ) :
    ∃ v₀ : Fin n → ℤ, cellCenter (augmentedForms A) c.2 - latticeLift v₀ ∈
      cellDirection (augmentedForms A) c.2.val.2 := by
  obtain ⟨m,slice⟩ := universalCellFanNormal_integralSlice_of_cover
    fan basis rays regular c cover
  refine ⟨basis.equivFun m,?_⟩
  rw [← universalCellFanNormal_annihilator fan basis rays c]
  change characterCoordinateEquiv fan.lattice basis
      (cellCenter (augmentedForms A) c.2 - latticeLift (basis.equivFun m)) ∈
        (universalCellFanNormal fan basis rays c).dualAnnihilator
  rw [map_sub,characterCoordinateEquiv_latticeLift fan basis,LinearEquiv.symm_apply_apply]
  apply (slice (universalCellCharacter fan basis rays c)).mp
  rw [sub_self]
  exact Submodule.zero_mem _

/-- Every sufficiently large exponent shrinks the complete bounded
test into the original open star, while preserving its prescribed
integral affine-slice equation. -/
theorem universalCell_shrinking_of_normalCover
    (regular : fan.IsRegular) (c : U)
    (cover : ∀ v ∈ universalCellFanNormal fan basis rays c,
      ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular
        (universalCellCharacter fan basis rays c) σ)
    (m : Fin n → ℤ) (K : Set (Fin n → ℝ)) (bounded : Bornology.IsBounded K) :
    ∃ v₀ : Fin n → ℤ,
      cellCenter (augmentedForms A) c.2 - latticeLift v₀ ∈
        cellDirection (augmentedForms A) c.2.val.2 ∧
      ∃ threshold : ℕ, 0 < threshold ∧ ∀ ell : ℕ, threshold ≤ ell →
        ∃ u : Fin n → ℤ,
          latticeLift u + latticeLift m - (ell : ℝ) • latticeLift v₀ ∈
            cellDirection (augmentedForms A) c.2.val.2 ∧
          ∀ z ∈ K, powerInverseBranchPoint ell u z ∈
            localStar (augmentedForms A) (cellCenter (augmentedForms A) c.2) := by
  obtain ⟨v₀,center⟩ := universalCell_integralTranslate_of_normalCover
    fan basis rays regular c cover
  have spans := fanCharacterAnnihilator_lattice_span fan basis regular
    (universalCellFanNormal fan basis rays c)
    (universalCellFanNormal_complete_of_cover fan basis rays regular c cover)
  rw [universalCellFanNormal_annihilator fan basis rays c] at spans
  obtain ⟨ε,positive,ball⟩ := Metric.isOpen_iff.mp
    (localStar_isOpen (augmentedForms A)
      (fun j => (augmentedForms A j).continuous_of_finiteDimensional)
      (cellCenter (augmentedForms A) c.2))
    _ (mem_localStar_self _ _)
  obtain ⟨threshold,thresholdPositive,shrink⟩ :=
    bounded_test_shrinks_for_every_integer_of_affine_span
      (cellDirection (augmentedForms A) c.2.val.2) (integerLattice n) spans
      (cellCenter (augmentedForms A) c.2) (latticeLift v₀) (integer_cast_mem v₀) center
      (latticeLift m) (integer_cast_mem m) K bounded ε positive
  refine ⟨v₀,center,threshold,thresholdPositive,fun ell large => ?_⟩
  obtain ⟨u,integral,compatible,small⟩ := shrink ell large
  obtain ⟨a,ha⟩ := integral
  have equal : latticeLift a = u := funext ha
  refine ⟨a,?_,?_⟩
  · rwa [equal]
  · intro z hz
    apply ball
    change (ell : ℝ)⁻¹ • (z+latticeLift a) ∈ Metric.ball _ ε
    rw [equal,add_comm z u]
    exact small (Set.mem_image_of_mem _ hz)

end ToricPower

end
