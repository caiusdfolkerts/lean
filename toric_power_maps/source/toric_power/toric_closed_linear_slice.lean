module

public import ToricPower.ArrangementClosedLinearSlice
public import ToricPower.FanArrangementNormals

/-! # Complete linear fan slices use the original arrangement cells

The annihilator of the span of an actual fan cone is cut out by the
zero equations of that cone's primitive rays. Thus every complete
linear subspace supplies a closed slice already adapted to the original
integral arrangement, including its auxiliary coordinate hyperplanes.
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

def fanConeSliceRows (σ : fan.cones) : Set (Fin s ⊕ Fin n) :=
  Set.range (fun ρ : ToricRay σ.val => Sum.inl (rays.symm (Fan.Ray.ofToricRay fan σ ρ)))

def fanCharacterAnnihilator (W : Submodule ℝ V) : Submodule ℝ (Fin n → ℝ) :=
  W.dualAnnihilator.comap (characterCoordinateEquiv fan.lattice basis).toLinearMap

theorem fanCharacterAnnihilator_eq_zeroSlice (σ : fan.cones)
    (W : Submodule ℝ V) (spans : Submodule.span ℝ (σ.val : Set V) = W) :
    fanCharacterAnnihilator fan basis W =
      arrangementZeroSlice (augmentedForms A) (fanConeSliceRows fan rays σ) := by
  apply Submodule.ext
  intro x
  change characterCoordinateEquiv fan.lattice basis x ∈ W.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator,mem_arrangementZeroSlice]
  constructor
  · intro annihilates j selected
    obtain ⟨ρ,rfl⟩ := selected
    have inside : i (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ) ∈ W := by
      rw [← spans]
      exact Submodule.subset_span
        (ρ.val.isFaceOf.le (primitiveGenerator_mem fan.lattice (fan.isToricCone σ.property) ρ))
    have zero := annihilates _ inside
    rw [← characterCoordinateEquiv_primitive fan basis rays]
    simpa only [fanRayPrimitiveGenerator_ofToricRay] using zero
  · intro vanishes
    have generators : i '' Set.range (primitiveGenerator fan.lattice (fan.isToricCone σ.property)) ⊆
        (LinearMap.ker (characterCoordinateEquiv fan.lattice basis x) : Set V) := by
      rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
      change characterCoordinateEquiv fan.lattice basis x
        (i (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ)) = 0
      have zero := vanishes _ (Set.mem_range_self ρ)
      rw [← characterCoordinateEquiv_primitive fan basis rays] at zero
      simpa only [fanRayPrimitiveGenerator_ofToricRay] using zero
    have cone : σ.val ≤ PointedCone.ofSubmodule
        (LinearMap.ker (characterCoordinateEquiv fan.lattice basis x)) := by
      rw [← (fan.isToricCone σ.property).hull_primitiveGenerator fan.lattice]
      exact Submodule.span_le.mpr generators
    have span : W ≤ LinearMap.ker (characterCoordinateEquiv fan.lattice basis x) := by
      rw [← spans]
      exact Submodule.span_le.mpr cone
    exact fun v hv => span hv

/-- Completeness of the actual subfan produces the adapted zero-row
presentation; no additional arrangement-adaptedness premise is supplied. -/
theorem fanCharacterAnnihilator_adapted (W : Submodule ℝ V)
    (complete : W ∈ fanCompleteSubspaces fan) :
    ∃ σ : fan.cones,
      fanCharacterAnnihilator fan basis W =
        arrangementZeroSlice (augmentedForms A) (fanConeSliceRows fan rays σ) := by
  obtain ⟨σ,member,_,spans⟩ := fanCompleteSubspaces_exists_cone_span fan complete
  exact ⟨⟨σ,member⟩,fanCharacterAnnihilator_eq_zeroSlice fan basis rays ⟨σ,member⟩ W spans⟩

/-- Its entire closed support is the union of the actual closed cells
contained in the slice. This is the geometric support for the constant
closed-slice coefficient object. -/
theorem fanCharacterAnnihilator_union_cells (W : Submodule ℝ V)
    (complete : W ∈ fanCompleteSubspaces fan) :
    (⋃ c : {c : UniversalIncidenceObject A //
      universalIncidenceClosedCell A c ⊆ fanCharacterAnnihilator fan basis W},
        universalIncidenceClosedCell A c.val) =
      (fanCharacterAnnihilator fan basis W : Set (Fin n → ℝ)) := by
  obtain ⟨σ,equal⟩ := fanCharacterAnnihilator_adapted fan basis rays W complete
  rw [equal]
  exact universalZeroSlice_union A (fanConeSliceRows fan rays σ)

end ToricPower

end
