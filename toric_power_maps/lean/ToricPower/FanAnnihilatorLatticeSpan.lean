module

public import ToricPower.RegularConeAnnihilatorLattice
public import ToricPower.ToricClosedSubtorusSupport
public import ToricPower.Core

/-!
# Lattice approximation in the actual character-coordinate slice

The integral dual-basis calculation is transported through the full
character-coordinate equivalence. Thus the exact integer lattice used
by the covering maps spans every complete fan annihilator, including
the zero-dimensional and full-dimensional cases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Module TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n : ℕ} (basis : Basis (Fin n) ℤ (N →+ ℤ))

/-- In character coordinates, the integral points of the complete
annihilator span the entire annihilator over the reals. -/
theorem fanConeCharacterAnnihilator_lattice_span
    (regular : fan.IsRegular) (σ : fan.cones)
    (W : Submodule ℝ V) (spans : Submodule.span ℝ (σ.val : Set V) = W) :
    Submodule.span ℝ
      ((integerLattice n).comap
        (fanCharacterAnnihilator fan basis W).subtype.toAddMonoidHom :
          Set (fanCharacterAnnihilator fan basis W)) = ⊤ := by
  let e := characterCoordinateEquiv fan.lattice basis
  let S := fanCharacterAnnihilator fan basis W
  have image : e '' ((integerLattice n : Set (Fin n → ℝ)) ∩ (S : Set (Fin n → ℝ))) =
      (Set.range fan.lattice.realCharacter) ∩ (W.dualAnnihilator : Set (Module.Dual ℝ V)) := by
    ext y
    constructor
    · rintro ⟨x,⟨integral,inside⟩,rfl⟩
      obtain ⟨a,ha⟩ := integral
      have equal : latticeLift a = x := funext ha
      refine ⟨⟨basis.equivFun.symm a,?_⟩,inside⟩
      rw [← equal]
      exact (characterCoordinateEquiv_latticeLift fan basis a).symm
    · rintro ⟨⟨m,rfl⟩,inside⟩
      have equal : e (latticeLift (basis.equivFun m)) = fan.lattice.realCharacter m := by
        rw [characterCoordinateEquiv_latticeLift fan basis,LinearEquiv.symm_apply_apply]
      refine ⟨latticeLift (basis.equivFun m),⟨integer_cast_mem _,?_⟩,equal⟩
      change e (latticeLift (basis.equivFun m)) ∈ W.dualAnnihilator
      rwa [equal]
  have ambient : Submodule.span ℝ
      ((integerLattice n : Set (Fin n → ℝ)) ∩ (S : Set (Fin n → ℝ))) = S := by
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    change Submodule.span ℝ (e '' ((integerLattice n : Set (Fin n → ℝ)) ∩
      (S : Set (Fin n → ℝ)))) = Submodule.map e.toLinearMap S
    rw [image]
    have span := regularCone_annihilator_integral_span fan.lattice
      (regularFanCone fan regular σ)
    rw [spans] at span
    rw [span]
    change W.dualAnnihilator =
      (W.dualAnnihilator.comap e.toLinearMap).map e.toLinearMap
    rw [Submodule.map_comap_eq,LinearEquiv.range,top_inf_eq]
  apply (Submodule.span_val_image_eq_iff S
    ((integerLattice n).comap S.subtype.toAddMonoidHom : Set S)).mp
  have imageSubtype : Subtype.val ''
      ((integerLattice n).comap S.subtype.toAddMonoidHom : Set S) =
        (integerLattice n : Set (Fin n → ℝ)) ∩ (S : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨integral,inside⟩
      exact ⟨⟨x,inside⟩,integral,rfl⟩
  rw [imageSubtype]
  exact ambient

/-- Completeness of the subfan provides the spanning cone, so no
additional rationality hypothesis is imposed on the paper's test spaces. -/
theorem fanCharacterAnnihilator_lattice_span (regular : fan.IsRegular)
    (W : Submodule ℝ V) (complete : W ∈ fanCompleteSubspaces fan) :
    Submodule.span ℝ
      ((integerLattice n).comap
        (fanCharacterAnnihilator fan basis W).subtype.toAddMonoidHom :
          Set (fanCharacterAnnihilator fan basis W)) = ⊤ := by
  obtain ⟨σ,member,_,spans⟩ := fanCompleteSubspaces_exists_cone_span fan complete
  exact fanConeCharacterAnnihilator_lattice_span fan basis regular ⟨σ,member⟩ W spans

end ToricPower

end
