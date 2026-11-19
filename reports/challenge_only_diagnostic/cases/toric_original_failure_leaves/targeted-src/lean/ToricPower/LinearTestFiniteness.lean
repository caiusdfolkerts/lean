module

public import ToricPower.RestrictedFan
public import ToricPower.FanCompleteSubspaces

/-!
# The complete linear tests and passage to a subfan

This connects the finite cone-span construction to the literal restricted
fans used in the principal statement. Complete tests are proved finite;
finiteness is not included in their definition. It also proves that a linear
subspace for a completion remains linear for the original subfan.

These are intermediate dependencies in Sections 3 and 4. Theorem 1.1 still
tests all rational linear subspaces, including noncomplete restrictions.
This file does not replace that full condition by the complete tests.

Candidate source awaiting ordinary compilation.
-/

@[expose] public noncomputable section

open Set TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The explicit integral spanning set of a complete subfan proves the
literal saturated-trace rationality predicate used in the principal goal. -/
theorem rationalSubspace_of_fanCompleteSubspaces (fan : Fan i)
    {W : Submodule ℝ V} (hW : W ∈ fanCompleteSubspaces fan) :
    IsRationalSubspace i W := by
  obtain ⟨s, hs⟩ := fanCompleteSubspaces_lattice_span fan hW
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    exact n.property
  · conv_lhs => rw [hs]
    apply Submodule.span_le.mpr
    rintro x ⟨n, hn, rfl⟩
    have hnW : i n ∈ W := by
      rw [hs]
      exact Submodule.subset_span ⟨n, hn, rfl⟩
    exact Submodule.subset_span ⟨⟨n, hnW⟩, rfl⟩

/-- Actual completeness of the restricted fan is equivalent to the
explicit cover by cones contained in the subspace. -/
theorem restrictedFan_complete_iff_fanCompleteSubspaces (fan : Fan i)
    (W : Submodule ℝ V) (hW : IsRationalSubspace i W) :
    (restrictedFan fan W hW).IsComplete ↔ W ∈ fanCompleteSubspaces fan := by
  constructor
  · intro hc x hx
    obtain ⟨τ, hτ, hxτ⟩ := (Fan.isComplete_iff _).mp hc (⟨x, hx⟩ : W)
    obtain ⟨σ, ⟨hσ, hσW⟩, rfl⟩ := hτ
    exact ⟨σ, hσ, hσW, hxτ⟩
  · intro hc
    apply (Fan.isComplete_iff _).mpr
    intro x
    obtain ⟨σ, hσ, hσW, hx⟩ := hc x.val x.property
    exact ⟨σ.comap W.subtype, ⟨σ, ⟨hσ, hσW⟩, rfl⟩, hx⟩

/-- The complete subspace gives an actual rational linear test. -/
def linearSubspaceOfCompleteCover (fan : Fan i) (W : Submodule ℝ V)
    (hW : W ∈ fanCompleteSubspaces fan) : LinearSubspace fan where
  space := W
  rational := rationalSubspace_of_fanCompleteSubspaces fan hW
  linear := fanCompleteSubspaces_linear fan hW

theorem LinearSubspace.space_injective (fan : Fan i) :
    Function.Injective (LinearSubspace.space (Φ := fan)) := by
  intro W₁ W₂ h
  cases W₁
  cases W₂
  cases h
  rfl

/-- Exactly the complete members of the original family of linear tests. -/
def completeLinearTests (fan : Fan i) : Set (LinearSubspace fan) :=
  {W | (restrictedFan fan W.space W.rational).IsComplete}

/-- Completeness gives a finite family of actual linear tests. -/
theorem completeLinearTests_finite (fan : Fan i) : (completeLinearTests fan).Finite := by
  have himage : (LinearSubspace.space '' completeLinearTests fan).Finite := by
    apply (fanCompleteSubspaces_finite fan).subset
    rintro W ⟨L, hL, rfl⟩
    exact (restrictedFan_complete_iff_fanCompleteSubspaces fan L.space L.rational).mp hL
  exact himage.of_finite_image (LinearSubspace.space_injective fan).injOn

/-- A linear subspace for a larger fan is linear for every subfan: the
intersection cone is a face of the original cone and is therefore retained. -/
theorem isLinearSubspace_of_cones_subset {fan completion : Fan i}
    (hsub : fan.cones ⊆ completion.cones) {W : Submodule ℝ V}
    (hW : IsLinearSubspace completion W) : IsLinearSubspace fan W := by
  intro σ hσ
  exact fan.mem_of_isFaceOf hσ
    (completion.isFaceOf_of_le (hsub hσ) (hW σ (hsub hσ)) inf_le_left)

/-- The complete-fan linear test has its literal restriction to the
original fan in exactly the same saturated lattice. -/
def linearTestOfSubfan {fan completion : Fan i}
    (hsub : fan.cones ⊆ completion.cones) (W : LinearSubspace completion) :
    LinearSubspace fan where
  space := W.space
  rational := W.rational
  linear := isLinearSubspace_of_cones_subset hsub W.linear

end ToricPower

end
