module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # The rank-one fibre criterion in a local ring -/

@[expose] public section
set_option autoImplicit false

namespace Unimodular.Syzygies

variable {R M : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M]

/-- A scalar multiple of a vector nonzero in the residue fibre remains
nonzero there exactly when the scalar is a unit. -/
theorem smul_not_mem_maximalIdeal_smul_iff
    {g : M}
    (hg : g ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (a : R) :
    a • g ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ IsUnit a := by
  constructor
  · intro h
    by_contra ha
    exact h (Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal a).mpr ha)
      Submodule.mem_top)
  · rintro ⟨u, rfl⟩ h
    apply hg
    have h' := Submodule.smul_mem
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (↑u⁻¹ : R) h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h'

end Unimodular.Syzygies

#print axioms Unimodular.Syzygies.smul_not_mem_maximalIdeal_smul_iff
