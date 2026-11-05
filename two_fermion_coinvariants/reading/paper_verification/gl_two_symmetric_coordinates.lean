module

public import TauCeti.RepresentationTheory.SU2.Irreducible
public import Mathlib.Tactic.NormNum

/-!
# Binary symmetric powers from the pinned SU(2) formalization

Tau Ceti proves irreducibility for the actual restriction of the standard
GL₂ symmetric-power representation to SU(2). A subrepresentation of GL₂
is also invariant under this subgroup, so the same theorem gives the
irreducibility needed here. No rationality or equivalence is assumed.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.GLTwoSymmetricCoordinates

abbrev Space (F : Type) [Field F] (n : ℕ) := Sym[F]^n (Fin 2 → F)

/-- Irreducibility of any restriction implies that of the original action.
The underlying invariant submodules are literally unchanged. -/
theorem irreducible_of_restriction {F G H V : Type*} [Field F]
    [Monoid G] [Monoid H] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (f : H →* G)
    (h : Representation.IsIrreducible (ρ.comp f)) :
    Representation.IsIrreducible ρ := by
  letI : Representation.IsIrreducible (ρ.comp f) := h
  letI : Nontrivial V := h.nontrivial
  refine ⟨fun S ↦ ?_⟩
  let S' : Subrepresentation (ρ.comp f) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g v hv ↦ S.apply_mem_toSubmodule (f g) hv }
  rcases eq_bot_or_eq_top S' with hS | hS
  · left
    apply Subrepresentation.toSubmodule_injective
    change S'.toSubmodule = _
    simp only [hS,Subrepresentation.toSubmodule_bot]
  · right
    apply Subrepresentation.toSubmodule_injective
    change S'.toSubmodule = _
    simp only [hS,Subrepresentation.toSubmodule_top]

/-- The actual GL₂(C) action is irreducible in every nonnegative degree. -/
theorem symmetricPower_irreducible (n : ℕ) :
    (TauCeti.symPowerRep ℂ 2 n).IsIrreducible := by
  apply irreducible_of_restriction _ TauCeti.SU2.toGL
  have hrestrict : (TauCeti.symPowerRep ℂ 2 n).comp TauCeti.SU2.toGL =
      TauCeti.SU2.symPower n := by
    apply MonoidHom.ext
    intro g
    exact (TauCeti.SU2.symPower_apply n g).symm
  rw [hrestrict]
  exact TauCeti.SU2.isIrreducible_symPower n

def twoUnit (F : Type) [Field F] [CharZero F] : Fˣ :=
  Units.mk0 2 (by norm_num)

def twoTorus (F : Type) [Field F] [CharZero F] : Fin 2 → Fˣ :=
  ![twoUnit F,1]

end PaperVerification.GLTwoSymmetricCoordinates
