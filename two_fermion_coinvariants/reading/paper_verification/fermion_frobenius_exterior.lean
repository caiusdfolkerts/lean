module

public import PaperVerification.FermionHarmonicPairing
public import PaperVerification.FermionSoclePairing
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The genuine Frobenius dual of the finite exterior coefficient module

Composing the ordinary Frobenius functional with the actual exterior
coordinate pairing gives a perfect pairing over the coefficient field.
Separation is proved by testing one exterior basis coefficient at a time.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {K A V I : Type*} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    [Fintype I] [LinearOrder I]
variable (b : Module.Basis I A V)

local notation "E" => ExteriorAlgebra A V

theorem coefficientPairing_symm (x y : E) : coefficientPairing b x y = coefficientPairing b y x := by
  have hh : (coefficientPairing b).flip = coefficientPairing b := by
    apply LinearMap.ext_basis b.ExteriorAlgebra b.ExteriorAlgebra
    intro S T
    simp only [LinearMap.flip_apply, coefficientPairing_basis_left,
      Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
  exact (LinearMap.congr_fun₂ hh x y).symm

def exteriorFrobeniusPairing (ε : A →ₗ[K] K) : E →ₗ[K] E →ₗ[K] K :=
  ((coefficientPairing b).restrictScalars₁₂ K K).compr₂ ε

@[simp] theorem exteriorFrobeniusPairing_apply (ε : A →ₗ[K] K) (x y : E) :
    exteriorFrobeniusPairing b ε x y = ε (coefficientPairing b x y) := rfl

theorem exteriorFrobeniusPairing_symm (ε : A →ₗ[K] K) (x y : E) :
    exteriorFrobeniusPairing b ε x y = exteriorFrobeniusPairing b ε y x := by
  rw [exteriorFrobeniusPairing_apply, exteriorFrobeniusPairing_apply, coefficientPairing_symm]

theorem exteriorFrobeniusPairing_separatingRight (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0) :
    (exteriorFrobeniusPairing b ε).SeparatingRight := by
  intro w hw
  apply b.ExteriorAlgebra.repr.injective
  ext T
  rw [map_zero, Finsupp.zero_apply]
  apply hε
  intro a
  have hh := hw (a • b.ExteriorAlgebra T)
  simpa only [exteriorFrobeniusPairing_apply, map_smul, LinearMap.smul_apply,
    coefficientPairing_basis_left, smul_eq_mul, mul_comm] using hh

theorem exteriorFrobeniusPairing_separatingLeft (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0) :
    (exteriorFrobeniusPairing b ε).SeparatingLeft := by
  intro w hw
  apply exteriorFrobeniusPairing_separatingRight b ε hε w
  intro x
  rw [exteriorFrobeniusPairing_symm]
  exact hw x

theorem exteriorFrobeniusPairing_isPerfPair [Module.Finite K A]
    (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0) :
    (exteriorFrobeniusPairing b ε).IsPerfPair := by
  letI : Module.Finite A E := Module.Finite.of_basis b.ExteriorAlgebra
  letI : Module.Finite K E := Module.Finite.trans A E
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (exteriorFrobeniusPairing_separatingLeft b ε hε)
  · apply LinearMap.ker_eq_bot.mp
    exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (exteriorFrobeniusPairing_separatingRight b ε hε)

/-- The second argument represents the functional in the first argument. -/
def exteriorFrobeniusDual [Module.Finite K A] (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0) : E ≃ₗ[K] Module.Dual K E := by
  letI := exteriorFrobeniusPairing_isPerfPair b ε hε
  exact (exteriorFrobeniusPairing b ε).flip.toPerfPair

@[simp] theorem exteriorFrobeniusDual_apply [Module.Finite K A] (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0) (w x : E) :
    exteriorFrobeniusDual b ε hε w x = ε (coefficientPairing b x w) := rfl

theorem exteriorFrobeniusDual_symm_apply [Module.Finite K A] (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ c : A, ε (a * c) = 0) → a = 0)
    (f : Module.Dual K E) (x : E) :
    ε (coefficientPairing b x ((exteriorFrobeniusDual b ε hε).symm f)) = f x := by
  have hh := congrArg (fun g : Module.Dual K E ↦ g x)
    ((exteriorFrobeniusDual b ε hε).apply_symm_apply f)
  exact hh

end PaperVerification.Fermion.Exterior
