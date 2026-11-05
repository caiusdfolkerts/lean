module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Multiplication and the Frobenius pairing on a principal colon quotient

The multiplication map from `A/(J : g)` into `A/J` is defined on the actual
quotient and proved injective. If `ε(ab)` separates points of `A/J`, the form
`ε(gab)` separates points of `A/(J : g)`. Over a field, finiteness then makes
this form a perfect pairing. These are the colon-pairing steps used in Sections
5 and 6; this file does not assume that any moment quotient is Frobenius.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The principal colon appearing in the paper, using Mathlib's literal colon ideal. -/
def principalColon (J : Ideal A) (g : A) : Ideal A := J.colon ({g} : Set A)

@[simp]
theorem mem_principalColon (J : Ideal A) (g a : A) :
    a ∈ principalColon J g ↔ a * g ∈ J :=
  Submodule.mem_colon_singleton

theorem le_principalColon (J : Ideal A) (g : A) : J ≤ principalColon J g := by
  intro a ha
  exact (mem_principalColon J g a).mpr (J.mul_mem_right g ha)

/-- Multiplication by `g`, followed by the ordinary quotient map. -/
def multiplyIntoQuotient (J : Ideal A) (g : A) : A →ₗ[K] A ⧸ J :=
  (Ideal.Quotient.mkₐ K J).toLinearMap.comp (LinearMap.mul K A g)

@[simp]
theorem multiplyIntoQuotient_apply (J : Ideal A) (g a : A) :
    multiplyIntoQuotient (K := K) J g a = Ideal.Quotient.mk J (g * a) := rfl

theorem multiplyIntoQuotient_ker (J : Ideal A) (g : A) :
    (multiplyIntoQuotient (K := K) J g).ker = (principalColon J g).restrictScalars K := by
  ext a
  simp only [LinearMap.mem_ker, multiplyIntoQuotient_apply,
    Ideal.Quotient.eq_zero_iff_mem, Submodule.restrictScalars_mem, mem_principalColon,
    mul_comm g a]

/-- The faithful multiplication map `A/(J:g) → A/J`. -/
def colonMultiplication (J : Ideal A) (g : A) : A ⧸ principalColon J g →ₗ[K] A ⧸ J :=
  ((principalColon J g).restrictScalars K).liftQ
    (multiplyIntoQuotient (K := K) J g)
    (by rw [multiplyIntoQuotient_ker])

@[simp]
theorem colonMultiplication_mk (J : Ideal A) (g a : A) :
    colonMultiplication (K := K) J g (Ideal.Quotient.mk (principalColon J g) a) =
      Ideal.Quotient.mk J (g * a) := rfl

theorem colonMultiplication_injective (J : Ideal A) (g : A) :
    Function.Injective (colonMultiplication (K := K) J g) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [multiplyIntoQuotient_ker]

/-- A principal colon quotient is finite whenever the original quotient is finite.
This uses the surjection from `A/J`, and therefore works over arbitrary base rings. -/
theorem finite_principalColon (J : Ideal A) (g : A) [Module.Finite K (A ⧸ J)] :
    Module.Finite K (A ⧸ principalColon J g) :=
  Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ K (le_principalColon J g)).toLinearMap
    (Ideal.Quotient.factor_surjective (le_principalColon J g))

/-- The unreduced bilinear form `ε(gab)`. -/
def colonPrePairing (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) :
    A →ₗ[K] A →ₗ[K] K where
  toFun a :=
    { toFun := fun b ↦ ε ((Ideal.Quotient.mkₐ K J) (g * a * b))
      map_add' b c := by simp [mul_add]
      map_smul' r b := by simp [mul_smul_comm] }
  map_add' a b := by
    ext c
    simp [mul_add, add_mul]
  map_smul' r a := by
    ext b
    simp [mul_smul_comm, smul_mul_assoc]

@[simp]
theorem colonPrePairing_apply (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) (a b : A) :
    colonPrePairing J g ε a b = ε (Ideal.Quotient.mk J (g * a * b)) := rfl

theorem principalColon_le_pairing_ker (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) :
    (principalColon J g).restrictScalars K ≤ (colonPrePairing J g ε).ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  change ε (Ideal.Quotient.mk J (g * a * b)) = 0
  have hga : g * a ∈ J := by simpa only [mul_comm] using (mem_principalColon J g a).mp ha
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right b hga), map_zero]

theorem principalColon_le_pairing_flip_ker (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) :
    (principalColon J g).restrictScalars K ≤ (colonPrePairing J g ε).flip.ker := by
  intro a ha
  apply LinearMap.ext
  intro b
  change ε (Ideal.Quotient.mk J (g * b * a)) = 0
  have hga : g * a ∈ J := by simpa only [mul_comm] using (mem_principalColon J g a).mp ha
  have hgba : g * b * a ∈ J := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using J.mul_mem_right b hga
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hgba, map_zero]

/-- The actual descended form `([a],[b]) ↦ ε([gab])` on the principal colon quotient. -/
def colonPairing (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) :
    A ⧸ principalColon J g →ₗ[K] A ⧸ principalColon J g →ₗ[K] K :=
  (colonPrePairing J g ε).liftQ₂
    ((principalColon J g).restrictScalars K) ((principalColon J g).restrictScalars K)
    (principalColon_le_pairing_ker J g ε) (principalColon_le_pairing_flip_ker J g ε)

@[simp]
theorem colonPairing_mk (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K) (a b : A) :
    colonPairing J g ε (Ideal.Quotient.mk (principalColon J g) a)
      (Ideal.Quotient.mk (principalColon J g) b) =
      ε (Ideal.Quotient.mk J (g * a * b)) := rfl

theorem colonPairing_symm (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K)
    (a b : A ⧸ principalColon J g) : colonPairing J g ε a b = colonPairing J g ε b a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [colonPairing_mk, mul_assoc, mul_comm a b]

/-- The colon pairing separates points whenever the ordinary Frobenius form does. -/
theorem colonPairing_separating (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[K] K)
    (hε : ∀ a : A ⧸ J, (∀ b : A ⧸ J, ε (a * b) = 0) → a = 0)
    (a : A ⧸ principalColon J g)
    (ha : ∀ b : A ⧸ principalColon J g, colonPairing J g ε a b = 0) : a = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_principalColon J g a).mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hε
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h := ha (Ideal.Quotient.mk (principalColon J g) b)
  simpa only [colonPairing_mk, ← map_mul, mul_comm a g] using h

section Field

variable {F : Type*} [Field F] [Algebra F A]

set_option maxHeartbeats 800000 in
/-- The colon form is perfect over a field as soon as the ordinary finite quotient
has a Frobenius functional. Every hypothesis concerns the actual original quotient. -/
theorem colonPairing_isPerfPair (J : Ideal A) (g : A) (ε : A ⧸ J →ₗ[F] F)
    [Module.Finite F (A ⧸ J)]
    (hε : ∀ a : A ⧸ J, (∀ b : A ⧸ J, ε (a * b) = 0) → a = 0) :
    (colonPairing J g ε).IsPerfPair := by
  letI := finite_principalColon (K := F) J g
  have hinj : Function.Injective (colonPairing J g ε) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    apply colonPairing_separating J g ε hε a
    intro b
    exact LinearMap.congr_fun ha b
  have hflip : (colonPairing J g ε).flip = colonPairing J g ε := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact colonPairing_symm (K := F) J g ε b a
  apply LinearMap.IsPerfPair.of_injective hinj
  rwa [hflip]

end Field

end PaperVerification.Fermion
