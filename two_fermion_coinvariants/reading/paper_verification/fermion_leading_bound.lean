module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega

/-!
# The finite-dimensional largest-coefficient bound

A subspace is filtered by its ordered coefficient blocks. Rank-nullity gives
the sum of the bounds on its actual leading-coordinate images. The second
part bounds a coefficient annihilator by the actual endpoint quotient, using
the ordinary Frobenius pairing and an explicit injective dual map.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section OrderedCoefficients

variable {K W A I : Type*} [Field K]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    [LinearOrder I]

/-- A finite ordered family of coordinates bounds a subspace by its actual
leading-coordinate constraints. No independence of those coordinates or
unproved direct-sum decomposition is assumed: separation is explicit. -/
theorem finrank_le_sum_leading_constraints
    (f : I → W →ₗ[K] A) (B : I → Submodule K A) (S : Finset I) (H : Submodule K W)
    (hsupport : ∀ w ∈ H, ∀ i ∉ S, f i w = 0)
    (hseparate : ∀ w ∈ H, (∀ i, f i w = 0) → w = 0)
    (hleading : ∀ i ∈ S, ∀ w ∈ H, (∀ j, i < j → f j w = 0) → f i w ∈ B i) :
    Module.finrank K H ≤ ∑ i ∈ S, Module.finrank K (B i) := by
  classical
  induction S using Finset.strongInductionOn generalizing H with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · let i := S.max' hS
      have hiS : i ∈ S := Finset.max'_mem S hS
      let H' : Submodule K W := H ⊓ (f i).ker
      have hsupport' : ∀ w ∈ H', ∀ j ∉ S.erase i, f j w = 0 := by
        intro w hw j hj
        by_cases hji : j = i
        · subst j
          exact hw.2
        · exact hsupport w hw.1 j (fun hjS ↦ hj (Finset.mem_erase.mpr ⟨hji, hjS⟩))
      have hseparate' : ∀ w ∈ H', (∀ j, f j w = 0) → w = 0 := by
        intro w hw hz
        exact hseparate w hw.1 hz
      have hleading' : ∀ j ∈ S.erase i, ∀ w ∈ H',
          (∀ l, j < l → f l w = 0) → f j w ∈ B j := by
        intro j hj w hw hzero
        exact hleading j (Finset.mem_erase.mp hj).2 w hw.1 hzero
      have hind := ih (S.erase i) (Finset.erase_ssubset hiS) H' hsupport' hseparate' hleading'
      let g : H →ₗ[K] A := (f i).comp H.subtype
      have hrange : g.range ≤ B i := by
        rintro a ⟨w, rfl⟩
        apply hleading i hiS w w.property
        intro j hij
        apply hsupport w w.property j
        intro hjS
        exact (not_le_of_gt hij) (Finset.le_max' S j hjS)
      let e : g.ker ≃ₗ[K] H' :=
        { toFun := fun w ↦ ⟨w.val.val, w.val.property, w.property⟩
          invFun := fun w ↦ ⟨⟨w.val, w.property.1⟩, w.property.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      have hker : Module.finrank K g.ker = Module.finrank K H' := e.finrank_eq
      have hdim := g.finrank_range_add_finrank_ker
      have himage := Submodule.finrank_mono hrange
      have hsum : (∑ j ∈ S, Module.finrank K (B j)) =
          (∑ j ∈ S.erase i, Module.finrank K (B j)) + Module.finrank K (B i) := by
        exact (Finset.sum_erase_add S (fun j ↦ Module.finrank K (B j)) hiS).symm
      rw [hsum]
      omega
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      have hH : H = ⊥ := by
        apply le_antisymm
        · intro w hw
          change w = 0
          apply hseparate w hw
          intro i
          exact hsupport w hw i (by rw [hS0]; simp)
        · exact bot_le
      rw [hH, hS0]
      simp

end OrderedCoefficients

section CoefficientAnnihilator

variable {K P A : Type*} [Field K] [CommRing P] [CommRing A]
    [Algebra K P] [Algebra K A]

/-- The actual coefficients killed by an ideal acting through a quotient map. -/
def coefficientAnnihilator (q : P →ₐ[K] A) (I : Ideal P) : Submodule K A where
  carrier := {a | ∀ p ∈ I, q p * a = 0}
  zero_mem' := by intro p hp; exact mul_zero _
  add_mem' := by intro a b ha hb p hp; rw [mul_add, ha p hp, hb p hp, add_zero]
  smul_mem' := by intro c a ha p hp; rw [mul_smul_comm, ha p hp, smul_zero]

def annihilatorPreFunctional (q : P →ₐ[K] A) (ε : A →ₗ[K] K) (a : A) : P →ₗ[K] K where
  toFun p := ε (q p * a)
  map_add' p r := by simp only [map_add, add_mul]
  map_smul' c p := by simp only [map_smul, smul_mul_assoc,RingHom.id_apply]

/-- The explicit map into the dual of the literal ideal quotient. -/
def coefficientAnnihilatorToDual (q : P →ₐ[K] A) (I : Ideal P) (ε : A →ₗ[K] K) :
    coefficientAnnihilator q I →ₗ[K] Module.Dual K (P ⧸ I) where
  toFun a := (I.restrictScalars K).liftQ (annihilatorPreFunctional q ε a)
    (by
      intro p hp
      change ε (q p * a.val) = 0
      rw [a.property p hp, map_zero])
  map_add' a b := by
    apply LinearMap.ext
    intro p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    change ε (q p * (a.val + b.val)) = ε (q p * a.val) + ε (q p * b.val)
    rw [mul_add, map_add]
  map_smul' c a := by
    apply LinearMap.ext
    intro p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    change ε (q p * (c • a.val)) = c • ε (q p * a.val)
    rw [mul_smul_comm, map_smul]

@[simp] theorem coefficientAnnihilatorToDual_mk
    (q : P →ₐ[K] A) (I : Ideal P) (ε : A →ₗ[K] K)
    (a : coefficientAnnihilator q I) (p : P) :
    coefficientAnnihilatorToDual q I ε a (Ideal.Quotient.mk I p) = ε (q p * a.val) := rfl

theorem coefficientAnnihilatorToDual_injective
    (q : P →ₐ[K] A) (hq : Function.Surjective q) (I : Ideal P) (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ b : A, ε (a * b) = 0) → a = 0) :
    Function.Injective (coefficientAnnihilatorToDual q I ε) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply Subtype.ext
  apply hε
  intro b
  obtain ⟨p, rfl⟩ := hq b
  have h := LinearMap.congr_fun ha (Ideal.Quotient.mk I p)
  simpa only [coefficientAnnihilatorToDual_mk, LinearMap.zero_apply, mul_comm] using h

/-- The leading coefficient space is bounded by the actual endpoint colength.
Frobenius separation of the original ordinary quotient is the only pairing
hypothesis, and the dual map is proved injective above. -/
theorem coefficientAnnihilator_finrank_le
    (q : P →ₐ[K] A) (hq : Function.Surjective q) (I : Ideal P)
    [Module.Finite K (P ⧸ I)] (ε : A →ₗ[K] K)
    (hε : ∀ a : A, (∀ b : A, ε (a * b) = 0) → a = 0) :
    Module.finrank K (coefficientAnnihilator q I) ≤ Module.finrank K (P ⧸ I) := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (coefficientAnnihilatorToDual_injective q hq I ε hε)
  simpa only [Subspace.dual_finrank_eq] using hh

end CoefficientAnnihilator

end PaperVerification.Fermion
