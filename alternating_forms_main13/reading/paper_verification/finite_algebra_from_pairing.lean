module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!+# Identifying a finite algebra from an integration pairing

Suppose a known quotient `P / I` has the same dimension as an upper bound for
an independently defined algebra `B`. If an algebra map `P → B` has kernel
contained in `I`, the dimension bound forces both surjectivity and equality
of the two ideals. An integration functional with exact annihilator `I`
provides precisely that kernel containment.

In a geometric application, both the dimension bound and the integration
identity must be proved for the actual geometric algebra. This lemma does
not define that algebra or supply either of those inputs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.FiniteAlgebraFromPairing

variable {K P B : Type*} [Field K] [CommRing P] [CommRing B]
  [Algebra K P] [Algebra K B]

/-- A quotient of the indicated dimension cannot have a strictly smaller
defining ideal while mapping into an algebra of at most that dimension. -/
theorem kernel_eq_and_surjective (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    RingHom.ker f = I ∧ Function.Surjective f := by
  let e := Ideal.quotientKerEquivRange f
  letI : FiniteDimensional K (P ⧸ RingHom.ker f) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let q : (P ⧸ RingHom.ker f) →ₐ[K] P ⧸ I := Ideal.Quotient.factorₐ K hker
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hQA : Module.finrank K (P ⧸ I) ≤ Module.finrank K (P ⧸ RingHom.ker f) :=
    LinearMap.finrank_le_finrank_of_surjective (f := q.toLinearMap) hq
  have hQB : Module.finrank K (P ⧸ RingHom.ker f) ≤ Module.finrank K B := by
    rw [e.toLinearEquiv.finrank_eq]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := f.range.val.toLinearMap) Subtype.val_injective
  have hQAeq : Module.finrank K (P ⧸ RingHom.ker f) = Module.finrank K (P ⧸ I) :=
    le_antisymm (hQB.trans hdim) hQA
  have hqi : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := q.toLinearMap) hQAeq).mpr hq
  have hI : I ≤ RingHom.ker f := by
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hqi
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hRange : Module.finrank K f.range = Module.finrank K B := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact le_antisymm hQB (hdim.trans hQA)
  have hSurjRange : Function.Surjective f.range.val :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.range.val.toLinearMap) hRange).mp Subtype.val_injective
  refine ⟨le_antisymm hker hI, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hSurjRange b
  obtain ⟨p, hp⟩ := a.property
  exact ⟨p, hp.trans ha⟩

/-- The actual quotient isomorphism produced by the dimension argument. -/
def quotientEquiv (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    (P ⧸ I) ≃ₐ[K] B :=
  (Ideal.quotientEquivAlgOfEq K (kernel_eq_and_surjective I f hker hdim).1.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (kernel_eq_and_surjective I f hker hdim).2)

@[simp] theorem quotientEquiv_mk (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (hker : RingHom.ker f ≤ I)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) (p : P) :
    quotientEquiv I f hker hdim (Ideal.Quotient.mk I p) = f p := by
  simp only [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Factoring an exact annihilator pairing through an algebra map forces
its kernel to be contained in the known relation ideal. -/
theorem kernel_le_of_pairing (I : Ideal P) (f : P →ₐ[K] B)
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p) :
    RingHom.ker f ≤ I := by
  intro p hp
  apply (hI p).mpr
  intro q
  rw [← htrace, map_mul, RingHom.mem_ker.mp hp, zero_mul, map_zero]

/-- An integration formula and the sharp total-dimension bound identify
the complete algebra. No duality property of `B` is an extra assumption. -/
def quotientEquivOfPairing (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) :
    (P ⧸ I) ≃ₐ[K] B :=
  quotientEquiv I f (kernel_le_of_pairing I f L trace hI htrace) hdim

@[simp] theorem quotientEquivOfPairing_mk (I : Ideal P) (f : P →ₐ[K] B)
    [FiniteDimensional K (P ⧸ I)] [FiniteDimensional K B]
    (L : P →ₗ[K] K) (trace : B →ₗ[K] K)
    (hI : ∀ p, p ∈ I ↔ ∀ q, L (p * q) = 0)
    (htrace : ∀ p, trace (f p) = L p)
    (hdim : Module.finrank K B ≤ Module.finrank K (P ⧸ I)) (p : P) :
    quotientEquivOfPairing I f L trace hI htrace hdim (Ideal.Quotient.mk I p) = f p := by
  exact quotientEquiv_mk I f _ hdim p

end PaperVerification.FiniteAlgebraFromPairing
