module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel

/-!
# The linear algebra of Euler reduction

The polynomial Euler reduction has a useful formulation with four linear maps.
`C` is the coefficient map, `D` is divergence, `E` is multiplication by the
weighted Euler vector field, and `L = C ∘ E` is multiplication by the potential.
This file proves the exact relation space, without assuming that any operator
image is an ideal and without any finiteness hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.EulerReduction

variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- The full differential perturbation of a coefficient map. -/
def perturbed (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) : U →ₗ[K] V :=
  C + t • (L.comp D)

/-- The scalar Euler operator acting on polynomial inputs. -/
def eulerScalar (D : U →ₗ[K] W) (E : W →ₗ[K] U) (t : K) : W →ₗ[K] W :=
  LinearMap.id + t • (D.comp E)

@[simp] theorem perturbed_apply (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (L : W →ₗ[K] V) (t : K) (u : U) :
    perturbed C D L t u = C u + t • L (D u) := rfl

@[simp] theorem eulerScalar_apply (D : U →ₗ[K] W) (E : W →ₗ[K] U)
    (t : K) (w : W) : eulerScalar D E t w = w + t • D (E w) := rfl

/-- Euler's identity after applying the perturbation. -/
theorem perturbed_euler (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (w : W) :
    perturbed C D L t (E w) = L (eulerScalar D E t w) := by
  have hw : C (E w) = L w := congrArg (fun f : W →ₗ[K] V => f w) hE
  simp only [perturbed_apply, eulerScalar_apply, map_add, map_smul, hw]

/-- Every coefficient value is a sum of a hit and a potential multiple. -/
theorem coefficient_range (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) :
    LinearMap.range C = LinearMap.range (perturbed C D L t) ⊔ LinearMap.range L := by
  have hL (w : W) : L w = C (E w) :=
    (congrArg (fun f : W →ₗ[K] V => f w) hE).symm
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨perturbed C D L t u, ⟨u, rfl⟩, L (-t • D u), ⟨_, rfl⟩, ?_⟩
    simp only [perturbed_apply, map_smul, map_neg, neg_smul]
    abel
  · apply sup_le
    · rintro _ ⟨u, rfl⟩
      refine ⟨u + t • E (D u), ?_⟩
      simp only [perturbed_apply, map_add, map_smul, ← hL]
    · rintro _ ⟨w, rfl⟩
      exact ⟨E w, (hL w).symm⟩

/-- The exact relation space for potential multiples modulo the hit space.
This is the algebraic kernel computation in Lemma 6.1. -/
theorem potential_relation_iff (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) (w : W) :
    L w ∈ LinearMap.range (perturbed C D L t) ↔
      w ∈ LinearMap.range (eulerScalar D E t) ⊔
        (LinearMap.ker C).map (t • D) := by
  constructor
  · rintro ⟨u, hu⟩
    let v := w - t • D u
    let z := u - E v
    have hCv : C u = L v := by
      dsimp [v]
      simp only [map_sub, map_smul]
      have hu' : C u + t • L (D u) = L w := hu
      rw [← hu']
      abel
    have hz : z ∈ LinearMap.ker C := by
      rw [LinearMap.mem_ker]
      dsimp [z]
      simp only [map_sub, hCv]
      have hv : C (E v) = L v := congrArg (fun f : W →ₗ[K] V => f v) hE
      rw [hv, sub_self]
    apply Submodule.mem_sup.mpr
    refine ⟨eulerScalar D E t v, ⟨v, rfl⟩, (t • D) z,
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
    simp only [eulerScalar_apply, LinearMap.smul_apply]
    dsimp [z, v]
    simp only [map_sub, map_smul]
    simp only [smul_sub, smul_add]
    abel
  · intro hw
    obtain ⟨a, ⟨v, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hb
    have hCz : C z = 0 := LinearMap.mem_ker.mp hz
    refine ⟨E v + z, ?_⟩
    rw [map_add, perturbed_euler C D E L t hE]
    rw [perturbed_apply, hCz, zero_add]
    rw [← hab]
    simp only [map_add, LinearMap.smul_apply, map_smul]

/-- The kernel statement packages the preceding elementwise calculation for
the first isomorphism theorem. -/
theorem potential_quotient_kernel (C : U →ₗ[K] V) (D : U →ₗ[K] W)
    (E : W →ₗ[K] U) (L : W →ₗ[K] V) (t : K)
    (hE : C.comp E = L) :
    LinearMap.ker ((LinearMap.range (perturbed C D L t)).mkQ.comp L) =
      LinearMap.range (eulerScalar D E t) ⊔
        (LinearMap.ker C).map (t • D) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change (LinearMap.range (perturbed C D L t)).mkQ (L w) = 0 ↔ _
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact potential_relation_iff C D E L t hE w

end PaperVerification.EulerReduction
