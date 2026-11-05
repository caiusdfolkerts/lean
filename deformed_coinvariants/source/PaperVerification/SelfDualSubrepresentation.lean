module

public import PaperVerification.EquivariantSection
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Moving a self-dual subrepresentation out of a dual space

An injective intertwiner into a dual space gives a surjective transpose. A
self-duality identifies its target with the original representation, and
averaging a linear section gives an actual injective intertwiner. This is a
linear-algebra proof over the given characteristic-zero field; no assertion
about irreducible characters or a splitting field is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SelfDualSubrepresentation

variable {K G V W : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W]

theorem exists_injective_intertwiner
    (ρ : Representation K G V) (σ : Representation K G W)
    (e : W ≃ₗ[K] Module.Dual K W)
    (he : ∀ g v w, e (σ g v) w = e v (σ g⁻¹ w))
    (f : W →ₗ[K] Module.Dual K V)
    (hf : ∀ g w v, f (σ g w) v = f w (ρ g⁻¹ v))
    (hi : Function.Injective f) :
    ∃ s : Representation.IntertwiningMap σ ρ, Function.Injective s := by
  let q : V →ₗ[K] W := e.symm.toLinearMap.comp f.flip
  have hq_apply (v : V) : e (q v) = f.flip v := e.apply_symm_apply _
  have hq_surjective : Function.Surjective q := by
    intro w
    obtain ⟨Φ, hΦ⟩ := LinearMap.dualMap_surjective_of_injective hi (e w)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv K V).surjective Φ
    refine ⟨v, e.injective ?_⟩
    rw [hq_apply]
    exact hΦ
  have hq_intertwines (g : G) (v : V) : q (ρ g v) = σ g (q v) := by
    apply e.injective
    apply LinearMap.ext
    intro w
    rw [hq_apply, he, hq_apply]
    change f w (ρ g v) = f (σ g⁻¹ w) v
    simpa only [inv_inv] using (hf g⁻¹ w v).symm
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq_surjective)
  have hsq (w : W) : q (s w) = w := LinearMap.congr_fun hs w
  let a : W →ₗ[K] V := EquivariantSection.average ρ σ s
  have hqa (w : W) : q (a w) = w :=
    EquivariantSection.average_rightInverse ρ σ q s hq_intertwines hsq w
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro g
    ext w
    exact EquivariantSection.average_intertwines ρ σ s g w
  · intro v w hvw
    have h := congrArg q hvw
    change q (a v) = q (a w) at h
    rw [hqa, hqa] at h
    exact h

end PaperVerification.SelfDualSubrepresentation
