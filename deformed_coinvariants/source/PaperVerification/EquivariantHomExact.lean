module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.Projective

/-!
# Exactness of actual intertwining spaces by averaging

The group order is required to be invertible, not the characteristic to be
zero. An ordinary linear lift is averaged to construct an equivariant lift.
Consequently `Hom_G(L,-)` preserves the actual image-kernel equality and every
surjection. The source representation may be any representation over the
ground field; no splitting-field or absolute irreducibility assumption occurs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Representation
open scoped BigOperators

namespace PaperVerification.EquivariantHomExact

section Ring

variable {R G V W L : Type*} [CommRing R] [Group G] [Fintype G]
  [Invertible (Fintype.card G : R)]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup L] [Module R L]

theorem averageMap_eq_sum (ρ : Representation R G V) :
    ρ.averageMap = ⅟(Fintype.card G : R) • ∑ g : G, ρ g := by
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_of]

theorem averageMap_natural (ρ : Representation R G V) (σ : Representation R G W)
    (f : V →ₗ[R] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (x : V) :
    f (ρ.averageMap x) = σ.averageMap (f x) := by
  simp only [averageMap_eq_sum, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, hf]

theorem averageMap_idempotent (ρ : Representation R G V) :
    ρ.averageMap.comp ρ.averageMap = ρ.averageMap := by
  ext x
  exact ρ.averageMap_id _ (ρ.averageMap_invariant x)

def homPost (f : V →ₗ[R] W) : (L →ₗ[R] V) →ₗ[R] (L →ₗ[R] W) where
  toFun h := f.comp h
  map_add' _ _ := LinearMap.comp_add _ _ _
  map_smul' _ _ := LinearMap.comp_smul _ _ _

@[simp] theorem homPost_apply (f : V →ₗ[R] W) (h : L →ₗ[R] V) (x : L) :
    homPost f h x = f (h x) := rfl

theorem homPost_intertwines (τ : Representation R G L)
    {ρ : Representation R G V} {σ : Representation R G W}
    (f : IntertwiningMap ρ σ) (g : G) (h : L →ₗ[R] V) :
    homPost f.toLinearMap (Representation.linHom τ ρ g h) =
      Representation.linHom τ σ g (homPost f.toLinearMap h) := by
  ext x
  simp only [Representation.linHom_apply, LinearMap.comp_apply, homPost_apply,
    IntertwiningMap.toLinearMap_apply, f.isIntertwining]

/-- An actual intertwiner constructed from an arbitrary underlying linear map. -/
def averagedIntertwiner (τ : Representation R G L) (ρ : Representation R G V)
    (h : L →ₗ[R] V) : IntertwiningMap τ ρ :=
  (Representation.invariantsEquivIntertwiningMap τ ρ)
    ⟨(Representation.linHom τ ρ).averageMap h,
      (Representation.linHom τ ρ).averageMap_invariant h⟩

@[simp] theorem averagedIntertwiner_toLinearMap (τ : Representation R G L)
    (ρ : Representation R G V) (h : L →ₗ[R] V) :
    (averagedIntertwiner τ ρ h).toLinearMap = (Representation.linHom τ ρ).averageMap h := rfl

@[simp] theorem averagedIntertwiner_of_intertwiner (τ : Representation R G L)
    (ρ : Representation R G V) (h : IntertwiningMap τ ρ) :
    averagedIntertwiner τ ρ h.toLinearMap = h := by
  apply IntertwiningMap.ext
  exact (Representation.linHom τ ρ).averageMap_id _
    ((Representation.invariantsEquivIntertwiningMap τ ρ).symm h).property

theorem averagedIntertwiner_post (τ : Representation R G L)
    {ρ : Representation R G V} {σ : Representation R G W}
    (f : IntertwiningMap ρ σ) (h : L →ₗ[R] V) :
    f.comp (averagedIntertwiner τ ρ h) =
      averagedIntertwiner τ σ (f.toLinearMap.comp h) := by
  apply IntertwiningMap.ext
  exact averageMap_natural (Representation.linHom τ ρ) (Representation.linHom τ σ)
    (homPost f.toLinearMap) (homPost_intertwines τ f) h

end Ring

section Field

variable {K G U V W L : Type*} [Field K] [Group G] [Fintype G]
  [Invertible (Fintype.card G : K)]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup L] [Module K L]
variable (τ : Representation K G L)
variable {ρU : Representation K G U} {ρV : Representation K G V}
  {ρW : Representation K G W}

/-- Lift an intertwiner through its actual containing image. The lift is
constructed by a linear section followed by the Reynolds operator. -/
theorem exists_intertwiner_lift (f : IntertwiningMap ρV ρW) (h : IntertwiningMap τ ρW)
    (himage : ∀ x, h x ∈ LinearMap.range f.toLinearMap) :
    ∃ l : IntertwiningMap τ ρV, f.comp l = h := by
  let h' : L →ₗ[K] LinearMap.range f.toLinearMap := h.toLinearMap.codRestrict _ himage
  obtain ⟨s, hs⟩ := f.toLinearMap.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr f.toLinearMap.surjective_rangeRestrict)
  let l : L →ₗ[K] V := s.comp h'
  have hl : f.toLinearMap.comp l = h.toLinearMap := by
    ext x
    exact congrArg Subtype.val (LinearMap.congr_fun hs (h' x))
  refine ⟨averagedIntertwiner τ ρV l, ?_⟩
  rw [averagedIntertwiner_post, hl, averagedIntertwiner_of_intertwiner]

/-- Exactness of `Hom_G(L,-)` is proved by averaging, over every field in
which the finite group order is invertible. -/
theorem intertwiner_post_exact (f : IntertwiningMap ρV ρW)
    (g : IntertwiningMap ρU ρV)
    (hexact : LinearMap.range g.toLinearMap = LinearMap.ker f.toLinearMap) :
    LinearMap.range (IntertwiningMap.llcomp τ ρU ρV g) =
      LinearMap.ker (IntertwiningMap.llcomp τ ρV ρW f) := by
  apply le_antisymm
  · rintro h ⟨l, rfl⟩
    change f.comp (g.comp l) = 0
    apply IntertwiningMap.ext
    ext x
    exact hexact.le (LinearMap.mem_range_self g.toLinearMap (l x))
  · intro h hh
    change f.comp h = 0 at hh
    have himage : ∀ x, h x ∈ LinearMap.range g.toLinearMap := by
      intro x
      apply hexact.ge
      exact congrArg (fun t : IntertwiningMap τ ρW => t x) hh
    obtain ⟨l, hl⟩ := exists_intertwiner_lift τ g h himage
    exact ⟨l, hl⟩

theorem intertwiner_post_surjective (f : IntertwiningMap ρV ρW)
    (hf : Function.Surjective f) :
    Function.Surjective (IntertwiningMap.llcomp τ ρV ρW f) := by
  intro h
  exact exists_intertwiner_lift τ f h (fun x => hf (h x))

/-- Degreewise dimension additivity for the literal equivariant cokernel.
This applies to each invariant-generator step of a homogeneous regular sequence. -/
theorem intertwiner_cokernel_finrank [Module.Finite K L] [Module.Finite K V]
    (f : IntertwiningMap ρV ρW) (g : IntertwiningMap ρU ρV)
    (hf : Function.Surjective f)
    (hexact : LinearMap.range g.toLinearMap = LinearMap.ker f.toLinearMap) :
    Module.finrank K (IntertwiningMap τ ρW) +
      Module.finrank K (LinearMap.range (IntertwiningMap.llcomp τ ρU ρV g)) =
        Module.finrank K (IntertwiningMap τ ρV) := by
  have h := (IntertwiningMap.llcomp τ ρV ρW f).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (intertwiner_post_surjective τ f hf),
    finrank_top, ← intertwiner_post_exact τ f g hexact] at h
  exact h

end Field

end PaperVerification.EquivariantHomExact
