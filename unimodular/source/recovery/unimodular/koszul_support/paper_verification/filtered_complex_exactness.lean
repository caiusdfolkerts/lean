module

public import Mathlib.LinearAlgebra.Basis.Basic

public import Recovery.Unimodular.KoszulSupport.PaperVerification.FermionFilteredInitial

/-!
# Exactness and strictness for a filtered perturbation

The filtration is the actual finite support filtration of a weighted basis.
The leading differential is an explicit linear map, with equality of every
leading component required.  Exactness of the leading pair then proves
exactness of the perturbed pair by finite descent.  At the next degree it
also proves strictness of the first image, which rules out new leading
relations caused by cancellation among multipliers.

This is supporting mathematics for the differential normal-form theorem.
The leading exactness and differential identities must still be established
for its actual Lie--Rinehart and Koszul complexes; they are not conclusions
about those complexes merely from this abstract lemma.  This source has not
yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredComplex

open Fermion.BasisFiltered

variable {R M₀ M₁ M₂ I₀ I₁ I₂ : Type*} [CommRing R]
  [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
  (b₀ : Module.Basis I₀ R M₀) (w₀ : I₀ → ℕ)
  (b₁ : Module.Basis I₁ R M₁) (w₁ : I₁ → ℕ)
  (b₂ : Module.Basis I₂ R M₂) (w₂ : I₂ → ℕ)

/-- The perturbed map preserves each actual filtration bound and has the
displayed map on leading components. -/
def HasLeadingMap (f g : M₁ →ₗ[R] M₀) : Prop :=
  ∀ d x, Bound b₁ w₁ d x →
    Bound b₀ w₀ d (f x) ∧
      component b₀ w₀ d (f x) = g (component b₁ w₁ d x)

/-- Homogeneity means commutation with the actual component projections. -/
def PreservesComponents (g : M₁ →ₗ[R] M₀) : Prop :=
  ∀ d x, g (component b₁ w₁ d x) = component b₀ w₀ d (g x)

variable (f : M₁ →ₗ[R] M₀) (d : M₂ →ₗ[R] M₁)
  (f₀ : M₁ →ₗ[R] M₀) (d₀ : M₂ →ₗ[R] M₁)

/-- A leading cycle has a homogeneous preimage in the leading complex.
Applying the perturbed differential gives a bounded lift of that cycle. -/
theorem leading_cycle_lift
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (m : ℕ) (x : M₁) (hx : f₀ (component b₁ w₁ m x) = 0) :
    ∃ y, Bound b₂ w₂ m y ∧ Bound b₁ w₁ m (d y) ∧
      component b₁ w₁ m (d y) = component b₁ w₁ m x := by
  have hmem : component b₁ w₁ m x ∈ d₀.range := by
    rw [hexact]
    exact LinearMap.mem_ker.mpr hx
  obtain ⟨z,hz⟩ := hmem
  let y := component b₂ w₂ m z
  have hy : Bound b₂ w₂ m y := bound_component b₂ w₂ m z
  have hyy : component b₂ w₂ m y = y := by
    rw [component_of_homogeneous b₂ w₂ (homogeneous_component b₂ w₂ m z),if_pos rfl]
  have hxx : component b₁ w₁ m (component b₁ w₁ m x) =
      component b₁ w₁ m x := by
    rw [component_of_homogeneous b₁ w₁ (homogeneous_component b₁ w₁ m x),if_pos rfl]
  refine ⟨y,hy,(hd m y hy).1,?_⟩
  rw [(hd m y hy).2,hyy]
  change d₀ (component b₂ w₂ m z) = component b₁ w₁ m x
  rw [hd₀ m z,hz,hxx]

/-- Every actual cycle with bound `m` is a boundary with that same bound.
No completion or infinite series enters the proof. -/
theorem bounded_cycle_is_boundary
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (m : ℕ) (x : M₁) (hbound : Bound b₁ w₁ m x) (hx : f x = 0) :
    ∃ y, Bound b₂ w₂ m y ∧ d y = x := by
  have hfd (y : M₂) : f (d y) = 0 := LinearMap.congr_fun hzero y
  induction m generalizing x with
  | zero =>
      have hc : f₀ (component b₁ w₁ 0 x) = 0 := by
        rw [←(hf 0 x hbound).2,hx,map_zero]
      obtain ⟨y,hy,hdy,he⟩ :=
        leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact 0 x hc
      have hz : x-d y = 0 :=
        eq_zero_of_bound_zero_component_zero b₁ w₁
          (bound_sub b₁ w₁ hbound hdy) (by rw [map_sub,he,sub_self])
      exact ⟨y,hy,(sub_eq_zero.mp hz).symm⟩
  | succ m ih =>
      have hc : f₀ (component b₁ w₁ (m+1) x) = 0 := by
        rw [←(hf (m+1) x hbound).2,hx,map_zero]
      obtain ⟨y,hy,hdy,he⟩ :=
        leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact (m+1) x hc
      have hr : Bound b₁ w₁ m (x-d y) :=
        bound_pred_of_component_zero b₁ w₁
          (bound_sub b₁ w₁ hbound hdy) (by rw [map_sub,he,sub_self])
      have hcycle : f (x-d y) = 0 := by rw [map_sub,hx,hfd,sub_self]
      obtain ⟨z,hz,hez⟩ := ih (x-d y) hr hcycle
      refine ⟨z+y,bound_add b₂ w₂
        (bound_mono b₂ w₂ (Nat.le_succ m) hz) hy,?_⟩
      rw [map_add,hez,sub_add_cancel]

/-- The entire perturbed pair is exact.  The conclusion is equality of
the actual range and actual kernel. -/
theorem range_eq_ker
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker) : d.range = f.ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (LinearMap.congr_fun hzero y)
  · intro hx
    obtain ⟨m,hm⟩ := exists_bound b₁ w₁ x
    obtain ⟨y,hy,he⟩ := bounded_cycle_is_boundary b₀ w₀ b₁ w₁ b₂ w₂
      f d f₀ d₀ hzero hf hd hd₀ hexact m x hm (LinearMap.mem_ker.mp hx)
    exact ⟨y,he⟩

/-- Cancellation among leading multipliers can be removed by subtracting
actual boundaries. Every bounded image has a preimage with the same bound. -/
theorem image_has_bounded_preimage
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (r : ℕ) (u : M₀) (hu : Bound b₀ w₀ r u) (him : u ∈ f.range) :
    ∃ x, Bound b₁ w₁ r x ∧ f x = u := by
  have hfd (y : M₂) : f (d y) = 0 := LinearMap.congr_fun hzero y
  have reduce : ∀ m x, Bound b₁ w₁ m x → f x = u →
      ∃ z, Bound b₁ w₁ r z ∧ f z = u := by
    intro m
    induction m with
    | zero =>
        intro x hx hxu
        exact ⟨x,bound_mono b₁ w₁ (Nat.zero_le r) hx,hxu⟩
    | succ m ih =>
        intro x hx hxu
        by_cases hmr : m+1 ≤ r
        · exact ⟨x,bound_mono b₁ w₁ hmr hx,hxu⟩
        · have hrm : r < m+1 := Nat.lt_of_not_ge hmr
          have hc : f₀ (component b₁ w₁ (m+1) x) = 0 := by
            rw [←(hf (m+1) x hx).2,hxu]
            exact component_eq_zero_of_bound_lt b₀ w₀ hrm hu
          obtain ⟨y,hy,hdy,he⟩ :=
            leading_cycle_lift b₁ w₁ b₂ w₂ d f₀ d₀ hd hd₀ hexact (m+1) x hc
          apply ih (x-d y)
          · exact bound_pred_of_component_zero b₁ w₁
              (bound_sub b₁ w₁ hx hdy) (by rw [map_sub,he,sub_self])
          · rw [map_sub,hxu,hfd,sub_zero]
  obtain ⟨x,hx⟩ := him
  obtain ⟨m,hm⟩ := exists_bound b₁ w₁ x
  exact reduce m x hm hx

/-- The leading part of every actual image belongs to the leading image.
This is a consequence of strictness, not a premise asserting the desired
associated-graded relation space. -/
theorem component_image_mem_leading_range
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (r : ℕ) (u : M₀) (hu : Bound b₀ w₀ r u) (him : u ∈ f.range) :
    component b₀ w₀ r u ∈ f₀.range := by
  obtain ⟨x,hx,hxu⟩ := image_has_bounded_preimage b₀ w₀ b₁ w₁ b₂ w₂
    f d f₀ d₀ hzero hf hd hd₀ hexact r u hu him
  exact ⟨component b₁ w₁ r x,((hf r x hx).2).symm.trans
    (congrArg (component b₀ w₀ r) hxu)⟩

/-- The initial submodule of the actual image is exactly the leading
image. Its definition uses leading components of actual image vectors. -/
theorem initial_image_eq
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker) :
    initialSubmodule b₀ w₀ f.range = f₀.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨u,hu,r,hb,rfl⟩
    exact component_image_mem_leading_range b₀ w₀ b₁ w₁ b₂ w₂
      f d f₀ d₀ hzero hf hd hd₀ hexact r u hb hu
  · rintro y ⟨x,rfl⟩
    have hx : x ∈ Submodule.span R (Set.range b₁) := by
      rw [b₁.span_eq]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        have hbi := homogeneous_bound b₁ w₁ (homogeneous_basis b₁ w₁ i)
        apply Submodule.subset_span
        refine ⟨f (b₁ i),⟨b₁ i,rfl⟩,w₁ i,(hf (w₁ i) (b₁ i) hbi).1,?_⟩
        rw [(hf (w₁ i) (b₁ i) hbi).2,
          component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_pos rfl]
    | zero => simpa only [map_zero] using (initialSubmodule b₀ w₀ f.range).zero_mem
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using (initialSubmodule b₀ w₀ f.range).add_mem ihx ihy
    | smul a x hx ih =>
        simpa only [map_smul] using (initialSubmodule b₀ w₀ f.range).smul_mem a ih

end PaperVerification.FilteredComplex
