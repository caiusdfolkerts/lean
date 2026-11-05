module

public import PaperVerification.FermionFilteredModuleSpanning
public import PaperVerification.FermionTwoSidedBasisSpan
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Finiteness descends from the actual homogeneous quotient

A finite homogeneous quotient has a finite spanning subset of the images of
an ambient homogeneous basis.  The filtered reduction transports that finite
family.  This establishes finiteness of the deformed module before any use of
closed-point basis descent.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

variable {R A Q Q₀ I J : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Q₀] [Module R Q₀]

theorem finite_of_filtered_relation_spans
    (b : Module.Basis I R A) (w : I → ℕ)
    (f g : J → A) (degree : J → ℕ)
    (htop : ∀ j, BasisFiltered.HasTop b w (degree j) (f j) (g j))
    (q : A →ₗ[R] Q) (q₀ : A →ₗ[R] Q₀)
    (hs : Function.Surjective q) (hs₀ : Function.Surjective q₀)
    (hker : q.ker = Submodule.span R (Set.range f))
    (hker₀ : q₀.ker = Submodule.span R (Set.range g))
    [Module.Finite R Q₀] : Module.Finite R Q := by
  classical
  have hfull : Submodule.span R (Set.range (fun i ↦ q₀ (b i))) = ⊤ := by
    change Submodule.span R (Set.range (q₀ ∘ b)) = ⊤
    rw [Set.range_comp,← Submodule.map_span,b.span_eq,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hs₀
  have hfg : (Submodule.span R (Set.range (fun i ↦ q₀ (b i)))).FG := by
    rw [hfull]
    exact Module.Finite.fg_top
  obtain ⟨t,ht,heq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range (fun i ↦ q₀ (b i)))).mp hfg
  let T := {y : Q₀ // y ∈ t}
  let index (y : T) : I := Classical.choose (ht y.property)
  have hindex (y : T) : q₀ (b (index y)) = y.val := Classical.choose_spec (ht y.property)
  let v (y : T) : A := b (index y)
  have hrange : Set.range (fun y : T ↦ q₀ (v y)) = (t : Set Q₀) := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      change q₀ (b (index z)) ∈ t
      rw [hindex]
      exact z.property
    · intro hy
      exact ⟨⟨y,hy⟩,hindex ⟨y,hy⟩⟩
  have hfiniteSpan : Submodule.span R (Set.range (fun y : T ↦ q₀ (v y))) = ⊤ := by
    rw [hrange,← heq,hfull]
  have hleading : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤ := by
    rw [← hker₀]
    exact (span_image_eq_top_iff q₀ hs₀ v).mp hfiniteSpan
  have hactual : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range f)=⊤ :=
    BasisFiltered.spanning_lifts b w f g degree htop v (fun y ↦ w (index y))
      (fun y ↦ BasisFiltered.homogeneous_basis b w (index y)) hleading
  have hspan : Submodule.span R (Set.range (fun y : T ↦ q (v y))) = ⊤ := by
    apply (span_image_eq_top_iff q hs v).mpr
    rw [hker]
    exact hactual
  have hfg' : (Submodule.span R (Set.range (fun y : T ↦ q (v y)))).FG :=
    Submodule.fg_span (Set.finite_range _)
  rw [hspan] at hfg'
  exact Module.Finite.of_fg_top hfg'

end PaperVerification.Fermion
