module
public import ToricPower.Cohomology.SchemeConnectingExactness
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules
namespace TauCeti.AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

omit hS in
/-- A monomorphism of sheaves of modules is injective on degree-zero cohomology. -/
theorem cohomologyMap_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (cohomologyMap f 0) := by
  intro x y hxy
  apply (CategoryTheory.Sheaf.H.map_injective.{u, u, u} ((toSheaf X).map f))
  simpa only [cohomologyMap_eq_sheafH, cohomologyδ, Cohomology, cohomologyFunctor,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Sheaf.functorH,
    ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ShortComplex.map_f, ShortComplex.map_g] using hxy

/-- Vanishing of the next cohomology group gives surjectivity. -/
theorem cohomologyMap_surjective (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (Cohomology S.X₁ n₁)) :
    Function.Surjective (cohomologyMap S.g n₀) := fun x =>
  (exact_cohomologyMap_cohomologyδ hS n₀ n₁ h x).1 (h₁.elim _ _)

/-- Vanishing of both outside terms implies vanishing of the middle term. -/
theorem subsingleton_cohomology_X₂ (n : ℕ) (h₁ : Subsingleton (Cohomology S.X₁ n))
    (h₃ : Subsingleton (Cohomology S.X₃ n)) : Subsingleton (Cohomology S.X₂ n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := (exact_cohomologyMap_cohomologyMap hS n x).1 (h₃.elim _ _)
  obtain ⟨b, hb⟩ := (exact_cohomologyMap_cohomologyMap hS n y).1 (h₃.elim _ _)
  exact ha.symm.trans ((congrArg (cohomologyMap S.f n) (h₁.elim a b)).trans hb)

/-- Vanishing before and after the connecting map implies vanishing at its source. -/
theorem subsingleton_cohomology_X₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Cohomology S.X₂ n₀)) (h₁ : Subsingleton (Cohomology S.X₁ n₁)) :
    Subsingleton (Cohomology S.X₃ n₀) := by
  letI := h₂
  exact (cohomologyMap_surjective hS n₀ n₁ h h₁).subsingleton

/-- Vanishing of both outside terms implies vanishing at the connecting target. -/
theorem subsingleton_cohomology_X₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₃ : Subsingleton (Cohomology S.X₃ n₀)) (h₂ : Subsingleton (Cohomology S.X₂ n₁)) :
    Subsingleton (Cohomology S.X₁ n₁) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha⟩ := (exact_cohomologyδ_cohomologyMap hS n₀ n₁ h x).1 (h₂.elim _ _)
  obtain ⟨b, hb⟩ := (exact_cohomologyδ_cohomologyMap hS n₀ n₁ h y).1 (h₂.elim _ _)
  exact ha.symm.trans ((congrArg (cohomologyδ hS n₀ n₁ h) (h₃.elim a b)).trans hb)

/-- Global sections are left exact: the sections of `M₁` are exactly the sections of `M₂` that
die in `M₃`. -/
theorem exact_sections : Function.Exact ⇑(S.f.app ⊤) ⇑(S.g.app ⊤) :=
  Function.Exact.of_ladder_addEquiv_of_exact (cohomologyZeroEquiv S.X₁)
    (cohomologyZeroEquiv S.X₂) (cohomologyZeroEquiv S.X₃) (cohomologySections_ladder S.f)
    (cohomologySections_ladder S.g) (exact_cohomologyMap_cohomologyMap hS 0)

omit hS in
/-- Global sections are left exact: a monomorphism of sheaves of modules is injective on global
sections. -/
theorem sections_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective ⇑(f.app ⊤) := by
  intro a b hab
  apply (cohomologyZeroEquiv M).symm.injective
  apply cohomologyMap_injective f
  apply (cohomologyZeroEquiv N).injective
  rw [cohomologyZeroEquiv_cohomologyMap, cohomologyZeroEquiv_cohomologyMap,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hab]

/-- If `H¹(X, M₁)` vanishes, then every global section of `M₃` lifts to a global section of `M₂`.
This is the form in which the long exact sequence is normally used. -/
theorem sections_surjective (h₁ : Subsingleton (Cohomology S.X₁ 1)) :
    Function.Surjective ⇑(S.g.app ⊤) := by
  intro y
  obtain ⟨x, hx⟩ := cohomologyMap_surjective hS 0 1 rfl h₁
    ((cohomologyZeroEquiv S.X₃).symm y)
  refine ⟨cohomologyZeroEquiv S.X₂ x, ?_⟩
  rw [← cohomologyZeroEquiv_cohomologyMap, hx, AddEquiv.apply_symm_apply]

end TauCeti.AlgebraicGeometry.Scheme.Modules

end
