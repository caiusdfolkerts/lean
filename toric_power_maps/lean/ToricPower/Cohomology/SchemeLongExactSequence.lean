module

public import ToricPower.Cohomology.SchemeConnectingLinear

/-! Base-ring linearity and finite-dimensional consequences of the actual
long exact cohomology sequence. -/

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

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
  {S : ShortComplex X.Modules}

omit hS in
/-- For a scheme over a commutative ring, the connecting map of the long exact cohomology
sequence is linear over the base ring. -/
def cohomologyδBaseLinear (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →ₗ[R] Cohomology S.X₁ n₁ where
  toFun := cohomologyδ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' r x := by
    rw [base_smul_cohomology]
    -- As for `cohomologyMapBaseLinear`, normalize the restricted action to the action of global
    -- functions and apply the linearity already proved there.
    change cohomologyδLinear hS n₀ n₁ h ((baseRingToGlobalSections R X r) • x) =
      (baseRingToGlobalSections R X r) • cohomologyδLinear hS n₀ n₁ h x
    exact (cohomologyδLinear hS n₀ n₁ h).map_smul _ x

omit hS in
@[simp]
lemma cohomologyδBaseLinear_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Cohomology S.X₃ n₀) :
    cohomologyδBaseLinear R X hS n₀ n₁ h x = cohomologyδ hS n₀ n₁ h x :=
  (rfl)

end Base

section Field

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  {S : ShortComplex X.Modules}

omit hS in
/-- `Hⁱ(X, M₂)` is squeezed by the exact sequence between `Hⁱ(X, M₁)` and `Hⁱ(X, M₃)`, so it is
finite-dimensional as soon as those two are. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_X₂
    (hS : S.ShortExact) (i : ℕ) [FiniteDimensional k (Cohomology S.X₁ i)]
    [FiniteDimensional k (Cohomology S.X₃ i)] :
    FiniteDimensional k (Cohomology S.X₂ i) := by
  have hex : Function.Exact (cohomologyMapBaseLinear k X S.f i)
      (cohomologyMapBaseLinear k X S.g i) := by
    have coe_map : ∀ {M N : X.Modules} (f : M ⟶ N),
        ⇑(cohomologyMapBaseLinear k X f i) = ⇑(cohomologyMap f i) := by
      intro M N f
      funext x
      rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
      rfl
    rw [coe_map, coe_map]
    exact exact_cohomologyMap_cohomologyMap hS i
  exact finiteDimensional_of_exact hex

omit hS in
/-- `Hⁿ¹(X, M₁)` is squeezed by the exact sequence between `Hⁿ⁰(X, M₃)` and `Hⁿ¹(X, M₂)`, where
`n₀ + 1 = n₁`, so it is finite-dimensional as soon as those two are. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_X₁
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    [FiniteDimensional k (Cohomology S.X₃ n₀)] [FiniteDimensional k (Cohomology S.X₂ n₁)] :
    FiniteDimensional k (Cohomology S.X₁ n₁) := by
  have hex : Function.Exact (cohomologyδBaseLinear k X hS n₀ n₁ h)
      (cohomologyMapBaseLinear k X S.f n₁) := by
    intro x
    rw [cohomologyMapBaseLinear_apply, cohomologyFunctor_map]
    exact exact_cohomologyδ_cohomologyMap hS n₀ n₁ h x
  exact finiteDimensional_of_exact hex

end Field

end TauCeti.AlgebraicGeometry.Scheme.Modules

end
