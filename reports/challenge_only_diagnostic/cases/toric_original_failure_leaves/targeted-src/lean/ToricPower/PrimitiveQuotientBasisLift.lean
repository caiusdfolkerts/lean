module

public import TauCeti.Algebra.Module.Primitive
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Lifting a quotient basis across a primitive cyclic kernel

Arbitrary integral lifts of a basis of `N / ℤa`, together with the
primitive vector `a`, form an actual integral basis of `N`. The map and
its inverse are obtained from the exact kernel calculation. This is the
regularity argument for the cones attached in relative fan completion.
-/

@[expose] public noncomputable section

open TauCeti
namespace ToricPower.FanSubdivision

variable {N P ι : Type*} [AddCommGroup N] [AddCommGroup P]
  (projection : N →ₗ[ℤ] P) (a : N)
  (kernel : projection.ker = Submodule.span ℤ {a})
  (basis : Module.Basis ι ℤ P) (lifts : ι → N)
  (projects : ∀ j, projection (lifts j) = basis j)

/-- The actual section determined by the selected integral lifts. -/
def quotientBasisSection : P →ₗ[ℤ] N := basis.constr ℤ lifts

@[simp]
theorem quotientBasisSection_basis (j : ι) :
    quotientBasisSection basis lifts (basis j) = lifts j := by
  exact basis.constr_basis ℤ lifts j

include projects in
theorem quotientBasisSection_rightInverse :
    projection.comp (quotientBasisSection basis lifts) = LinearMap.id := by
  apply basis.ext
  intro j
  simpa only [LinearMap.comp_apply,quotientBasisSection_basis,LinearMap.id_apply]
    using projects j

include kernel in
theorem primitiveKernel_generator_eq_zero : projection a = 0 := by
  apply LinearMap.mem_ker.mp
  rw [kernel]
  exact Submodule.mem_span_singleton_self _

/-- Sum of the kernel coordinate and the selected quotient section. -/
def quotientBasisProductMap : (ℤ × P) →ₗ[ℤ] N :=
  (LinearMap.toSpanSingleton ℤ N a).coprod (quotientBasisSection basis lifts)

@[simp]
theorem quotientBasisProductMap_apply (r : ℤ) (p : P) :
    quotientBasisProductMap a basis lifts (r,p) =
      r • a + quotientBasisSection basis lifts p := rfl

include kernel projects in
theorem quotientBasisProductMap_projects (r : ℤ) (p : P) :
    projection (quotientBasisProductMap a basis lifts (r,p)) = p := by
  rw [quotientBasisProductMap_apply,map_add,map_smul,
    primitiveKernel_generator_eq_zero projection a kernel,smul_zero,zero_add]
  exact LinearMap.congr_fun (quotientBasisSection_rightInverse projection basis lifts projects) p

include kernel projects in
theorem quotientBasisProductMap_bijective (primitive : IsPrimitive a) :
    Function.Bijective (quotientBasisProductMap a basis lifts) := by
  obtain ⟨coordinate,value⟩ := isPrimitive_def.mp primitive
  constructor
  · rintro ⟨r,p⟩ ⟨s,q⟩ equal
    have same : p = q := by
      simpa only [quotientBasisProductMap_projects projection a kernel basis lifts projects]
        using congrArg projection equal
    subst q
    have scalars : r • a = s • a := by
      exact add_right_cancel equal
    have scalarEq : r = s := by
      simpa only [map_smul,value,smul_eq_mul,mul_one] using congrArg coordinate scalars
    exact Prod.ext scalarEq rfl
  · intro n
    have discrepancy : n - quotientBasisSection basis lifts (projection n) ∈ projection.ker := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub]
      have sectionEq := LinearMap.congr_fun
        (quotientBasisSection_rightInverse projection basis lifts projects) (projection n)
      change projection (quotientBasisSection basis lifts (projection n)) = projection n at sectionEq
      rw [sectionEq,sub_self]
    rw [kernel] at discrepancy
    obtain ⟨r,eq⟩ := Submodule.mem_span_singleton.mp discrepancy
    refine ⟨(r,projection n),?_⟩
    rw [quotientBasisProductMap_apply,eq,sub_add_cancel]

/-- The actual integral product decomposition, with the requested lifts. -/
def quotientBasisProductEquiv (primitive : IsPrimitive a) : (ℤ × P) ≃ₗ[ℤ] N :=
  LinearEquiv.ofBijective (quotientBasisProductMap a basis lifts)
    (quotientBasisProductMap_bijective projection a kernel basis lifts projects primitive)

/-- The first vector is the original primitive vector; every other
vector is exactly the prescribed integral lift. -/
def liftedQuotientBasis (primitive : IsPrimitive a) : Module.Basis (PUnit ⊕ ι) ℤ N :=
  ((Module.Basis.singleton PUnit ℤ).prod basis).map
    (quotientBasisProductEquiv projection a kernel basis lifts projects primitive)

@[simp]
theorem liftedQuotientBasis_inl (primitive : IsPrimitive a) (u : PUnit) :
    liftedQuotientBasis projection a kernel basis lifts projects primitive (.inl u) = a := by
  simp [liftedQuotientBasis,Module.Basis.map_apply,Module.Basis.prod_apply,
    quotientBasisProductEquiv,quotientBasisProductMap_apply]

@[simp]
theorem liftedQuotientBasis_inr (primitive : IsPrimitive a) (j : ι) :
    liftedQuotientBasis projection a kernel basis lifts projects primitive (.inr j) = lifts j := by
  simp [liftedQuotientBasis,Module.Basis.map_apply,Module.Basis.prod_apply,
    quotientBasisProductEquiv,quotientBasisProductMap_apply]

end ToricPower.FanSubdivision
end
