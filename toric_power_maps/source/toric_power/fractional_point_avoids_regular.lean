module

public import ToricPower.SimplicialFanCoordinates

/-!
# Fractional lattice points avoid every regular cone

The coefficients of an integral point in a regular cone are integers:
extend the primitive rays to an integral basis and evaluate its dual
characters. A nonzero integral point whose primitive coefficients are
all in `[0,1)` therefore belongs to no regular cone of the simplicial
fan. This is the relative-preservation part of regular subdivision.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped BigOperators Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- Any local primitive-ray representation of an integral point in a
regular cone has integral coefficients. -/
theorem regular_localRay_coefficient_integral (fan : Fan i) (τ : fan.cones)
    (regular : IsRegularCone i τ.val) (q : N) (c : ToricRay τ.val →₀ ℝ)
    (evaluates : localRayCombination fan τ c = i q) :
    ∀ ρ, ∃ z : ℤ, c ρ = (z : ℝ) := by
  letI := ToricRay.finite_of_fg (fan.isToricCone τ.property).fg
  letI := Fintype.ofFinite (ToricRay τ.val)
  obtain ⟨n, basis, rayIndex, basisExtends⟩ := regular.exists_basis
  have primitive (ν : ToricRay τ.val) :
      primitiveGenerator fan.lattice (fan.isToricCone τ.property) ν = basis (rayIndex ν) :=
    ((basisExtends.isPrimitiveGenerator_apply ν).eq_primitiveGenerator fan.lattice
      (fan.isToricCone τ.property)).symm
  intro ρ
  let character : N →+ ℤ := (basis.coord (rayIndex ρ)).toAddMonoidHom
  have generatorValue (ν : ToricRay τ.val) :
      fan.lattice.realCharacter character (fanRayRealVector fan (Fan.Ray.ofToricRay fan τ ν)) =
        if ν = ρ then 1 else 0 := by
    simp only [fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay, primitive,
      fan.lattice.realCharacter_apply]
    change ((basis.repr (basis (rayIndex ν)) (rayIndex ρ) : ℤ) : ℝ) = _
    rw [basis.repr_self, Finsupp.single_apply]
    by_cases equal : ν = ρ
    · simp only [equal, if_true, Int.cast_one]
    · simp only [equal, rayIndex.injective.ne equal, if_false, Int.cast_zero]
  have coefficient : fan.lattice.realCharacter character (localRayCombination fan τ c) = c ρ := by
    rw [localRayCombination, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype c (fun ν a => a • fanRayRealVector fan (Fan.Ray.ofToricRay fan τ ν))
        (fun _ => zero_smul _ _)]
    simp only [map_sum, map_smul, smul_eq_mul, generatorValue, mul_ite, mul_one, mul_zero]
    simp
  refine ⟨character q, ?_⟩
  rw [← coefficient, evaluates, fan.lattice.realCharacter_apply]

/-- The nonzero fractional point used in stellar subdivision cannot lie
in any old regular cone, including a lower-dimensional one. -/
theorem fractional_integral_point_avoids_regular (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (σ : fan.cones)
    (fullσ : Submodule.span ℝ (σ.val : Set V) = ⊤) (q : N)
    (nonzero : i q ≠ 0) (memberσ : i q ∈ σ.val)
    (bound : ∀ ρ, (simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
      (simplicial σ.val σ.property) fullσ).repr (i q) ρ < 1) :
    ∀ C ∈ fan.cones, IsRegularCone i C → i q ∉ C := by
  intro C hC regular memberC
  let τ : fan.cones := ⟨C, hC⟩
  obtain ⟨c, nonnegative, evaluates⟩ := localRay_nonnegative_representation fan τ memberC
  have bounded := fractional_profile_bounds_any_local fan simplicial σ τ fullσ memberσ
    bound c nonnegative evaluates
  have integral := regular_localRay_coefficient_integral fan τ regular q c evaluates
  have zero : c = 0 := by
    apply Finsupp.ext
    intro ρ
    obtain ⟨z, hz⟩ := integral ρ
    have nonnegativeInt : (0 : ℤ) ≤ z := by
      have h : (0 : ℝ) ≤ (z : ℝ) := hz ▸ nonnegative ρ
      exact_mod_cast h
    have smallInt : z < (1 : ℤ) := by
      have h : (z : ℝ) < 1 := hz ▸ bounded ρ
      exact_mod_cast h
    have zzero : z = 0 := by omega
    simpa only [Finsupp.zero_apply, zzero, Int.cast_zero] using hz
  rw [zero, map_zero] at evaluates
  exact nonzero evaluates.symm

end ToricPower.FanSubdivision
end
