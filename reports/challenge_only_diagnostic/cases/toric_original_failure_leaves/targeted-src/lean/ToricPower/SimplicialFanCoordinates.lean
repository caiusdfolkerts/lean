module

public import ToricPower.SimplicialPrimitiveBasis
public import ToricPower.FanRayCoordinates

/-!
# Primitive coordinates across a simplicial fan

Nonnegative primitive-ray coordinates agree across every common face.
They are recorded in the original global ray indexing, so coordinate
bounds from one cone transfer literally to every other cone containing
the point. Smoothness is not needed for this compatibility.
-/

@[expose] public noncomputable section
open TauCeti.Toric
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

theorem simplicial_fanRayRealVector_linearIndepOn (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (σ : fan.cones) :
    LinearIndepOn ℝ (fanRayRealVector fan) {ρ | ρ.toCone ≤ σ} := by
  have independent : LinearIndependent ℝ
      (fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ)) := by
    simpa only [fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay] using
      simplicial_primitiveGenerator_linearIndependent fan.lattice (fan.isToricCone σ.property)
        (simplicial σ.val σ.property)
  exact independent.comp (fanConeRayEquiv fan σ).symm (fanConeRayEquiv fan σ).symm.injective

theorem simplicial_fanRayProfile_unique (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial)
    {x : V} {c d : fan.Ray →₀ ℝ}
    (hc : IsFanRayProfile fan x c) (hd : IsFanRayProfile fan x d) : c = d := by
  obtain ⟨cnonnegative, σ, csupport, cevaluate⟩ := hc
  obtain ⟨dnonnegative, τ, dsupport, devaluate⟩ := hd
  have xσ : x ∈ σ.val := cevaluate ▸ rayProfileCombination_mem fan σ c cnonnegative csupport
  have xτ : x ∈ τ.val := devaluate ▸ rayProfileCombination_mem fan τ d dnonnegative dsupport
  have dsupportσ : rayProfileSupported fan σ d := by
    intro ρ hρ
    exact (rayProfile_supported_in_face fan τ (τ.val ⊓ σ.val)
      (fan.inf_isFaceOf_left τ.property σ.property) d dnonnegative dsupport
      (by rw [devaluate]; exact ⟨xτ, xσ⟩) ρ hρ).trans inf_le_right
  apply (linearIndepOn_iffₛ.mp (simplicial_fanRayRealVector_linearIndepOn fan simplicial σ))
    c ((Finsupp.mem_supported _ _).mpr csupport)
    d ((Finsupp.mem_supported _ _).mpr dsupportσ)
  exact cevaluate.trans devaluate.symm

theorem extendConeRayProfile_lt_one (fan : Fan i) (σ : fan.cones)
    (c : ToricRay σ.val →₀ ℝ) (bound : ∀ ρ, c ρ < 1) :
    ∀ ρ, extendConeRayProfile fan σ c ρ < 1 := by
  intro ρ
  by_cases member : ρ ∈ (extendConeRayProfile fan σ c).support
  · obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support member)
    change Finsupp.mapDomain (Fan.Ray.ofToricRay fan σ) c (Fan.Ray.ofToricRay fan σ τ) < 1
    rw [Finsupp.mapDomain_apply_of_injective (fanConeRay_injective fan σ)]
    exact bound τ
  · rw [Finsupp.notMem_support_iff.mp member]
    exact zero_lt_one

theorem fullCone_primitiveBasis_profile (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (σ : fan.cones)
    (full : Submodule.span ℝ (σ.val : Set V) = ⊤) {x : V} (member : x ∈ σ.val) :
    IsFanRayProfile fan x (extendConeRayProfile fan σ
      ((simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
        (simplicial σ.val σ.property) full).repr x)) := by
  let basis := simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
    (simplicial σ.val σ.property) full
  have nonnegative := (mem_simplicialCone_iff_coordinates_nonnegative fan.lattice
    (fan.isToricCone σ.property) (simplicial σ.val σ.property) full x).mp member
  refine ⟨extendConeRayProfile_nonnegative fan σ (basis.repr x) nonnegative,
    σ, extendConeRayProfile_supported fan σ (basis.repr x), ?_⟩
  rw [extendConeRayProfile_evaluate]
  have family : (fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ)) =
      (basis : ToricRay σ.val → V) := by
    funext ρ
    simp only [fanRayRealVector, fanRayPrimitiveGenerator_ofToricRay,
      basis, simplicialPrimitiveBasis_apply]
  change Finsupp.linearCombination ℝ
    (fun ρ : ToricRay σ.val => fanRayRealVector fan (Fan.Ray.ofToricRay fan σ ρ)) (basis.repr x) = x
  rw [family]
  exact basis.linearCombination_repr x

/-- Fractional primitive coordinates in one full-dimensional cone give
the same upper bound in every full-dimensional cone containing the point. -/
theorem primitive_coordinates_lt_one_transfer (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (σ τ : fan.cones)
    (fullσ : Submodule.span ℝ (σ.val : Set V) = ⊤)
    (fullτ : Submodule.span ℝ (τ.val : Set V) = ⊤)
    {x : V} (memberσ : x ∈ σ.val) (memberτ : x ∈ τ.val)
    (bound : ∀ ρ, (simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
      (simplicial σ.val σ.property) fullσ).repr x ρ < 1) :
    ∀ ρ, (simplicialPrimitiveBasis fan.lattice (fan.isToricCone τ.property)
      (simplicial τ.val τ.property) fullτ).repr x ρ < 1 := by
  let bσ := simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
    (simplicial σ.val σ.property) fullσ
  let bτ := simplicialPrimitiveBasis fan.lattice (fan.isToricCone τ.property)
    (simplicial τ.val τ.property) fullτ
  have equal := simplicial_fanRayProfile_unique fan simplicial
    (fullCone_primitiveBasis_profile fan simplicial σ fullσ memberσ)
    (fullCone_primitiveBasis_profile fan simplicial τ fullτ memberτ)
  intro ρ
  have bounded := extendConeRayProfile_lt_one fan σ (bσ.repr x) bound (Fan.Ray.ofToricRay fan τ ρ)
  rw [equal] at bounded
  change Finsupp.mapDomain (Fan.Ray.ofToricRay fan τ) (bτ.repr x) (Fan.Ray.ofToricRay fan τ ρ) < 1 at bounded
  rwa [Finsupp.mapDomain_apply_of_injective (fanConeRay_injective fan τ)] at bounded

/-- The same transfer also applies to any nonnegative local profile,
including one in a lower-dimensional regular cone. -/
theorem fractional_profile_bounds_any_local (fan : Fan i)
    (simplicial : ∀ C ∈ fan.cones, C.IsSimplicial) (σ τ : fan.cones)
    (fullσ : Submodule.span ℝ (σ.val : Set V) = ⊤)
    {x : V} (memberσ : x ∈ σ.val)
    (bound : ∀ ρ, (simplicialPrimitiveBasis fan.lattice (fan.isToricCone σ.property)
      (simplicial σ.val σ.property) fullσ).repr x ρ < 1)
    (c : ToricRay τ.val →₀ ℝ) (nonnegative : ∀ ρ, 0 ≤ c ρ)
    (evaluates : localRayCombination fan τ c = x) : ∀ ρ, c ρ < 1 := by
  have profile : IsFanRayProfile fan x (extendConeRayProfile fan τ c) :=
    ⟨extendConeRayProfile_nonnegative fan τ c nonnegative, τ,
      extendConeRayProfile_supported fan τ c, (extendConeRayProfile_evaluate fan τ c).trans evaluates⟩
  have equal := simplicial_fanRayProfile_unique fan simplicial
    (fullCone_primitiveBasis_profile fan simplicial σ fullσ memberσ) profile
  intro ρ
  have bounded := extendConeRayProfile_lt_one fan σ _ bound (Fan.Ray.ofToricRay fan τ ρ)
  rw [equal] at bounded
  change Finsupp.mapDomain (Fan.Ray.ofToricRay fan τ) c (Fan.Ray.ofToricRay fan τ ρ) < 1 at bounded
  rwa [Finsupp.mapDomain_apply_of_injective (fanConeRay_injective fan τ)] at bounded

end ToricPower.FanSubdivision
end
