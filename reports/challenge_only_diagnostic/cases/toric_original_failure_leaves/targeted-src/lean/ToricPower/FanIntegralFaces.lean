module

public import ToricPower.RegularConeIntegralSubfamily
public import ToricPower.FanCompleteSubspaces

/-! # Integral active faces of the actual fan

At a character-space point, the primitive rays on integral hyperplanes
select an actual face of each smooth cone. If these faces cover a normal
space, that space is complete and linear for the original fan, and its
affine annihilator slice is an integral translate.
-/

@[expose] public noncomputable section

open Set TauCeti.Toric

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular)
  (x : Module.Dual ℝ V)

/-- Precisely the primitive rays whose hyperplane through the point
has integral level. -/
def integralConeRays (σ : fan.cones) : Set (ToricRay σ.val) :=
  {ρ | ∃ z : ℤ,
    x (i (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ)) = (z : ℝ)}

def regularFanCone (σ : fan.cones) : IsRegularCone i σ.val :=
  Fan.isRegular_iff.mp regular σ.val σ.property

def fanIntegralFace (σ : fan.cones) : PointedCone ℝ V :=
  regularRaySubcone fan.lattice (regularFanCone fan regular σ) (integralConeRays fan x σ)

theorem fanIntegralFace_isFaceOf (σ : fan.cones) :
    (fanIntegralFace fan regular x σ).IsFaceOf σ.val :=
  regularRaySubcone_isFaceOf fan.lattice (regularFanCone fan regular σ) _

theorem fanIntegralFace_mem (σ : fan.cones) :
    fanIntegralFace fan regular x σ ∈ fan.cones :=
  fan.mem_of_isFaceOf σ.property (fanIntegralFace_isFaceOf fan regular x σ)

theorem fanIntegralFace_le_submodule (σ : fan.cones) (W : Submodule ℝ V)
    (contained : ∀ ρ ∈ integralConeRays fan x σ,
      i (primitiveGenerator fan.lattice (fan.isToricCone σ.property) ρ) ∈ W) :
    fanIntegralFace fan regular x σ ≤ (W : PointedCone ℝ V) :=
  regularRaySubcone_le_submodule fan.lattice (regularFanCone fan regular σ) _ W contained

/-- A cover by these actual faces gives the complete-subfan property
and therefore the paper's full linearity condition. -/
theorem fanIntegralFace_cover_complete (W : Submodule ℝ V)
    (contained : ∀ σ, fanIntegralFace fan regular x σ ≤ (W : PointedCone ℝ V))
    (cover : ∀ v ∈ W, ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular x σ) :
    W ∈ fanCompleteSubspaces fan := by
  intro v hv
  obtain ⟨σ,hσ⟩ := cover v hv
  exact ⟨_,fanIntegralFace_mem fan regular x σ,contained σ,hσ⟩

/-- Full normal coverage supplies one actual integral lattice translate
of the entire affine slice. The original fan need not be complete. -/
theorem fanIntegralFace_cover_integralSlice (W : Submodule ℝ V)
    (contained : ∀ σ, fanIntegralFace fan regular x σ ≤ (W : PointedCone ℝ V))
    (cover : ∀ v ∈ W, ∃ σ : fan.cones, v ∈ fanIntegralFace fan regular x σ) :
    ∃ m : N →+ ℤ, ∀ y : Module.Dual ℝ V,
      y-x ∈ W.dualAnnihilator ↔ y-fan.lattice.realCharacter m ∈ W.dualAnnihilator := by
  letI := fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V :=
    NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  obtain ⟨σ,spans⟩ := exists_cone_span_eq_of_finite_cover W
    (fanIntegralFace fan regular x) contained cover
  exact regularRaySubcone_integralAffineSlice fan.lattice (regularFanCone fan regular σ)
    (integralConeRays fan x σ) W spans x (fun _ h => h)

end ToricPower

end
