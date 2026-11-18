module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Equiv
import all TauCeti.Geometry.Toric.Algebraic.Fan.Equiv

public import Recovery.Unimodular.WeakFano.CanonicalSeed
public import Recovery.Unimodular.PriorExtensions.NormalFanCoordinateTransport
public import Recovery.Unimodular.ProductLatticeCoordinates
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set TauCeti.Toric
open scoped NNReal BigOperators

namespace Unimodular.OriginalSeedGeometry
open NormalFanCoordinateTransport

section Linear
variable {V V' : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup V'] [Module ℝ V']

/-- The ordinary polar in the actual real dual, with no coordinate choice. -/
def polar (P : Set V) : Set (Module.Dual ℝ V) :=
  {f | ∀ x ∈ P, f x ≤ 1}

/-- The polar uses contragredient transport of genuine linear forms. -/
theorem polar_image (e : V ≃ₗ[ℝ] V') (P : Set V) :
    polar (e '' P) = dualTransport e '' polar P := by
  ext f
  obtain ⟨g, rfl⟩ := (dualTransport e).surjective f
  rw [(dualTransport e).injective.mem_set_image]
  constructor
  · intro h x hx
    have hh := h (e x) ⟨x, hx, rfl⟩
    simpa only [dualTransport_apply, LinearEquiv.symm_apply_apply] using hh
  · rintro h _ ⟨x, hx, rfl⟩
    simpa only [dualTransport_apply, LinearEquiv.symm_apply_apply] using h x hx

/-- Extreme faces, including the empty face, are carried by the actual
linear equivalence. -/
theorem extreme_image (e : V ≃ₗ[ℝ] V') {P F : Set V}
    (h : IsExtreme ℝ P F) : IsExtreme ℝ (e '' P) (e '' F) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hs
  have hs' : z ∈ openSegment ℝ x y := by
    have he : e '' openSegment ℝ x y = openSegment ℝ (e x) (e y) :=
      image_openSegment ℝ e.toLinearMap.toAffineMap x y
    rw [← he] at hs
    exact e.injective.mem_set_image.mp hs
  exact ⟨x, h.left_mem_of_mem_openSegment hx hy hz hs', rfl⟩

theorem extreme_image_iff (e : V ≃ₗ[ℝ] V') (P F : Set V) :
    IsExtreme ℝ (e '' P) (e '' F) ↔ IsExtreme ℝ P F := by
  constructor
  · intro h
    have hh := extreme_image e.symm h
    simpa only [Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id'] using hh
  · exact extreme_image e

theorem map_hull (e : V ≃ₗ[ℝ] V') (F : Set V) :
    (PointedCone.hull ℝ F).map e.toLinearMap = PointedCone.hull ℝ (e '' F) := by
  change Submodule.map (e.toLinearMap.restrictScalars ℝ≥0) (Submodule.span ℝ≥0 F) = _
  rw [Submodule.map_span]
  rfl

end Linear

section Coordinates
variable {n : ℕ}

/-- The standard pairing identifies real coordinate vectors with genuine
linear forms; its action is the ordinary dot product. -/
abbrev coordinateDual : Ambient n ≃ₗ[ℝ] Module.Dual ℝ (Ambient n) :=
  dotProductEquiv ℝ (Fin n)

@[simp] theorem coordinateDual_apply (z x : Ambient n) :
    coordinateDual z x = realPairing z x := rfl

theorem coordinate_polar (P : Set (Ambient n)) :
    polar P = coordinateDual '' realPolar P := by
  ext f
  obtain ⟨z, rfl⟩ := coordinateDual.surjective f
  rw [coordinateDual.injective.mem_set_image]
  simp only [polar, realPolar, Set.mem_ofPred_eq, coordinateDual_apply, realPairing_comm]

theorem coordinate_normalCone (P : Set (Ambient n)) (z : Ambient n) :
    NormalFanSupport.normalCone (coordinateDual '' P) (coordinateDual z) =
      GenericProjectivity.normalCone P z := by
  ext x
  constructor
  · intro h q hq
    exact h (coordinateDual q) ⟨q, hq, rfl⟩
  · rintro h _ ⟨q, hq, rfl⟩
    exact h q hq

theorem coordinateDual_integral (z x : Lattice n) :
    coordinateDual (embed z) (embed x) = ((∑ i, z i * x i : ℤ) : ℝ) := by
  simp only [coordinateDual_apply, realPairing, embed, Int.cast_sum, Int.cast_mul]

end Coordinates

section Fans
variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ι : N →+ V} {ι' : N' →+ V'} {Φ : Fan ι} {Ψ : Fan ι'}

/-- Every cone and every proper convex extreme face are transported together;
there is no selected-vertex or maximal-cone restriction. -/
theorem radial_fan_transport (e : FanEquiv Φ Ψ) (P : Set V)
    (hΦ : ∀ C, C ∈ Φ.cones ↔ ∃ F : Set V, Convex ℝ F ∧
      IsExtreme ℝ P F ∧ F ≠ P ∧ C = PointedCone.hull ℝ F) :
    ∀ D, D ∈ Ψ.cones ↔ ∃ F : Set V', Convex ℝ F ∧
      IsExtreme ℝ (e.realEquiv '' P) F ∧ F ≠ e.realEquiv '' P ∧
      D = PointedCone.hull ℝ F := by
  intro D
  constructor
  · intro hD
    obtain ⟨F, hc, hf, hp, he⟩ := (hΦ _).mp ((e.symm.map_mem D).mpr hD)
    change D.map e.realEquiv.symm.toLinearMap = PointedCone.hull ℝ F at he
    refine ⟨e.realEquiv '' F, hc.linear_image e.realEquiv.toLinearMap,
      extreme_image e.realEquiv hf, ?_, ?_⟩
    · exact fun h => hp (e.realEquiv.injective.image_injective h)
    · calc
        D = (D.map e.realEquiv.symm.toLinearMap).map e.realEquiv.toLinearMap :=
          (FanTransport.map_inverse_rev e.realEquiv D).symm
        _ = (PointedCone.hull ℝ F).map e.realEquiv.toLinearMap := by rw [he]
        _ = _ := map_hull e.realEquiv F
  · rintro ⟨F, hc, hf, hp, rfl⟩
    let E := e.realEquiv.symm '' F
    have hE : e.realEquiv '' E = F := by
      simp only [E, Set.image_image, LinearEquiv.apply_symm_apply, Set.image_id']
    have hext : IsExtreme ℝ P E := by
      have hh := extreme_image e.realEquiv.symm hf
      simpa only [Set.image_image, LinearEquiv.symm_apply_apply, Set.image_id'] using hh
    have hne : E ≠ P := by
      intro hh
      exact hp (hE.symm.trans (congrArg (fun S => e.realEquiv '' S) hh))
    have hC : PointedCone.hull ℝ E ∈ Φ.cones := (hΦ _).mpr
      ⟨E, hc.linear_image e.realEquiv.symm.toLinearMap, hext, hne, rfl⟩
    have hm := (e.map_mem (PointedCone.hull ℝ E)).mpr hC
    simpa only [map_hull, hE] using hm

/-- The whole normal fan is transported along the same lattice-compatible
map as its polar. -/
theorem polar_normal_fan_transport (e : FanEquiv Φ Ψ) (P : Set V)
    (hΦ : ∀ C, C ∈ Φ.cones ↔ ∃ f ∈ polar P,
      C = NormalFanSupport.normalCone (polar P) f) :
    ∀ D, D ∈ Ψ.cones ↔ ∃ f ∈ polar (e.realEquiv '' P),
      D = NormalFanSupport.normalCone (polar (e.realEquiv '' P)) f := by
  intro D
  rw [polar_image]
  constructor
  · intro hD
    obtain ⟨f, hf, he⟩ := (hΦ _).mp ((e.symm.map_mem D).mpr hD)
    change D.map e.realEquiv.symm.toLinearMap = NormalFanSupport.normalCone (polar P) f at he
    refine ⟨dualTransport e.realEquiv f, ⟨f, hf, rfl⟩, ?_⟩
    calc
      D = (D.map e.realEquiv.symm.toLinearMap).map e.realEquiv.toLinearMap :=
        (FanTransport.map_inverse_rev e.realEquiv D).symm
      _ = (NormalFanSupport.normalCone (polar P) f).map e.realEquiv.toLinearMap := by rw [he]
      _ = _ := map_normalCone e.realEquiv _ _
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [← map_normalCone]
    exact (e.map_mem _).mpr ((hΦ _).mpr ⟨f, hf, rfl⟩)

end Fans
end Unimodular.OriginalSeedGeometry

#print axioms Unimodular.OriginalSeedGeometry.polar_image
#print axioms Unimodular.OriginalSeedGeometry.extreme_image_iff
#print axioms Unimodular.OriginalSeedGeometry.coordinate_polar
#print axioms Unimodular.OriginalSeedGeometry.radial_fan_transport
#print axioms Unimodular.OriginalSeedGeometry.polar_normal_fan_transport
#check Unimodular.OriginalSeedGeometry.polar_normal_fan_transport
