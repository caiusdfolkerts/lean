module

public import Continuation.Geometry.OriginalLatticeFan
public import TauCeti.Geometry.Toric.Algebraic.Fan.Subdivision

@[expose] public section

/-!
# Transporting the entire seed and subdivision to the original lattice

The seed may be singular.  Its complete cone set is transported by the
same integral and real equivalences as the smooth realization.  The
subdivision relation is proved directly on all cones and both supports.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

private theorem map_inverse {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (C : PointedCone ℝ A) :
    (C.map e.toLinearMap).map e.symm.toLinearMap = C := by
  rw [PointedCone.map_map]
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [h, PointedCone.map_id]

private theorem map_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) :
    Function.Injective (fun C : PointedCone ℝ A => C.map e.toLinearMap) := by
  intro C D h
  have he := congrArg (fun K => K.map e.symm.toLinearMap) h
  simpa only [map_inverse] using he

private theorem map_inf {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℝ A] [Module ℝ B] (e : A ≃ₗ[ℝ] B) (C D : PointedCone ℝ A) :
    (C ⊓ D).map e.toLinearMap = C.map e.toLinearMap ⊓ D.map e.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyD⟩, rfl⟩
    exact ⟨⟨y, hyC, rfl⟩, ⟨y, hyD, rfl⟩⟩
  · rintro ⟨⟨y, hy, hey⟩, ⟨z, hz, hez⟩⟩
    have hyz : y = z := e.injective (hey.trans hez.symm)
    exact ⟨y, ⟨hy, hyz.symm ▸ hz⟩, hey⟩

/-- The whole original-lattice fan, allowing nonsimplicial seed cones. -/
def transportFan (Φ : Fan (Unimodular.FanBridge.standardEmbedding n)) : Fan ι where
  lattice := hi
  cones := (fun C : PointedCone ℝ (Ambient n) =>
    C.map (realCoordinates b hi).symm.toLinearMap) '' Φ.cones
  finite_cones := Φ.finite_cones.image _
  isToricCone := by
    rintro D ⟨C, hC, rfl⟩
    exact (Φ.isToricCone hC).map (f := b.equivFun.symm.toAddMonoidHom)
      (fun v => realCoordinates_symm_lattice b hi v)
      (realCoordinates b hi).symm.injective
  mem_of_isFaceOf := by
    rintro D K ⟨C, hC, rfl⟩ hK
    have hk := hK.map (realCoordinates b hi).toLinearMap (realCoordinates b hi).injective
    change (K.map (realCoordinates b hi).toLinearMap).IsFaceOf
      ((C.map (realCoordinates b hi).symm.toLinearMap).map
        (realCoordinates b hi).toLinearMap) at hk
    have hback : (C.map (realCoordinates b hi).symm.toLinearMap).map
        (realCoordinates b hi).toLinearMap = C := by
      simpa only [LinearEquiv.symm_symm] using
        map_inverse (realCoordinates b hi).symm C
    rw [hback] at hk
    exact ⟨K.map (realCoordinates b hi).toLinearMap,
      Φ.mem_of_isFaceOf hC hk, map_inverse (realCoordinates b hi) K⟩
  inf_isFaceOf_left := by
    rintro C' D' ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    rw [← map_inf]
    exact (Φ.inf_isFaceOf_left hC hD).map
      (realCoordinates b hi).symm.toLinearMap (realCoordinates b hi).symm.injective

/-- The integral lattice, real embedding and every cone are identified. -/
def transportFanEquiv (Φ : Fan (Unimodular.FanBridge.standardEmbedding n)) :
    FanEquiv Φ (transportFan b hi Φ) where
  latticeEquiv := b.equivFun.symm.toAddEquiv
  realEquiv := (realCoordinates b hi).symm
  map_lattice v := realCoordinates_symm_lattice b hi v
  map_mem C := by
    constructor
    · rintro ⟨D, hD, he⟩
      exact map_injective (realCoordinates b hi).symm he ▸ hD
    · intro hC
      exact ⟨C, hC, rfl⟩

theorem transportFan_complete_iff (Φ : Fan (Unimodular.FanBridge.standardEmbedding n)) :
    (transportFan b hi Φ).IsComplete ↔ Φ.IsComplete :=
  (transportFanEquiv b hi Φ).isComplete_iff

/-- This agrees with the fan already attached to the actual original atlas. -/
theorem transportFan_dictionary (F : SmoothCompleteFan n) :
    transportFan b hi (Unimodular.FanInterfaces.dictionaryToricFan F) =
      originalFan b hi F := by
  apply Fan.ext
  rfl

/-- Supports are transported literally; no completeness is assumed. -/
theorem mem_support_transportFan_iff
    (Φ : Fan (Unimodular.FanBridge.standardEmbedding n)) (x : V) :
    x ∈ (transportFan b hi Φ).support ↔ realCoordinates b hi x ∈ Φ.support := by
  rw [Fan.mem_support, Fan.mem_support]
  constructor
  · rintro ⟨D, ⟨C, hC, rfl⟩, hx⟩
    change ∃ y ∈ C, (realCoordinates b hi).symm y = x at hx
    obtain ⟨y, hy, he⟩ := hx
    refine ⟨C, hC, ?_⟩
    rw [← he, LinearEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨C, hC, hx⟩
    exact ⟨C.map (realCoordinates b hi).symm.toLinearMap, ⟨C, hC, rfl⟩,
      realCoordinates b hi x, hx, (realCoordinates b hi).symm_apply_apply x⟩

/-- Every cone inclusion and the support equality of a subdivision survive
in the original lattice, even when the seed is nonsimplicial. -/
theorem transportFan_subdivision
    {Φ Ψ : Fan (Unimodular.FanBridge.standardEmbedding n)} (h : Φ.IsSubdivision Ψ) :
    (transportFan b hi Φ).IsSubdivision (transportFan b hi Ψ) where
  exists_cone_le := by
    rintro D ⟨C, hC, rfl⟩
    obtain ⟨K, hK, hCK⟩ := h.exists_cone_le hC
    refine ⟨K.map (realCoordinates b hi).symm.toLinearMap, ⟨K, hK, rfl⟩, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hCK hy, rfl⟩
  support_eq := by
    ext x
    rw [mem_support_transportFan_iff, mem_support_transportFan_iff, h.support_eq]

theorem originalFan_subdivision
    (F : SmoothCompleteFan n) {Ψ : Fan (Unimodular.FanBridge.standardEmbedding n)}
    (h : (Unimodular.FanInterfaces.dictionaryToricFan F).IsSubdivision Ψ) :
    (originalFan b hi F).IsSubdivision (transportFan b hi Ψ) := by
  rw [← transportFan_dictionary]
  exact transportFan_subdivision b hi h

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.transportFan_subdivision
#print axioms PaperVerification.OriginalLatticeCharts.originalFan_subdivision
