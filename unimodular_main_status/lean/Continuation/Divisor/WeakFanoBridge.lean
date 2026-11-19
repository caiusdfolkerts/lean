module

public import Continuation.Divisor.ReverseFanInterface
public import Continuation.Divisor.NefBigTheorems
public import Recovery.Unimodular.WeakFano.AnticanonicalSupport

/-!
# The weak-Fano realization and its actual anticanonical bundle

The constructed integral normal fan is passed to the scheme interface by
preserving every cone and every primitive generator. The unit-height
support functions from the original smooth presentation then prove
nefness of the actual dual canonical bundle. Section growth proves its
bigness, with the actual Krull dimension as exponent.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Unimodular.WeightedPolytopes.SmoothPresentation

open Set TauCeti.Toric AlgebraicGeometry
open Unimodular.FanInterfaces Unimodular.NefBig
open scoped Classical

variable {n : ℕ} (P : SmoothPresentation n)

/-- The same normal fan in the finite primitive-ray-set interface used by
the scheme construction. Every geometric cone is preserved. -/
def schemeFan : PaperVerification.ToricGeometry.SmoothCompleteFan n :=
  geometricFan P.normalFan P.normalFan_complete P.normalFan_regular

@[simp] theorem schemeFan_all_cones :
    dictionaryToricFan P.schemeFan = P.normalFan :=
  dictionaryToricFan_geometricFan P.normalFan P.normalFan_complete P.normalFan_regular

/-- There is no rescaling or deletion of the original normals. -/
theorem schemeFan_rays (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) (u : Lattice n) :
    u ∈ P.schemeFan.rays ↔ u ∈ P.normals := by
  rw [schemeFan, geometricFan_ray_iff]
  constructor
  · rintro ⟨C, hC, ρ, hρ⟩
    obtain ⟨v, hv⟩ := (P.mem_normalFan_cones C).mp hC
    have hρ' := (isPrimitiveGenerator_faceEmbedding hv ρ).mpr hρ
    obtain ⟨i, rfl⟩ := ConeBases.primitive_generator_eq_basis_of_eq
      P.normalFan.lattice (P.basis v) rfl _ hρ'
    exact P.basis_mem v i
  · intro hu
    obtain ⟨v, i, rfl⟩ := P.normals_occur hweak hzero u hu
    exact ConeBases.isRay_basis P.normalFan (P.basis v)
      (P.basisCone_mem_normalFan v) i

/-- The finite linear-support condition is verified for every actual
cone, including all nonmaximal faces. -/
theorem schemeFan_unitBoundary_support (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) :
    P.schemeFan.IsNef (fun _ => 1) := by
  intro s hs
  have hC : PaperVerification.ToricGeometry.latticeRayCone s ∈ P.normalFan.cones := by
    rw [← P.schemeFan_all_cones]
    exact ⟨s, hs, rfl⟩
  obtain ⟨v, hv⟩ := (P.mem_normalFan_cones _).mp hC
  refine ⟨P.unitDual v, ?_, ?_⟩
  · intro u hu
    have hu' : u ∈ P.normals := (P.schemeFan_rays hweak hzero u).mp
      (P.schemeFan.ray_mem_of_mem_cone hs hu)
    have hmem : embed u ∈ PaperVerification.ToricGeometry.latticeRayCone s := by
      rw [latticeRayCone_eq_hull_image]
      exact PointedCone.subset_hull ⟨u, hu, rfl⟩
    have hbas : embed u ∈ basisCone (P.basis v) := by
      rw [basisCone_eq_pointed]
      exact hv.le hmem
    exact (P.antiSupport_on_basis hweak v _ hbas).symm.trans
      (P.antiSupport_ray hweak hzero u hu')
  · intro u hu
    exact (P.unitDual_le_antiSupport v (embed u)).trans_eq
      (P.antiSupport_ray hweak hzero u ((P.schemeFan_rays hweak hzero u).mp hu))

/-- The geometric weak-Fano conclusion for the original constructed
normal fan, using the ordinary canonical bundle and ordinary sections. -/
theorem schemeFan_anticanonical_nef_and_big
    (k : Type u) [Field k] (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) :
    Smooth (P.schemeFan.fanScheme k ↘ Spec (CommRingCat.of k)) ∧
      topologicalKrullDim (P.schemeFan.fanScheme k) = n ∧
      IsNefOnCurves k (anticanonicalLineBundle P.schemeFan k) ∧
      IsBig k (anticanonicalLineBundle P.schemeFan k).obj :=
  ⟨fanScheme_smooth P.schemeFan k,
    P.schemeFan.fanScheme_topologicalKrullDim k P.schemeFan.isPure,
    anticanonical_nef_and_big_of_support P.schemeFan k
      (P.schemeFan_unitBoundary_support hweak hzero)⟩

end Unimodular.WeightedPolytopes.SmoothPresentation

namespace Unimodular.WeightedPolytopes

open Set TauCeti.Toric AlgebraicGeometry
open Unimodular.FanInterfaces Unimodular.NefBig

variable {n : ℕ}


#print axioms SmoothPresentation.schemeFan_rays
#print axioms SmoothPresentation.schemeFan_unitBoundary_support

end Unimodular.WeightedPolytopes
