module

public import Recovery.Unimodular.WeakFano.Realization
public import Recovery.Unimodular.ProductLatticeCoordinates

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.WeightedPolytopes

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : N →+ V}

/-- The smooth projective realization lives in the original lattice and real
space. Coordinates transport the entire actual fan and integral dual polytope,
not merely the ray list or a combinatorial incidence table. -/
theorem smooth_projective_realization_original (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Finset N)
    (hU : IntegralRigidity.Uniform b (fun u : (U : Set N) => u.val))
    (hpos : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) (hzero : (0 : N) ∉ U) :
    ∃ Φ : Fan ι, Φ.IsComplete ∧ Φ.IsRegular ∧
      AllowedBlocks.HasRays ι (fun u : (U : Set N) => u.val) Φ ∧
      LiteralA3Projectivity.HasIntegralNormalFan Φ := by
  classical
  letI : FiniteDimensional ℝ V := hι.finiteDimensional
  let eN := LatticeCoordinates.latticeEquiv b
  let eR := LatticeCoordinates.realEquiv hι b
  let UC : Finset (Lattice n) := U.image eN
  have hUC : (UC : Set (Lattice n)) = eN '' (U : Set N) := Finset.coe_image
  have hUc : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (UC : Set (Lattice n)) => u.val) := by
    rw [hUC]
    exact (LatticeCoordinates.uniform_image_iff b (U : Set N)).2 hU
  have hpc : PointedCone.hull ℝ (embed '' (UC : Set (Lattice n))) = ⊤ := by
    have h := (LatticeCoordinates.hull_top_coordinates_iff hι b (U : Set N)).2 hpos
    have hemb : (LatticeCoordinates.coordinateEmbedding n : Lattice n → Ambient n) = embed := by
      ext x i
      rfl
    simpa only [hUC, hemb] using h
  have hzc : (0 : Lattice n) ∉ UC := by
    intro h
    obtain ⟨u, hu, he⟩ := Finset.mem_image.1 h
    have hz : u = 0 := eN.injective (he.trans eN.map_zero.symm)
    exact hzero (hz ▸ hu)
  obtain ⟨Φ, hΦc, hΦr, hΦu, hΦp⟩ := smooth_projective_realization UC hUc hpc hzc
  have hcomm : ∀ x : N, eR (ι x) = FanBridge.standardEmbedding n (eN x) :=
    LatticeCoordinates.coordinates_commute hι b
  have hback : ∀ x : Lattice n, eR.symm (FanBridge.standardEmbedding n x) =
      ι (eN.symm x) := FanTransport.compatible_inverse eN.toAddEquiv eR hcomm
  let Ψ := FanTransport.transport eN.toAddEquiv.symm eR.symm hback Φ
  let ε : FanEquiv Φ Ψ := FanTransport.equivalence eN.toAddEquiv.symm eR.symm hback Φ
  have hlabel : AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : (U : Set N) => eN u.val) Φ := by
    intro C
    rw [hΦu C]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu, he⟩ := Finset.mem_image.1 v.property
      exact ⟨⟨u, hu⟩, by simpa only [he] using hv⟩
    · rintro ⟨u, hu⟩
      exact ⟨⟨eN u.val, Finset.mem_image.2 ⟨u.val, u.property, rfl⟩⟩, hu⟩
  refine ⟨Ψ, ε.isComplete_iff.2 hΦc, ε.isRegular_iff.2 hΦr, ?_,
    LiteralA3Projectivity.integral_normalFan_of_equiv ε hΦp⟩
  apply FanTransport.hasRays_of_equiv ε (u := fun u : (U : Set N) => eN u.val)
    (u' := fun u : (U : Set N) => u.val) _ hlabel
  intro u
  change eR.symm (FanBridge.standardEmbedding n (eN u.val)) = ι u.val
  rw [hback, eN.symm_apply_apply]

/-- A coordinate basis is available for every actual integral lattice, so the
basis argument in the realization theorem adds no existence assumption. -/
theorem integral_lattice_has_coordinate_basis (hι : IsIntegralLattice ι) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ N) := by
  letI : Module.Free ℤ N := hι.free
  letI : Module.Finite ℤ N := hι.finite
  exact ⟨Module.finrank ℤ N, ⟨Module.finBasis ℤ N⟩⟩

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.smooth_projective_realization_original
#print axioms Unimodular.WeightedPolytopes.integral_lattice_has_coordinate_basis
#check Unimodular.WeightedPolytopes.smooth_projective_realization_original
