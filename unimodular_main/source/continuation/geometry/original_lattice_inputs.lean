module

public import Continuation.Geometry.OriginalLatticeFan

@[expose] public section

/-!
# Exact coordinate transport of the realization inputs

The full maximal-minor predicate and the actual positive hull are
preserved.  The image set is indexed by its own elements, so no repeated
selection, original label, or determinant quantifier is lost.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TauCeti.Toric PaperVerification.ToricGeometry
open scoped Classical NNReal

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

private theorem basis_map_coordinates :
    b.map b.equivFun = Pi.basisFun ℤ (Fin n) := by
  ext i j
  simp [Module.Basis.map_apply, Module.Basis.equivFun_self,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- Every full determinant is unchanged, including repeated columns. -/
theorem determinant_in_coordinates (v : Fin n → N) :
    (Pi.basisFun ℤ (Fin n)).det (b.equivFun ∘ v) = b.det v := by
  rw [← basis_map_coordinates b, Module.Basis.det_map]
  congr 1
  funext i
  exact b.equivFun.symm_apply_apply (v i)

/-- The complete uniform-unimodularity assertion, with the literal image
set as labels, is equivalent to the assertion on the original set. -/
theorem uniform_coordinate_image_iff (U : Finset N) :
    Unimodular.IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (fun u : (U.image b.equivFun : Set (Lattice n)) => u.val) ↔
      Unimodular.IntegralRigidity.Uniform b
        (fun u : (U : Set N) => u.val) := by
  constructor
  · intro h a
    have ha := h (fun i => ⟨b.equivFun (a i).val,
      Finset.mem_image.mpr ⟨(a i).val, (a i).property, rfl⟩⟩)
    change |(Pi.basisFun ℤ (Fin n)).det
      (b.equivFun ∘ (fun i => (a i).val))| ≤ 1 at ha
    rw [determinant_in_coordinates] at ha
    exact ha
  · intro h a
    choose v hv he using fun i => Finset.mem_image.mp (a i).property
    have ha := h (fun i => ⟨v i, hv i⟩)
    have heq : (fun i => (a i).val) = b.equivFun ∘ v := by
      funext i
      exact (he i).symm
    change |(Pi.basisFun ℤ (Fin n)).det (fun i => (a i).val)| ≤ 1
    rw [heq, determinant_in_coordinates]
    exact ha

/-- The actual positive real cone, not merely the linear span, is the
coordinate image of the original one. -/
theorem positiveHull_coordinates (U : Set N) :
    (PointedCone.hull ℝ (ι '' U)).map (realCoordinates b hi).toLinearMap =
      PointedCone.hull ℝ (PaperVerification.ToricGeometry.embed n ''
        (b.equivFun '' U)) := by
  change Submodule.map ((realCoordinates b hi).toLinearMap.restrictScalars ℝ≥0)
    (Submodule.span ℝ≥0 (ι '' U)) = _
  rw [Submodule.map_span]
  change PointedCone.hull ℝ (realCoordinates b hi '' (ι '' U)) = _
  simp only [Set.image_image]
  congr 1
  apply congrArg (fun f : N → Ambient n => f '' U)
  funext x
  exact realCoordinates_lattice b hi x

include hi in
/-- Positive spanning in the given original real vector space supplies
exactly the coordinate positive-spanning hypothesis of the construction. -/
theorem coordinate_image_positiveHull_top (U : Finset N)
    (hU : PointedCone.hull ℝ (ι '' (U : Set N)) = ⊤) :
    PointedCone.hull ℝ (PaperVerification.ToricGeometry.embed n ''
      (U.image b.equivFun : Set (Lattice n))) = ⊤ := by
  rw [Finset.coe_image, ← positiveHull_coordinates b hi (U : Set N), hU]
  change Submodule.map ((realCoordinates b hi).toLinearMap.restrictScalars ℝ≥0) ⊤ = ⊤
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (realCoordinates b hi).surjective

/-- Nonzero original rays stay nonzero with their original signs. -/
theorem zero_not_mem_coordinate_image (U : Finset N) (hU : (0 : N) ∉ U) :
    (0 : Lattice n) ∉ U.image b.equivFun := by
  intro h
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp h
  have hz : u = 0 := b.equivFun.injective (he.trans (map_zero b.equivFun).symm)
  exact hU (hz ▸ hu)

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.uniform_coordinate_image_iff
#print axioms PaperVerification.OriginalLatticeCharts.coordinate_image_positiveHull_top
