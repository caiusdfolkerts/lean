module
public import shared_results.part018_tensor_koszul_coefficient_equiv
public import shared_results.part021

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulCoefficientPieces -/
section

/-!
# Actual coefficient-degree pieces under a Koszul algebra equivalence

The only input concerning a chosen degree is equality of the coefficient
submodules. The exterior factor is retained in full, and the equality of
the selected homology classes is derived from the literal DGA equivalence.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.TensorKoszulCoefficientEquiv
open Classical CommAlg FilteredTensorKoszul
open scoped TensorProduct
universe u
variable {K A B V : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [LinearOrder V]
  (e : A ≃ₐ[K] B) (W : Submodule K A) (P : B →ₗ[K] B)
  (hW : ∀ a, e a ∈ LinearMap.range P ↔ a ∈ W)

@[simp] theorem algebra_symm_tmul (b : B) (z : Simplicial.Ambient V K) :
    (algebra e).symm (b ⊗ₜ[K] z) = e.symm b ⊗ₜ[K] z := rfl

include hW in
theorem algebra_mem_tensorRange (z : A ⊗[K] Simplicial.Ambient V K)
    (hz : z ∈ coordinatePiece (fun _ : Finset V => W)) :
    algebra e z ∈ LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P) := by
  rw [← sum_coefficients z, map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [algebra_tmul]
  obtain ⟨b,hb⟩ := (hW (coefficient s z)).mpr ((mem_coordinatePiece _ z).mp hz s)
  refine ⟨b ⊗ₜ[K] Simplicial.basis s, ?_⟩
  rw [KoszulCoefficientProjection.tensor_tmul, hb]

include hW in
theorem algebra_symm_mem_coordinatePiece (z : B ⊗[K] Simplicial.Ambient V K)
    (hz : z ∈ LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P)) :
    (algebra e).symm z ∈ coordinatePiece (fun _ : Finset V => W) := by
  obtain ⟨x,rfl⟩ := hz
  rw [← sum_coefficients x, map_sum, map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [KoszulCoefficientProjection.tensor_tmul, algebra_symm_tmul]
  apply tmul_basis_mem_coordinatePiece
  apply (hW _).mp
  rw [e.apply_symm_apply]
  exact ⟨coefficient s x,rfl⟩

include hW in
theorem algebra_mem_tensorRange_iff (z : A ⊗[K] Simplicial.Ambient V K) :
    algebra e z ∈ LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P) ↔
      z ∈ coordinatePiece (fun _ : Finset V => W) := by
  constructor
  · intro hz
    simpa only [(algebra e).symm_apply_apply] using
      algebra_symm_mem_coordinatePiece e W P hW (algebra e z) hz
  · exact algebra_mem_tensorRange e W P hW z

variable (x : V → A) (y : V → B) (hxy : ∀ v, e (x v) = y v)

include hW in
/-- A coefficient-algebra identification preserving the selected
coefficient degree identifies its actual cycle classes as well. -/
theorem homologyEquiv_coordinateClasses :
    homologyEquiv e x y hxy ''
      (TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom
        (coordinatePiece (fun _ : Finset V => W)) =
      (TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := V) P)) :=
  ParityDifferential.homologyEquiv_classesFrom _ _ (algebra e)
    (differential e x y hxy) _ _ (algebra_mem_tensorRange_iff e W P hW)

end FourPapers.TensorKoszulCoefficientEquiv

end
end
end


end
