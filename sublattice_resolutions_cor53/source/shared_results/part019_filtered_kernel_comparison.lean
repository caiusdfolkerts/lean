module
public import graph_foundation.part013
public import shared_results.part018

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredKernelComparison -/
section

/-! # Equality of kernel dimensions forces actual cycle lifting -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.FilteredHomology

open Classical

variable {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [FiniteDimensional K X] [FiniteDimensional K Y]
  (F : Filtration (K:=K) X) (G : Filtration (K:=K) Y)
  (f : X →ₗ[K] Y) (hf : Preserves F G f)

theorem gradeCyclesMap_surjective_of_lifts (hlift : LiftsCycles F G f) (n : ℕ) :
    Function.Surjective (gradeCyclesMap F G f hf n) := by
  intro x
  obtain ⟨y,hy⟩ := (lowerInLevel F n).mkQ_surjective x.val
  have hfy : f y.val ∈ G.level n := by
    have hx := x.property
    change gradeMap F G f hf n x.val = 0 at hx
    rw [← hy] at hx
    simp only [Submodule.mkQ_apply] at hx
    rw [gradeMap_mk] at hx
    have hmem := (Submodule.Quotient.mk_eq_zero (lowerInLevel G n)).mp hx
    change f y.val ∈ G.level n at hmem
    exact hmem
  obtain ⟨z,hz,hdz,herr⟩ := hlift n y.val y.property hfy
  let z' : cycleLevel F f (n+1) := ⟨⟨z,hdz⟩,hz⟩
  refine ⟨Submodule.Quotient.mk z',?_⟩
  apply Subtype.ext
  rw [gradeCyclesMap_mk]
  change (Submodule.Quotient.mk (⟨z,hz⟩ : F.level (n+1)) : Grade F n) = x.val
  rw [← hy]
  symm
  apply (Submodule.Quotient.eq (lowerInLevel F n)).mpr
  exact herr

theorem kernel_dimension_eq_of_liftsCycles (N : ℕ) (hN : F.level N=⊤)
    (hlift : LiftsCycles F G f) :
    Module.finrank K (LinearMap.ker f) =
      ∑ n∈Finset.range N,Module.finrank K (LinearMap.ker (gradeMap F G f hf n)) := by
  have hs := sum_finrank_grade (cyclesFiltration F f) N
  rw [cyclesFiltration_top F f N hN,finrank_top] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro n hn
  exact (LinearEquiv.ofBijective (gradeCyclesMap F G f hf n)
    ⟨gradeCyclesMap_injective F G f hf n,gradeCyclesMap_surjective_of_lifts F G f hf hlift n⟩).finrank_eq

include hf in
/-- Both maps have the same genuine source and target. The second is a
homogeneous model, and their actual coefficient discrepancy is strictly lower. -/
theorem liftsCycles_of_equal_kernel_strict_perturbation
    (f₀ : X →ₗ[K] Y) (hf₀ : Preserves F G f₀)
    (hstrict : ∀ n x,x∈F.level (n+1) → f x-f₀ x∈G.level n)
    (hlift₀ : LiftsCycles F G f₀) (N : ℕ) (hN : F.level N=⊤)
    (hdim : Module.finrank K (LinearMap.ker f)=Module.finrank K (LinearMap.ker f₀)) :
    LiftsCycles F G f := by
  apply liftsCycles_of_kernel_dimension_eq F G f hf N hN
  rw [hdim,kernel_dimension_eq_of_liftsCycles F G f₀ hf₀ N hN hlift₀]
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun h : Grade F n →ₗ[K] Grade G n => Module.finrank K (LinearMap.ker h))
    (gradeMap_eq_of_strict_difference F G f₀ f hf₀ hf
      (fun r x hx => by simpa only [neg_sub] using (G.level r).neg_mem (hstrict r x hx)) n)

end FourPapers.FilteredHomology

end
end
end


end
