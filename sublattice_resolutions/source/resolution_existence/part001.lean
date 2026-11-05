module
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.ProjectiveComplexHomologyComparison -/
section

/-!
# Two literal presentations of homology

The splitting construction retains every chain in degree zero as a cycle.
Equivalently, its outgoing map there is the zero map. This file identifies
its quotient of cycles by boundaries with the three-term kernel/image
quotient used by the filtered and fine Koszul comparisons. The equivalence
preserves the underlying cycle representative.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.ProjectiveComplexSplitting

variable {R : Type*} [CommRing R]
  (C : ℕ → Type*) [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
  (d : ∀ p, C (p + 1) →ₗ[R] C p)
  (dd : ∀ p, (d p).comp (d (p + 1)) = 0)

/-- The same cycle, with its zero-degree membership expressed as a kernel
condition rather than membership in the top submodule. -/
def cyclesEquivKernel (p : ℕ) : cycles C d p ≃ₗ[R] LinearMap.ker (previous C d p) where
  toFun x := ⟨x.val, by
    cases p with
    | zero => rfl
    | succ p => exact x.property⟩
  invFun x := ⟨x.val, by
    cases p with
    | zero => trivial
    | succ p => exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cyclesEquivKernel_val (p : ℕ) (x : cycles C d p) :
    (cyclesEquivKernel C d p x).val = x.val := rfl

theorem cyclesEquivKernel_boundaries (p : ℕ) :
    (boundaries C d dd p).map (cyclesEquivKernel C d p).toLinearMap =
      LinearMap.range (FilteredHomology.boundaryMap (d p) (previous C d p)
        (previous_comp C d dd p)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨toCycles C d dd p y, ⟨y, rfl⟩, ?_⟩
    exact Subtype.ext rfl

/-- A representative-preserving equivalence between the actual homology
quotients. It has no projectivity or finiteness hypotheses. -/
def homologyEquivKernelQuotient (p : ℕ) :
    Homology C d dd p ≃ₗ[R]
      FilteredHomology.Homology (d p) (previous C d p) (previous_comp C d dd p) :=
  Submodule.Quotient.equiv _ _ (cyclesEquivKernel C d p)
    (cyclesEquivKernel_boundaries C d dd p)

@[simp] theorem homologyEquivKernelQuotient_mk (p : ℕ) (x : cycles C d p) :
    homologyEquivKernelQuotient C d dd p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cyclesEquivKernel C d p x) := rfl

end FourPapers.ProjectiveComplexSplitting

#print axioms FourPapers.ProjectiveComplexSplitting.homologyEquivKernelQuotient
#print axioms FourPapers.ProjectiveComplexSplitting.homologyEquivKernelQuotient_mk

end
end
end

end
