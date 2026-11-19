module

public import ToricPower.ModuleExtConnecting
public import ToricPower.InjectiveModuleFlasque
public import ToricPower.Cohomology.SchemeFlasque

/-! The actual degree-one Ext / ordinary sheaf cohomology comparison, proved by comparing the two quotient kernels. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.Abelian MonoidalCategory Opposite TopologicalSpace

namespace ToricPower

universe u

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

local instance moduleOneHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Degree-one comparison, using the same actual injective cokernel
sequence and the two actual connecting homomorphisms. -/
def moduleUnitExtOneCohomologyOfShortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Injective S.X₂] :
    Ext.{u} (𝟙_ X.Modules) S.X₁ 1 ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology S.X₁ 1 := by
  let e := moduleUnitExtZeroCohomology k X S.X₃
  let dE := moduleExtConnecting k X hS (𝟙_ X.Modules) 0
  let dH := (TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδBaseLinear k X hS 0 1 rfl).comp e.toLinearMap
  have hE : Function.Surjective dE := moduleExtConnecting_surjective k X hS _ 0
  have hH : Function.Surjective dH := by
    intro y
    obtain ⟨z, hz⟩ := TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδ_surjective_of_isFlasque hS 0 1 rfl y
    exact ⟨e.symm z, by simpa [dH] using hz⟩
  have hker : LinearMap.ker dE = LinearMap.ker dH := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₃ (𝟙_ X.Modules) hS x rfl hx
      change TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyδBaseLinear k X hS 0 1 rfl
        (moduleUnitExtZeroCohomology k X S.X₃
          (z.comp (Ext.mk₀ S.g) (add_zero 0))) = 0
      rw [moduleUnitExtZeroCohomology_naturality]
      exact (TauCeti.AlgebraicGeometry.Scheme.Modules.exact_cohomologyMap_cohomologyδ
        hS 0 1 rfl _).2 ⟨moduleUnitExtZeroCohomology k X S.X₂ z, by
          rw [Scheme.Modules.cohomologyMapBaseLinear_apply,
            TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor_map]
          rfl⟩
    · intro hx
      obtain ⟨z, hz⟩ := (TauCeti.AlgebraicGeometry.Scheme.Modules.exact_cohomologyMap_cohomologyδ hS 0 1 rfl (e x)).1 hx
      let z' := (moduleUnitExtZeroCohomology k X S.X₂).symm z
      have hx' : z'.comp (Ext.mk₀ S.g) (add_zero 0) = x := by
        apply e.injective
        rw [moduleUnitExtZeroCohomology_naturality, LinearEquiv.apply_symm_apply]
        rw [Scheme.Modules.cohomologyMapBaseLinear_apply,
          TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor_map]
        exact hz
      rw [← hx']
      change (z'.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
      rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  exact (dE.quotKerEquivOfSurjective hE).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (dH.quotKerEquivOfSurjective hH))


/-- Apply the comparison to the canonical injective embedding and its actual cokernel. -/
def moduleUnitExtOneCohomology (M : X.Modules) :
    Ext.{u} (𝟙_ X.Modules) M 1 ≃ₗ[k]
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M 1 :=
  moduleUnitExtOneCohomologyOfShortExact k X
    (TauCeti.injectiveCokernelSequence_shortExact M)

end ToricPower

end
