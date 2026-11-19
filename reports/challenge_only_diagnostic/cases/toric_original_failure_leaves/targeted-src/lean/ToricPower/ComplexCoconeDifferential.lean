module

public import ToricPower.ComplexCoconeShortExact

/-! # The actual signed cone differential in module coordinates

This formula uses the original cone projections. It therefore fixes
both signs in the full differential without introducing an alternative
model of the cone.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex HomologicalComplex

namespace ToricPower.ComplexCone

variable {k : Type} [CommRing k]

theorem moduleHom_neg_apply {M N : ModuleCat.{0} k} (f : M ⟶ N) (x : M) :
    (-f) x = -(f x) := rfl

theorem mappingConeModuleTermEquiv_d
    {K L : CochainComplex (ModuleCat.{0} k) ℤ} (φ : K ⟶ L) (q : ℤ)
    (x : (mappingCone φ).X q) :
    mappingConeModuleTermEquiv φ (q+1) ((mappingCone φ).d q (q+1) x) =
      (-(K.d (q+1) (q+1+1) (mappingConeModuleTermEquiv φ q x).1),
        φ.f (q+1) (mappingConeModuleTermEquiv φ q x).1 +
          L.d q (q+1) (mappingConeModuleTermEquiv φ q x).2) := by
  apply Prod.ext
  · rw [mappingConeModuleTermEquiv_fst,mappingConeModuleTermEquiv_fst]
    have equation := ConcreteCategory.congr_hom
      (mappingCone.d_fst_v φ q (q+1) (q+1+1) rfl rfl) x
    simpa only [ModuleCat.comp_apply,moduleHom_neg_apply,map_neg] using equation
  · rw [mappingConeModuleTermEquiv_snd,mappingConeModuleTermEquiv_fst,
      mappingConeModuleTermEquiv_snd]
    exact ConcreteCategory.congr_hom (mappingCone.d_snd_v φ q (q+1) rfl) x

end ToricPower.ComplexCone

end
