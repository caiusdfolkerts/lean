module

public import ToricPower.AffineTildeCochain
public import ToricPower.SingleAugmentationComponent

/-! # The original augmentation component after exact affine tilde -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ToricPower

universe u
variable (R : CommRingCat.{u}) {K : CochainComplex (ModuleCat.{u} R) ℕ}
  {M : ModuleCat.{u} R} {n : ℕ}

/-- The actual mapped chain augmentation has exactly its original
module component after affine sheafification. -/
theorem affineTildeSingleAugmentation_component
    (f : K ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) n).obj M) :
    singleAugmentationComponent
        ((affineTildeCochainFunctor R).map f ≫ (affineTildeSingleIso R M n).hom) =
      tilde.map (singleAugmentationComponent f) :=
  singleAugmentationComponent_map (tilde.functor R) f

end ToricPower

end
